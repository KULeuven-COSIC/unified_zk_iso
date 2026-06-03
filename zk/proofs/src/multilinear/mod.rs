use tracing::instrument;

use feanor_math::seq::VectorFn;
use feanor_math::ring::{El, RingBase, RingStore, RingExtension};
use feanor_math::field::{Field, FieldStore};
use feanor_math::homomorphism::Homomorphism;
use feanor_math::rings::multivariate::{
    MultivariatePolyRing,
    MultivariatePolyRingStore,
};

use crate::util::{bits_from_int, gen_vector, Coeff};

pub mod sumcheck;

pub mod spartan;

// indeterminates are ordered from encoding the lsb to encoding the msb
pub fn from_hypercube_coeffs<Poly>(polyring: &Poly, coeffs: &[Coeff<Poly>]) -> El<Poly>
    where Poly: MultivariatePolyRingStore<Type: MultivariatePolyRing>
{
    let vc = polyring.indeterminate_count();
    let ring = polyring.get_ring().base_ring();
    polyring.from_terms((0..(1 << vc)).zip(coeffs.iter()).map(|(i, coeff)|
        (ring.clone_el(coeff), polyring.create_monomial(bits_from_int(i, vc))
    )))
}

pub fn get_hypercube_coeffs<Poly>(polyring: &Poly, poly: &El<Poly>,
    dim_count: usize) -> Vec<Coeff<Poly>>
    where Poly: MultivariatePolyRingStore<Type: MultivariatePolyRing>
{
    let vc = polyring.indeterminate_count();
    let coeffring = polyring.get_ring().base_ring();
    (0..(1 << dim_count)).map(|i|
        coeffring.clone_el(
            polyring.coefficient_at(&poly, &polyring.create_monomial(bits_from_int(i, vc)))
        )
    ).collect()
}


pub struct MultilinearBasis<'a, R>
    where R: RingStore
{
    ring: &'a R,
    z: &'a [El<R>]
}

impl<'a, R: RingStore> MultilinearBasis<'a, R> {

    pub fn new(ring: &'a R, z: &'a [El<R>]) -> Self {
        Self { ring, z }
    }

    pub fn polynomial<Poly>(&self, polyring: &Poly) -> El<Poly>
        where Poly: MultivariatePolyRingStore<Type: MultivariatePolyRing<BaseRing = R>>
    {
        let zlen = self.z.len();
        let N = polyring.indeterminate_count();
        debug_assert!(zlen <= N);

        let mut res = polyring.one();
        (0..zlen).for_each(|i| {
            let tmp = polyring.add(
                polyring.create_term(
                    self.ring.sub_ref_snd(self.ring.one(), &self.z[i]),
                    polyring.create_monomial((0..N).map(|_| 0))
                ),
                polyring.create_term(
                    self.ring.sub(self.ring.get_ring().mul_int_ref(&self.z[i], 2), self.ring.one()),
                    polyring.create_monomial((0..N).map(|j| if j == i {1} else {0}))
                ),
            );
            polyring.mul_assign(&mut res, tmp);
        });
        res
    }

    // TODO: this could be faster
    pub fn evaluate(&self, at: &[El<R>]) -> El<R> {
        debug_assert!(self.z.len() == at.len());
        self.z.iter().zip(at).fold(self.ring.one(), |acc, (zi, ri)|
            self.ring.mul(acc, self.ring.add(
                self.ring.mul_ref(zi, ri),
                self.ring.mul(
                    self.ring.sub_ref_snd(self.ring.one(), zi),
                    self.ring.sub_ref_snd(self.ring.one(), ri)
            )))
        )
    }

    pub fn evaluate_athc(&self, at: Vec<usize>) -> El<R> {
        debug_assert!(self.z.len() == at.len());
        debug_assert!(at.iter().all(|x| *x == 0 || *x == 1));
        self.z.iter().zip(at).fold(self.ring.one(), |acc, (zi, ri)|
            self.ring.mul(acc, if ri == 0 {
                self.ring.sub_ref_snd(self.ring.one(), zi)
            } else { self.ring.clone_el(zi) })
        )
    }

    #[allow(dead_code)]
    pub fn evals_slow(&self) -> Vec<El<R>> {
        let vc = self.z.len();

        let mut res = gen_vector::<El<R>>(|| self.ring.one(), 1 << vc);
        let mut ws = gen_vector::<El<R>>(|| self.ring.one(), 1 << (vc - 1));

        for i in 0..vc {
            let fsthalf = &mut res[..(1 << i)];
            ws.iter_mut().zip(fsthalf.iter()).for_each(|(wsel, fel)| *wsel = self.ring.clone_el(fel));
            fsthalf.iter_mut().zip(ws.iter()).for_each(|(el, wsel)|
                *el = self.ring.mul_ref(wsel, &self.ring.sub_ref_snd(self.ring.one(), &self.z[i])));
            res[(1 << i)..].iter_mut().zip(ws.iter()).for_each(|(el, wsel)|
                *el = self.ring.mul_ref(wsel, &self.z[i]));
        }
        res
    }
}

pub struct MultilinearBasisEvals<'a, F>
    where F: FieldStore<Type: Field>
{
    mb: MultilinearBasis<'a, F>,
    ind: usize,
    pub cur: El<F>
}

impl<'a, F> MultilinearBasisEvals<'a, F>
    where F: FieldStore<Type: Field>
{
    pub fn new(field: &'a F, z: &'a [El<F>]) -> Self {
        MultilinearBasisEvals::from_basis(MultilinearBasis::new(field, z))
    }

    fn from_basis(mb: MultilinearBasis<'a, F>) -> Self {
        let cur = MultilinearBasisEvals::zero_eval(&mb);
        Self { mb, ind: 0, cur }
    }

    pub fn reset(&mut self) {
        self.ind = 0;
        self.cur = MultilinearBasisEvals::zero_eval(&self.mb);
    }

    fn zero_eval(mb: &MultilinearBasis<'a, F>) -> El<F> {
        mb.z.iter().fold(mb.ring.one(), |acc, r|
            mb.ring.mul(acc, mb.ring.sub_ref_snd(mb.ring.one(), r)))
    }
}

impl<'a, F> Clone for MultilinearBasisEvals<'a, F>
    where F: FieldStore<Type: Field>
{
    fn clone(&self) -> Self {
        Self {
            mb: MultilinearBasis {
                ring: self.mb.ring,
                z: self.mb.z
            },
            ind: self.ind,
            cur: self.mb.ring.clone_el(&self.cur)
        }
    }
}

// iterates over hypercube evals in lsb to msb order
impl<'a, F> Iterator for MultilinearBasisEvals<'a, F>
    where F: FieldStore<Type: Field>
{
    type Item = El<F>;

    fn next(&mut self) -> Option<Self::Item> {
        let field = self.mb.ring;
        if self.ind < ((1 << self.mb.z.len()) - 1) {
            let res = field.clone_el(&self.cur);

            self.ind += 1;
            // TODO: use bits instead of bits_from_int here
            // store bit repr of ind istead
            let j = bits_from_int(self.ind, self.mb.z.len()).position(|b| b == 1).unwrap();
            let mut scalar = field.div(&self.mb.z[j], &field.sub_ref_snd(field.one(), &self.mb.z[j]));
            if j > 0 {
                field.mul_assign(&mut scalar,
                    (0..j).fold(field.one(), |acc, i|
                        field.mul(acc, field.div(
                            &field.sub_ref_snd(field.one(), &self.mb.z[i]), &self.mb.z[i]))));
            }
            self.cur = field.mul_ref_fst(&self.cur, scalar);
            Some(res)
        } else if self.ind == ((1 << self.mb.z.len()) - 1) {
            self.ind += 1;
            Some(field.clone_el(&self.cur))
        } else {
            None
        }
    }
}

// TODO: remove redundancy in following functions
pub fn evaluate_at_fromevals<F>(field: &F, logsize: usize, at: &[El<F>], evals: &[El<F>])
    -> Vec<El<F>>
    where F: FieldStore<Type: Field>
{
    assert!(logsize > 0);
    assert!(1 << logsize == evals.len());
    // if evals.len() > 1 << at.len() then we evaluate the last at.len() variables
    assert!(at.len() <= logsize);
    assert!(at.len() > 0);

    let reslen = 1 << (logsize - at.len());
    let mut res = Vec::with_capacity(reslen);
    let mut eq = MultilinearBasisEvals::new(field, at);
    let first = eq.next().unwrap();

    let (firstchunk, rest) = evals.split_at(reslen);
    firstchunk.iter().for_each(|evalj| res.push(field.mul_ref(&evalj, &first)));
    rest.chunks_exact(reslen).zip(eq).for_each(|(evalchunk, eqi)|
        res.iter_mut().zip(evalchunk).for_each(|(rsj, chunkj)|
            field.add_assign(rsj, field.mul_ref(chunkj, &eqi))));
    res
}

#[instrument(skip_all)]
pub fn evaluate_at_fromevals_inplace<F>(field: &F, logsize: usize, at: &[El<F>], evals: &mut [El<F>])
    where F: FieldStore<Type: Field>
{
    assert!(logsize > 0);
    assert!(1 << logsize == evals.len());
    // if evals.len() > 1 << at.len() then we evaluate the last at.len() variables
    assert!(at.len() <= logsize);
    assert!(at.len() > 0);

    let reslen = 1 << (logsize - at.len());
    let mut eq = MultilinearBasisEvals::new(field, at);
    let first = eq.next().unwrap();
    let (ws, rest) = evals.split_at_mut(reslen);
    ws.iter_mut().for_each(|evali| *evali = field.mul_ref(evali, &first));
    rest.chunks_exact(reslen).zip(eq).for_each(|(evalchunk, eqi)|
        ws.iter_mut().zip(evalchunk).for_each(|(wsi, chunki)|
            *wsi = field.add_ref_fst(wsi, field.mul_ref(chunki, &eqi))));
}


// TODO: remove, not used anymore
pub fn evaluate_at_fromcoeff<R>(ring: &R, logsize: usize, at: &[El<R>], coeff: &[El<R>]) -> Vec<El<R>>
    where R: RingStore
{
    assert!(logsize > 0);
    assert!(1 << logsize == coeff.len());
    // if size != 1 << at.len() then we evaluate the last at.len() variables
    assert!(at.len() <= logsize);
    assert!(at.len() > 0);
    
    let reslen = 1 << (logsize - at.len());
    let mut res = gen_vector::<El<R>>(|| ring.zero(), reslen);
    coeff.iter().enumerate().for_each(|(i, c)| {
        let tmp = bits_from_int(i, logsize).enumerate().rev().take(at.len()).filter(|(_, b)| *b == 1).fold(
            ring.one(), |acc, (j, _)| ring.mul_ref_snd(acc, &at[j - (logsize - at.len())]));
        ring.add_assign(&mut res[i % reslen], ring.mul_ref_fst(c, tmp))
    });
    res
}


#[allow(dead_code)]
pub fn sum_over_hypercube_fromcoeff<R, I>(ring: &R, size: usize, coeff: I) -> El<R>
    where R: RingStore, I: Iterator<Item = El<R>>
{
    assert!(size.is_power_of_two());
    let vc = size.ilog2() as usize;
    coeff.enumerate().fold(ring.zero(), |acc, (i, c)|
        ring.add(acc, ring.get_ring().mul_int(c,
            (size >> bits_from_int(i, vc).filter(|b| *b == 1).count()) as i32)
        )
    )
}


// here, each term in the sum has a scalar
pub fn sum_over_hypercube_withscalars<'a, R, I, J>(ring: &'a R, scalars: I, coeff: J) -> El<R>
    where R: RingStore, I: Iterator<Item = &'a El<R>>, J: Iterator<Item = &'a El<R>>
{
    coeff.zip(scalars).fold(ring.zero(), |acc, (c, csc)| ring.add(acc, ring.mul_ref(c, csc)))
}


// helper for sum_over_hypercube_withscalars
pub fn evalscalars_to_coeffscalars<'a, R>(ring: &'a R, logsize: usize, scalars: &mut [El<R>])
    where R: RingStore
{
    debug_assert!(scalars.len() == 1 << logsize);
    (1..=logsize).for_each(|i| {
        let chunksize = 1 << i;
        let halfchunk = 1 << (i - 1);
        scalars.chunks_mut(chunksize).for_each(|chunk| {
            let (l, r) = chunk.split_at_mut(halfchunk);
            l.iter_mut().zip(r).for_each(|(li, ri)| ring.add_assign_ref(li, ri));
        });
    });
}


// TODO: make ref versions of these?
pub fn coeffs_to_evals_inplace<R: RingStore>(ring: &R, logsize: usize, coeffs: &mut [El<R>]) {
    debug_assert!(coeffs.len() == 1 << logsize);
    (1..=logsize).for_each(|i| {
        let chunksize = 1 << i;
        let halfchunk = 1 << (i - 1);
        coeffs.chunks_mut(chunksize).for_each(|chunk| {
            let (l, r) = chunk.split_at_mut(halfchunk);
            r.iter_mut().zip(l).for_each(|(ri, li)| ring.add_assign_ref(ri, li));
        });
    });
}

pub fn evals_to_coeffs_inplace<R: RingStore>(ring: &R, logsize: usize, evals: &mut [El<R>]) {
    (1..=logsize).for_each(|i| {
        let chunksize = 1 << i;
        let halfchunk = 1 << (i - 1);
        evals.chunks_mut(chunksize).for_each(|chunk| {
            let (l, r) = chunk.split_at_mut(halfchunk);
            r.iter_mut().zip(l).for_each(|(ri, li)| ring.sub_assign_ref(ri, li));
        });
    });
}


pub fn sum_over_hypercube<Poly>(polyring: &Poly, poly: &El<Poly>,
    dim_count: usize, suffix: &[Coeff<Poly>]) -> Coeff<Poly>
    where Poly: MultivariatePolyRingStore<Type: MultivariatePolyRing>
{
    let coeffring = polyring.get_ring().base_ring();
    let vc = polyring.indeterminate_count();
    assert!(dim_count + suffix.len() == vc);

    (0..(1 << dim_count)).map(|i| {
        let bs = bits_from_int(i, dim_count).map(|b| coeffring.int_hom().map(b as i32)).collect::<Vec<_>>();
        polyring.evaluate(&poly,
            (0..vc).map_fn(|i|
                if i < dim_count {
                    coeffring.clone_el(&bs[i])
                } else {
                    coeffring.clone_el(&suffix[i - dim_count])
                }
            ),
            coeffring.identity())
    }).fold(coeffring.zero(), |acc, x| coeffring.add(acc, x))
}




#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::rings::zn::zn_64::Zn;
    use feanor_math::rings::field::AsField;
    use feanor_math::assert_el_eq;
    use feanor_math::rings::finite::FiniteRingStore;
    use feanor_math::rings::multivariate::multivariate_impl::MultivariatePolyRingImpl;

    use crate::util::gen_vector;

    #[test]
    fn test_hypercube_coeffs() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        pub type Field = AsField<Zn>;

        let N = 5;
        let polyring = MultivariatePolyRingImpl::new(field.clone(), N);

        let randomcoeffs = gen_vector::<El<Field>>(||
            field.random_element(rand::random::<u64>), 1 << N);
        let poly = from_hypercube_coeffs(&polyring, &randomcoeffs);

        let mut coeffs = get_hypercube_coeffs(&polyring, &poly, N);

        assert!(randomcoeffs.iter().zip(coeffs.iter()).all(|(l, r)| field.eq_el(l, r)));

        coeffs_to_evals_inplace(&field, N, &mut coeffs);
        let evals = (0..(1 << N)).map(|j| polyring.evaluate(&poly,
            (0..N).map_fn(|n| field.int_hom().map(((j >> n) & 1) as i32)),
            field.identity())).collect::<Vec<_>>();

        assert!(evals.iter().zip(coeffs.iter()).all(|(l, r)| field.eq_el(l, r)));

        evals_to_coeffs_inplace(&field, N, &mut coeffs);

        assert!(randomcoeffs.iter().zip(coeffs.iter()).all(|(l, r)| field.eq_el(l, r)));
    }

    #[test]
    fn test_hypercube_folding() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        pub type Field = AsField<Zn>;

        let N = 7;
        let polyring = MultivariatePolyRingImpl::new(field.clone(), N);

        let randomcoeffs = gen_vector::<El<Field>>(||
            field.random_element(rand::random::<u64>), 1 << N);
        let poly = from_hypercube_coeffs(&polyring, &randomcoeffs);
        let evals = (0..(1 << N)).map(|j| polyring.evaluate(&poly,
            (0..N).map_fn(|n| field.int_hom().map(((j >> n) & 1) as i32)),
            field.identity())).collect::<Vec<_>>();
    
        let rs = gen_vector::<El<Field>>(|| field.random_element(rand::random::<u64>), N);

        let mut foldedpoly = polyring.clone_el(&poly);
        assert!((0..N).rev().all(|i| {
            let rconst = polyring.create_term(field.clone_el(&rs[i]),
                polyring.create_monomial((0..N).map(|_| 0)));
            foldedpoly = polyring.specialize(&foldedpoly, i, &rconst);
            let foldedpolycoeffs = get_hypercube_coeffs(&polyring, &foldedpoly, i);
            let foldedpolyevals = (0..(1 << i)).map(|j| polyring.evaluate(&foldedpoly,
                    (0..N).map_fn(|n| field.int_hom().map(((j >> n) & 1) as i32)),
                    field.identity())).collect::<Vec<_>>();

            let foldedcoeffs = evaluate_at_fromcoeff(&field, N, &rs[i..], &randomcoeffs);
            let mut foldedevals = evals.iter().map(|el| field.clone_el(el)).collect::<Vec<_>>();
            evaluate_at_fromevals_inplace(&field, N, &rs[i..], &mut foldedevals);

            let res1 = foldedevals.iter().zip(foldedpolyevals.iter()).all(|(l, r)|
                field.eq_el(&l, r));

            assert!(foldedcoeffs.len() == foldedpolycoeffs.len());
            let res2 = foldedcoeffs.iter().zip(foldedpolycoeffs.iter()).all(|(l, r)|
                field.eq_el(&l, r));
            res1 && res2
        }));
    }

    #[test]
    fn test_multilinear_basis() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        pub type Field = AsField<Zn>;

        let N = 5;
        let polyring = MultivariatePolyRingImpl::new(field.clone(), N);

        let randint = rand::random_range(0..(1 << N));
        let z: Vec<_> = bits_from_int(randint, N).map(|b|
            field.int_hom().map(b as i32)).collect();

        let mb = MultilinearBasis::new(&field, &z);
        let eq = mb.polynomial(&polyring);

        assert!((0..(1 << N)).all(|i| {
            let eval = polyring.evaluate(&eq,
                (0..N).map_fn(|n| field.int_hom().map(((i >> n) & 1) as i32)),
                field.identity());
            if i == randint {field.is_one(&eval)} else {field.is_zero(&eval)}
        }));

        assert!(polyring.appearing_indeterminates(&eq).into_iter().all(|(_, exp)| exp == 1));

        let randpoint = gen_vector::<El<Field>>(|| field.random_element(rand::random::<u64>), N);
        assert_el_eq!(field,
            polyring.evaluate(&eq, (0..randpoint.len()).map_fn(|i| randpoint[i]), field.identity()),
            mb.evaluate(&randpoint)
        );
    }

    #[test]
    fn test_multilinear_basis_evals() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        pub type Field = AsField<Zn>;

        let N = 5;
        let polyring = MultivariatePolyRingImpl::new(field.clone(), N);

        let z = gen_vector::<El<Field>>(|| field.random_element(rand::random::<u64>), N);

        let mb = MultilinearBasis::new(&field, &z);
        let eq = mb.polynomial(&polyring);
        let evals_slow = mb.evals_slow();
        let mbe = MultilinearBasisEvals::from_basis(mb);

        assert!((0..(1 << N)).zip(evals_slow.iter().zip(mbe)).all(|(i, (e, ef))| {
            let eval = polyring.evaluate(&eq,
                (0..N).map_fn(|n| field.int_hom().map(((i >> n) & 1) as i32)),
                field.identity());
            field.eq_el(&e, &eval) && field.eq_el(&ef, &eval)
        }));
    }
}


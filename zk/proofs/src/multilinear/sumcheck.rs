use itertools::Itertools;
use std::cell::{Ref, RefCell};
use tracing::instrument;

use feanor_math::ring::{El, RingBase, RingStore, RingExtension};
use feanor_math::rings::finite::FiniteRing;
use feanor_math::field::{Field, FieldStore};
use feanor_math::homomorphism::Homomorphism;
use feanor_math::rings::multivariate::{
    MultivariatePolyRingStore,
    multivariate_impl::MultivariatePolyRingImpl
};

use crate::multilinear::{
    sum_over_hypercube, evaluate_at_fromevals_inplace,
    MultilinearBasisEvals, evaluate_at_fromevals
};


// M is the number additional evaluation points besides (0, 1)
pub struct PolyEvals<F: RingStore<Type: Field>, const M: usize>
{
    eval01: [El<F>; 2],
    points: [i32; M],
    evals: [El<F>; M],
}

impl<'a, F: RingStore<Type: Field>, const M: usize> PolyEvals<F, M>
{
    pub fn new(eval01: [El<F>; 2], points: [i32; M], evals: [El<F>; M]) -> Self
    {
        Self { eval01, points, evals }
    }

    fn degone_at_negone(field: &F, atzero: &El<F>, atone: &El<F>) -> El<F> {
        field.sub_ref_snd(field.get_ring().mul_int_ref(atzero, 2), atone)
    }
    
    fn at_zero(&self) -> &El<F> {
        &self.eval01[0]
    }

    fn at_one(&self) -> &El<F> {
        &self.eval01[1]
    }

    pub fn at(&self, field: &F, int: i32) -> El<F> {
        match int {
            0 | 1 => field.clone_el(&self.eval01[int as usize]),
            _ => {
                if let Some(eval) = self.points.iter().enumerate().find_map(|(i, p)|
                    (*p == int).then_some(&self.evals[i]))
                { field.clone_el(eval) } else { self.interp(field, &field.int_hom().map(int)) }
            }
        }
    }

    #[instrument(skip_all)]
    pub fn degone_at(&self, field: &F, int: i32) -> El<F> {
        debug_assert!(M == 0);
        match int {
            -1 => PolyEvals::<F, M>::degone_at_negone(field, self.at_zero(), self.at_one()),
            2 => PolyEvals::<F, M>::degone_at_negone(field, self.at_one(), self.at_zero()),
            _ => self.at(field, int)
        }
    }

    pub fn get_points(&self) -> impl Iterator<Item = &i32> {
        [0, 1].iter().chain(self.points.iter())
    }

    pub fn get_evals(&self) -> impl Iterator<Item = &El<F>> {
        self.eval01.iter().chain(self.evals.iter())
    }

    pub fn get_lagrange_polys_at(field: &F, a: &El<F>, points: &[&i32])
        -> impl Iterator<Item = El<F>>
    {
        let inthom = field.int_hom();
        (0..(M+2)).map(move |i| {
            let (nom, invdenom) = points.iter().enumerate().fold(
                (field.one(), 1),
                |(nomacc, invdenomacc), (j, p)| if j != i {(
                    field.mul(nomacc, field.sub_ref_fst(a, inthom.map_ref(p))),
                    invdenomacc * (points[i] - *p)
                )} else { (nomacc, invdenomacc) }
            );
            field.div(&nom, &inthom.map(invdenom))
        })
    }

    pub fn interp(&self, field: &F, a: &El<F>) -> El<F> {
        let points = self.get_points().collect_vec();
        // TODO: this is collecting every iteration of sumcheck
        let lagr = PolyEvals::<F, M>::get_lagrange_polys_at(field, a, &points);
        self.get_evals().zip(lagr).fold(field.zero(), |acc, (e, l)|
            field.add(acc, field.mul_ref_fst(e, l))
        )
    }

    pub fn print(&self, field: &F) {
        self.get_evals().for_each(|eval| field.println(eval))
    }

    pub fn clone(&self, field: &F) -> Self {
        PolyEvals::new(
            core::array::from_fn(|i| field.clone_el(&self.eval01[i])),
            self.points.clone(),
            core::array::from_fn(|i| field.clone_el(&self.evals[i]))
        )
    }

    pub fn eq(&self, field: &F, other: &Self) -> bool {
        (0..M as i32).all(|x| field.eq_el(&self.at(field, x), &other.at(field, x)))
    }
}


// D: degree of the product sumcheck
pub trait SumcheckBase<const D: usize>
{
    type F: RingStore<Type: Field + FiniteRing>;

    fn field(&self) -> &Self::F;
    fn varcount(&self) -> usize;
    fn get_challenge(&self) -> El<Self::F>;
    fn get_other_eval_points(&self) -> [i32; D - 1];
    fn get_scalars<'b, 'c>(&'c self, challs: &'b [El<Self::F>])
        -> impl Iterator<Item = (El<Self::F>, El<Self::F>)> + 'b
        where 'c: 'b;
}


// type alias used below
type SCF<T, const D: usize, const N: usize>
    = <<T as Sumcheck<D,N>>::SCB as SumcheckBase<D>>::F;


// D: degree of the product sumcheck
// N: number of generic multilinear polynomials in the product sumcheck
pub trait Sumcheck<const D: usize, const N: usize>
    where [(); D - 1]: // trick that tells compiler that D - 1 is still valid usize?
{
    type SCB: SumcheckBase<D>;

    fn TE() -> bool;

    fn get_base(&self) -> &Self::SCB;

    fn get_reference(&self) -> [&[El<SCF<Self,D,N>>]; N];

    fn get_workspace(&self) -> [&RefCell<Vec<El<SCF<Self,D,N>>>>; N];

    fn compute_term(ring: &SCF<Self,D,N>, at: [&El<SCF<Self,D,N>>; N],
        scalar: &El<SCF<Self,D,N>>) -> El<SCF<Self,D,N>>;

    fn check_eval(&self, rX: Vec<El<SCF<Self,D,N>>>) -> bool;

    #[instrument(skip_all)]
    fn compute_round(&self, challs: &[El<SCF<Self,D,N>>],
        sum: Option<El<SCF<Self,D,N>>>) -> PolyEvals<SCF<Self,D,N>, {D - 1}>
    {
        let field = self.get_base().field();
        let i = challs.len();
        let vc = self.get_base().varcount();
        assert!(i < vc);
        let TE = Self::TE();

        if i > 0 && TE {
            let mut ws = self.get_workspace();
            debug_assert!(i == 1 || ws.iter().all(|v| v.borrow().len() == 1 << (vc - i + 1)));

            ws.iter_mut().enumerate().for_each(|(j, wszM)| {
                let mut wszMmut = wszM.borrow_mut();
                if i == 1 {
                    let refs = self.get_reference(); // only call this for i == 1
                    *wszMmut = evaluate_at_fromevals(field, vc, &challs[..1], &refs[j]);
                } else {
                    evaluate_at_fromevals_inplace(field, vc - i + 1, &challs[..1], &mut wszMmut);
                    wszMmut.truncate(1 << vc - i);
                }
            });
        }
        if i > 0 && TE {
            debug_assert!(self.get_workspace().iter().all(|v| v.borrow().len() == 1 << vc - i));
        }
        if i == 0 {
            debug_assert!(self.get_reference().iter().all(|v| v.len() == 1 << vc));
        }

        let mut hzero = field.zero();
        let mut hone = field.zero();
        let other_points = self.get_base().get_other_eval_points();
        let mut other_evals: [El<SCF<Self,D,N>>; D - 1] = core::array::from_fn(|_| field.zero());

        let ws = self.get_workspace(); 
        let wsrefref: [Ref<'_, _>; N] = core::array::from_fn(|i| ws[i].borrow());
        let wsref: [&[_]; N] = if !TE || i == 0 { self.get_reference() } else {
            core::array::from_fn::<&[_], N, _>(|i| &wsrefref[i])
        };
        
        let evalchalls = |wsind: usize, ind: usize| -> El<SCF<Self,D,N>> {
            let eq = MultilinearBasisEvals::new(field, challs);
            (0..(1 << i)).map(|j| &wsref[wsind][ind + j*(1 << (vc - i))]).zip(eq).fold(field.zero(),
                |acc, (wsel, eqel)| field.add(acc, field.mul_ref(wsel, &eqel)))
        };
        let mut tmpz: [_; N] = core::array::from_fn(|_| field.zero());
        let mut tmpo: [_; N] = core::array::from_fn(|_| field.zero());

        let half = 1 << (vc - i - 1);
        self.get_base().get_scalars(challs).enumerate().for_each(|(j, (sczi, scoi))| {
            if !TE {
                (0..N).for_each(|k| tmpz[k] = evalchalls(k, j)) ;
            }
            field.add_assign(&mut hzero, Self::compute_term(field,
                core::array::from_fn(|k| if TE { &wsref[k][j] } else { &tmpz[k] }), &sczi));

            if !TE { (0..N).for_each(|k| tmpo[k] = evalchalls(k, j+half)); }
            if sum.is_none() {
                field.add_assign(&mut hone, Self::compute_term(field,
                    core::array::from_fn(|k| if TE { &wsref[k][j+half] } else { &tmpo[k] }), &scoi));
            }

            let sci = PolyEvals::new([sczi, scoi], [], []);
            // NOTE: initializing the PolyEvals objects here is slower since blocks inlining?
            other_evals.iter_mut().zip(other_points.iter()).for_each(|(eval, point)| {
                let wspi: [_; N] = core::array::from_fn(|k| PolyEvals::new(
                        if TE { core::array::from_fn(|l| field.clone_el(&wsref[k][j+l*half])) }
                        else { [ field.clone_el(&tmpz[k]), field.clone_el(&tmpo[k]) ] },
                    [], []).degone_at(field, *point)
                );
                debug_assert!(wspi.len() == N);
                field.add_assign(eval, Self::compute_term(field,
                    core::array::from_fn(|k| &wspi[k]), &sci.at(field, *point)
                ))
            });
        });

        hone = if let Some(sum) = sum { field.sub_ref_snd(sum, &hzero) } else { hone };
        PolyEvals::new([hzero, hone], other_points, other_evals)
    }

    fn execute(&self, sum: El<SCF<Self,D,N>>) -> Option<Vec<El<SCF<Self,D,N>>>>
    {
        let field = self.get_base().field();
        let mut challvec = Vec::new();

        let mut tmpsum = sum;
        ((0..self.get_base().varcount()).all(|_| {
            // println!("================== Round {i}");
            // let hdi = self.compute_round(&challvec, None);
            let hdi = self.compute_round(&challvec, Some(field.clone_el(&tmpsum)));
            // {
            //     let ws = self.get_workspace();
            //     ws.iter().enumerate().for_each(|(i, v)| {
            //         println!("Printing ws {i}");
            //         v.borrow().iter().for_each(|el| field.println(&el));
            //         println!("");
            //     });
            // }
            // println!("round {i}: hdi:");
            // hdi.print(field);
            // println!("round {i}: at0: {}, at1: {}", field.format(&hdi.at(field, 0)), field.format(&hdi.at(field, 1)));
            let res = field.eq_el(&tmpsum, &field.add(hdi.at(field, 0), hdi.at(field, 1)));
            let chall = self.get_base().get_challenge();
            tmpsum = hdi.interp(field, &chall);
            challvec.insert(0, chall);
            res
        }) && {
            let (mut sc, _): (Vec<_>, Vec<_>) = self.get_base().get_scalars(&challvec).unzip();
            let ws = self.get_workspace();
            ws.into_iter().for_each(|wsi| {
                let mut wsimut = wsi.borrow_mut();
                evaluate_at_fromevals_inplace(field, 1, &challvec[..1], &mut wsimut);
                wsimut.truncate(1);
            });
            let wsref: [Ref<'_, _>; N] = core::array::from_fn(|i| ws[i].borrow());
            field.eq_el(&tmpsum, &Self::compute_term(field,
                core::array::from_fn(|i| &wsref[i][0]), &sc.pop().unwrap()))
        }).then(|| challvec)
    }
}


pub fn sumcheck_sum<F, const M: usize>(mpolyring: &MultivariatePolyRingImpl<F>,
    poly: &El<MultivariatePolyRingImpl<F>>, freevarind: usize, otherevalpoints: [i32; M])
    -> PolyEvals<F,M>
    where F: FieldStore<Type: Field>
{
    assert!(mpolyring.appearing_indeterminates(poly).into_iter().all(|(varind, _)| varind <= freevarind));
    let maxdeg =  mpolyring.appearing_indeterminates(poly).into_iter().map(|(_, exp)| exp).max().unwrap();
    assert!(maxdeg == M + 1);
    assert!(maxdeg <= 2);
    let field = mpolyring.get_ring().base_ring();
    let sufflen = mpolyring.indeterminate_count() - freevarind;

    let makesuffix = |at: El<F>| {
        let mut suffix = vec![at];
        suffix.extend((0..(sufflen-1)).map(|_| field.zero()));
        suffix
    };

    let c0 = sum_over_hypercube(mpolyring, poly, freevarind, &makesuffix(field.zero()));
    let c1 = sum_over_hypercube(mpolyring, poly, freevarind, &makesuffix(field.one()));

    PolyEvals::new([c0, c1], otherevalpoints, core::array::from_fn(|i|
        sum_over_hypercube(mpolyring, poly, freevarind,
            &makesuffix(field.int_hom().map_ref(&otherevalpoints[i])))
    ))
}


#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::seq::VectorFn;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::rings::zn::zn_64::Zn;
    use feanor_math::rings::field::AsField;
    use feanor_math::assert_el_eq;
    use feanor_math::rings::finite::FiniteRingStore;

    use crate::util::gen_vector;
    use crate::multilinear::{
        MultilinearBasis,
        sum_over_hypercube,
        from_hypercube_coeffs,
        sum_over_hypercube_fromcoeff,
        sum_over_hypercube_withscalars,
        evalscalars_to_coeffscalars
    };

    #[test]
    fn test_sumoverhypercube() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        pub type Field = AsField<Zn>;

        let N = 5;
        let polyring = MultivariatePolyRingImpl::new(field.clone(), N);

        let zinner = gen_vector::<El<Field>>(|| field.random_element(rand::random::<u64>), N);
        let z = (0..N).map_fn(|i| field.clone_el(&zinner[i]));
        let zvec: Vec<_> = z.clone().into_iter().collect();

        let randomcoeffs = gen_vector::<El<Field>>(||
            field.random_element(rand::random::<u64>), 1 << N);
        let poly = from_hypercube_coeffs(&polyring, &randomcoeffs);

        let poly0 = polyring.specialize(&poly, N - 1, &polyring.create_term(field.zero(), polyring.create_monomial((0..N).map(|_| 0))));
        assert_el_eq!(field,
            sum_over_hypercube(&polyring, &poly0, N, &[]),
            sum_over_hypercube_fromcoeff(&field, 1 << N, randomcoeffs.iter().take(1 << (N - 1)).map(|c| field.clone_el(&c))));

        let poly1 = polyring.specialize(&poly, N - 1, &polyring.create_term(field.one(), polyring.create_monomial((0..N).map(|_| 0))));

        let poly10 = polyring.sub(poly1, poly0);
        assert_el_eq!(field,
            sum_over_hypercube(&polyring, &poly10, N, &[]),
            sum_over_hypercube_fromcoeff(&field, 1 << N, randomcoeffs.iter().skip(1 << (N - 1)).map(|c| field.clone_el(&c)))
            );

        assert_el_eq!(field,
            sum_over_hypercube(&polyring, &poly, N, &[]),
            sum_over_hypercube_fromcoeff(&field, 1 << N, randomcoeffs.iter().map(|c| field.clone_el(&c)))
        );

        let polyscalar = polyring.mul_ref_fst(&poly, polyring.one());
        let mut scalars = (0..(1 << N)).map(|_| field.one()).collect::<Vec<_>>();
        evalscalars_to_coeffscalars(&field, N, &mut scalars);
        assert_el_eq!(field,
            sum_over_hypercube(&polyring, &polyscalar, N, &[]),
            sum_over_hypercube_withscalars(&field, scalars.iter(), randomcoeffs.iter())
        );

        let eq = MultilinearBasis::new(&field, &zvec).polynomial(&polyring);
        let y = polyring.evaluate(&poly, &z, field.identity());
        let scpoly = polyring.mul_ref_fst(&poly, eq);

        assert_el_eq!(field, sum_over_hypercube(&polyring, &scpoly, N, &[]), y);
    }

    #[test]
    fn test_sumchecksum() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        pub type Field = AsField<Zn>;

        let N = 5;
        let polyring = MultivariatePolyRingImpl::new(field.clone(), N);

        let randomcoeffs = gen_vector::<El<Field>>(||
            field.random_element(rand::random::<u64>), 1 << N);
        let mut poly = from_hypercube_coeffs(&polyring, &randomcoeffs);
        
        // to make poly have variables of deg 2
        let zinner = gen_vector::<El<Field>>(|| field.random_element(rand::random::<u64>), N);
        let z = (0..N).map_fn(|i| field.clone_el(&zinner[i]));
        let zvec: Vec<_> = z.clone().into_iter().collect();
        let eq = MultilinearBasis::new(&field, &zvec).polynomial(&polyring);
        poly = polyring.mul_ref_fst(&poly, eq);
        
        let sum = sum_over_hypercube(&polyring, &poly, N, &[]);

        let mut hd = sumcheck_sum(&polyring, &poly, N - 1, [2]);

        assert_el_eq!(field, &field.add(hd.at(&field, 0), hd.at(&field, 1)), &sum);

        for ind in 1..=N-1 {
            //println!("tested: {}", ind - 1);
            let r = field.random_element(rand::random::<u64>);
            poly = polyring.specialize(&poly, N - ind,
                &polyring.create_term(field.clone_el(&r), polyring.create_monomial((0..N).map(|_| 0))));
            let sum = hd.interp(&field, &r);
            hd = sumcheck_sum(&polyring, &poly, N - ind - 1, [2]);
            assert_el_eq!(field, &field.add(hd.at(&field, 0), hd.at(&field, 1)), &sum);
        }
    }
}

use tracing::instrument;

use feanor_math::algorithms::linsolve::LinSolveRing;
use feanor_math::ring::{RingStore, El};
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};

use crate::util::{gen_vector, matmul::MatrixMul};
use crate::codes::{LinearCode, RScode};

// Default
pub type DFC<'a, F> = RSFoldableCode<'a, F>;

pub trait FoldableCode {

    type R: RingStore;
    type C: LinearCode<R = Self::R>;

    fn ring(&self) -> &Self::R;
    fn d(&self) -> usize;
    fn k0(&self) -> usize;
    fn c(&self) -> usize;
    fn k(&self, d: usize) -> usize {self.k0()*(1 << d)}
    fn n(&self, d: usize) -> usize {self.c()*self.k(d)}
    fn t(&self, d: usize) -> impl Iterator<Item = &El<Self::R>>;
    fn G0code(&self) -> &Self::C;

    fn check_invariants(&self) {
        assert!((0..self.d()).all(|dind| self.t(dind).count() == self.n(dind)));
        assert!(self.n(0) == self.G0code().generator().rows());
        assert!(self.k(0) == self.G0code().generator().columns());
    }

    fn encode(&self, input: &[El<Self::R>]) -> Vec<El<Self::R>>
    {
        self.check_invariants();
        assert!(input.len() % self.k0() == 0);
        assert!((input.len() / self.k0()).is_power_of_two());

        let d = (input.len() / self.k0()).ilog2() as usize;
        let output_len = self.c()*input.len();

        // TODO: can be better using feanor-math VectorViews?
        let mut res = gen_vector::<El<Self::R>>(|| self.ring().zero(), output_len);
        
        // encode into res using the G0 matrix
        res.chunks_exact_mut(self.n(0)).zip(input.chunks_exact(self.k0())).for_each(
            |(out, inp)| out.iter_mut().zip(self.G0code().encode(inp)).for_each(|(o, i)| *o = i));

        if d == 0 {
            return res;
        }

        let mut ws = gen_vector::<El<Self::R>>(|| self.ring().zero(), output_len / 2);
       
        for dind in 0..d {

            let chunksize = self.n(dind);

            // compute rt and store in the workspace
            ws.chunks_exact_mut(chunksize)
                .zip(res.chunks_exact(chunksize).skip(1).step_by(2)).for_each(|(ws, r)|
                    ws.iter_mut().zip(r.iter().zip(self.t(dind))).for_each(
                    |(wsi, (ri, ti))| *wsi = self.ring().mul_ref(ri, ti)));

            // add rt to all left parts and subtract it from all right parts
            res.chunks_exact_mut(chunksize*2).zip(ws.chunks_exact(chunksize)).for_each(|(lr, rt)| {
                let (l, r) = lr.split_at_mut(chunksize);
                rt.iter().zip(l.iter_mut().zip(r.iter_mut())).for_each(|(rti, (li, ri))| {
                    *ri = self.ring().sub_ref(li, rti);
                    self.ring().add_assign_ref(li, rti);
                });
            });
        }
        res
    }

}

pub struct RSFoldableCode<'a, R: RingStore<Type: LinSolveRing>> {
    G0code: RScode<'a, R>,
    d: Option<usize>,
    t: Vec<Vec<El<R>>>
}

impl<'a, R> RSFoldableCode<'a, R> 
    where R: RingStore<Type: LinSolveRing + FiniteRing>
{
    #[instrument(skip_all)]
    pub fn new(ring: &'a R, k0: usize, c: usize, d: Option<usize>) -> Self {

        let G0code = RScode::new(ring, k0, k0*c);

        let t = if let Some(d) = d {
            Self::construct_t(d, &G0code)
        } else { Vec::new() };

        Self {
            G0code,
            d,
            t
        }
    }

    pub fn construct_t(d: usize, G0code: &RScode<'a, R>) -> Vec<Vec<El<R>>> {
        let mut t: Vec<Vec<El<R>>> = Vec::with_capacity(d);
        (0..d).for_each(|dind| t.push(gen_vector::<El<R>>(|| {
                let mut el = G0code.ring().random_element(rand::random::<u64>);
                while G0code.ring().is_zero(&el) {
                    el = G0code.ring().random_element(rand::random::<u64>);
                }
                el
            }, G0code.generator().rows()*(1 << dind))
        ));
        t
    }
}

impl<'a, R> RSFoldableCode<'a, R> 
    where R: RingStore<Type: LinSolveRing>
{
    pub fn from(ring: &'a R, k0: usize, c: usize, t: Vec<Vec<El<R>>>) -> Self {

        let G0code = RScode::new(ring, k0, k0*c);

        let d = t.len();
        assert!((0..d).all(|dind| t[dind].len() == c*k0*(1 << dind)));

        Self {
            G0code,
            d: Some(d),
            t
        }
    }
}

impl<'a, Rg: RingStore<Type: LinSolveRing>> FoldableCode for RSFoldableCode<'a, Rg> {

    type R = Rg;
    type C = RScode<'a, Rg>;

    fn ring(&self) -> &Rg {
        self.G0code().ring()
    }

    fn d(&self) -> usize {
        self.d.unwrap()
    }

    fn k0(&self) -> usize {
        self.G0code.generator().columns()
    }

    fn c(&self) -> usize {
        self.G0code.generator().rows() / self.k0()
    }

    fn t(&self, d: usize) -> impl Iterator<Item = &El<Self::R>> {
        self.t[d].iter()
    }

    fn G0code(&self) -> &RScode<'a, Rg> {
        &self.G0code
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::ring::RingBase;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::rings::zn::zn_64::Zn;
    use feanor_math::field::FieldStore;

    use crate::util::gen_random;

    #[test]
    fn test_myfoldablecode_basics() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        let mut rng = rand::rng();

        let k0 = 5;
        let c = 2;
        let d = 1; 
        let mfc = RSFoldableCode::new(&field, k0, c, Some(d));

        let mut input = gen_random(&field, &mut rng, mfc.k(0));
        let input1 = gen_random(&field, &mut rng, mfc.k(0));

        input.extend(input1);

        let t = mfc.t(0).collect::<Vec<_>>();
        let Gl = mfc.G0code().encode(&input[..mfc.k(0)]);
        let Gr = mfc.G0code().encode(&input[mfc.k(0)..]);

        let code = mfc.encode(&input);

        assert!((0..mfc.n(0)).all(|i| {
            let Grt = field.mul_ref(t[i], &Gr[i]);
            field.eq_el(&code[i], &field.add_ref(&Gl[i], &Grt)) && 
            field.eq_el(&code[i + mfc.n(0)], &field.sub_ref_fst(&Gl[i], Grt))
        }));
    }

    #[test]
    fn test_myfoldablecode_linearity() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        let mut rng = rand::rng();

        let k0 = 5;
        let c = 2;
        let d = 2; 
        let mfc = RSFoldableCode::new(&field, k0, c, Some(d));
        let t = mfc.t(d-1).collect::<Vec<_>>();

        let mut inp1 = gen_random(&field, &mut rng, mfc.k(d-1));
        let code1 = mfc.encode(&inp1);

        let inp2 = gen_random(&field, &mut rng, mfc.k(d-1));
        let code2 = mfc.encode(&inp2);

        inp1.extend(inp2);
        let code = mfc.encode(&inp1);

        assert!((0..mfc.n(d-1)).all(|i| {
            let tmp = field.mul_ref(&code2[i], t[i]);
            field.eq_el(&code[i], &field.add_ref(&code1[i], &tmp)) &&
            field.eq_el(&code[i + mfc.n(d-1)], &field.sub_ref_fst(&code1[i], tmp))
        }));
    }

    #[test]
    fn test_myfoldablecode_foldability() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        let mut rng = rand::rng();

        let k0 = 5;
        let c = 2;
        let d = 2; 
        let mfc = RSFoldableCode::new(&field, k0, c, Some(d));

        let inp = gen_random(&field, &mut rng, mfc.k(d));

        let code = mfc.encode(&inp);

        let chall = field.random_element(rand::random::<u64>);

        let d = mfc.d();

        let foldedinp = (0..mfc.k(d-1)).map(|i| {
            field.add_ref_fst(
                &inp[i],
                field.mul_ref(&inp[i + mfc.k(d-1)], &chall)
            )
        }).collect::<Vec<_>>();

        let foldedcode = mfc.t(d-1).enumerate().map(|(i, ti)| {
            let mut tmpleft = field.add_ref(&chall, ti);
            let mut tmpright = field.sub_ref(ti, &chall);
            field.mul_assign_ref(&mut tmpleft, &code[i]);
            field.mul_assign_ref(&mut tmpright, &code[i + mfc.n(d-1)]);
            field.div(
                &field.add(tmpleft, tmpright),
                &field.get_ring().mul_int_ref(ti, 2)
            )
        }).collect::<Vec<_>>();

        let foldedcode2 = mfc.encode(&foldedinp);

        assert!((0..mfc.n(d-1)).all(|i| field.eq_el(&foldedcode[i], &foldedcode2[i])));
    }

}


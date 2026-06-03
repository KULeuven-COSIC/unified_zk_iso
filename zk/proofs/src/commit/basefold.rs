use std::alloc::Global;
use std::cell::RefCell;
use std::marker::PhantomData;
use itertools::{izip, Itertools};

use tracing::instrument;
use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::{BigIntRing, IntegerRingStore};
use feanor_math::ring::{RingStore, RingBase, El};
use feanor_math::field::{Field, FieldStore};
use feanor_math::rings::finite::FiniteRing;
use feanor_math::rings::multivariate::{
    MultivariatePolyRingStore,
    multivariate_impl::MultivariatePolyRingImpl
};

use crate::FSRng;
use crate::util::{Coeff, FiatShamirSim};
use crate::codes::{
    LinearCode,
    foldablecodes::{FoldableCode, RSFoldableCode}
};
use crate::multilinear::{
    MultilinearBasis, MultilinearBasisEvals,
    get_hypercube_coeffs, evals_to_coeffs_inplace, evaluate_at_fromevals,
    sum_over_hypercube_withscalars, evalscalars_to_coeffscalars,
    sumcheck::{
        SumcheckBase, Sumcheck,
        sumcheck_sum, PolyEvals
    }
};
use crate::commit::{MultilinearPCS, Proof, Commitment};


pub struct BaseFoldCommitment<R: RingStore>{
    pub code_el: Vec<El<R>>
}
impl<R: RingStore> Commitment for BaseFoldCommitment<R>{}

pub struct BaseFoldProof<R: RingStore<Type: Field>> {
    pub code_els: Vec<Vec<El<R>>>,
    pub sumcheck_els: Vec<PolyEvals<R, 1>>,
    pub sumcheck_last: Vec<El<R>>
}

impl<R: RingStore<Type: Field>> BaseFoldProof<R> {
    pub fn clone(&self, ring: &R) -> Self {
        Self {
            code_els: self.code_els.iter().map(|v|
                v.iter().map(|el| ring.clone_el(el)).collect()).collect(),
            sumcheck_els: self.sumcheck_els.iter().map(|poly| poly.clone(ring)).collect(),
            sumcheck_last: self.sumcheck_last.iter().map(|el| ring.clone_el(el)).collect()
        }
    }
}

impl<R: RingStore<Type: Field>> Proof for BaseFoldProof<R>{}


// type alias
pub type BSCF<T> = <<T as Sumcheck<2, 1>>::SCB as SumcheckBase<2>>::F;

pub struct BaseFoldPCS<'a, C, SC>
    where SC: BaseFoldSumcheck<'a>, C: FoldableCode<R = BSCF<SC>>
{
    fs: RefCell<FiatShamirSim<FSRng>>,
    polyring: MultivariatePolyRingImpl<BSCF<SC>>,
    code: C,
    ver_rep: Option<usize>,
    phantom: PhantomData<&'a ()>
}

impl<'a, C, SC> BaseFoldPCS<'a, C, SC>
    where SC: BaseFoldSumcheck<'a>, C: FoldableCode<R = BSCF<SC>>
{
    pub fn field(&self) -> &BSCF<SC> {
        self.code.ring()
    }

    pub fn code(&self) -> &C {
        &self.code
    }

    pub fn proofsize(&self) -> usize {
        let d = self.code.d();
        let proofsize = d*2*self.ver_rep.unwrap() + 3*d +
            if self.code.k(0) == 0 { 0 } else { self.code.k(0).ilog2() as usize };
        let ZZbig: BigIntRing = BigIntRing::RING;
        let bits = ZZbig.abs_log2_ceil(&self.field().characteristic(ZZbig).unwrap()).unwrap();
        let authpath = self.code.n(d).ilog2() as usize * 256; // worst-case no pruning
        return proofsize*(bits + authpath)
    }
}

impl<'a, C, SC> BaseFoldPCS<'a, C, SC>
    where SC: BaseFoldSumcheck<'a>, C: FoldableCode<R = BSCF<SC>>,
          <BSCF<SC> as RingStore>::Type: FiniteRing
{
    pub fn reset_fs(&self) {
        self.fs.borrow_mut().reset()
    }
}


impl<'a, F, SC> BaseFoldPCS<'a, RSFoldableCode<'a, F>, SC>
    where F: RingStore<Type: Field + FiniteRing> + Clone, SC: BaseFoldSumcheck<'a>,
          <SC as Sumcheck<2,1>>::SCB: SumcheckBase<2, F = F>
{
    #[instrument(skip_all)]
    pub fn new(field: &'a F, varcount: usize, k0: usize, c: usize, ver_rep: Option<usize>) -> Self
    {
        assert!(k0.is_power_of_two());

        let d = if ver_rep.is_some() {
            Some(varcount - (k0.ilog2() as usize))
        } else { None };
        let code = RSFoldableCode::new(field, k0, c, d);
        
        // NOTE: fake polyring to efficiently test large instances
        let polyring = MultivariatePolyRingImpl::new_with(field.clone(),
            varcount, 0, (0, 0), Global);
        // let polyring = MultivariatePolyRingImpl::new_with(field.clone(),
        //     varcount, 2*varcount as u16, (0, 0), Global);

        let fs = RefCell::new(FiatShamirSim::<FSRng>::new());
        
        Self {
            fs,
            polyring, 
            code,
            ver_rep,
            phantom: PhantomData::default()
        }
    }

}

impl<'a, 'b, C, SC> MultilinearPCS<'b> for BaseFoldPCS<'a, C, SC>
    where SC: BaseFoldSumcheck<'a>, C: FoldableCode<R = BSCF<SC>>,
          BSCF<SC>: Clone, <BSCF<SC> as RingStore>::Type: FiniteRing, 'b: 'a
{
    type Poly = MultivariatePolyRingImpl<BSCF<SC>>;
    type C = BaseFoldCommitment<BSCF<SC>>;
    type P = BaseFoldProof<BSCF<SC>>;

    fn polyring(&self) -> &Self::Poly {
        &self.polyring
    }

    fn get_challenge(&self) -> Coeff<Self::Poly> {
        self.fs.borrow_mut().challenge(self.coeffring())
    }

    fn commit(&self, poly: &[Coeff<Self::Poly>]) -> Self::C
    {
        BaseFoldCommitment{code_el: self.code.encode(poly) }
    }
    
    fn open(&self, _com: &Self::C, _poly: &[Coeff<Self::Poly>]) -> bool {
        // TODO
        true
    }

    fn eval_slow(&self, com: &Self::C, z: &[Coeff<Self::Poly>],
        _y: Coeff<Self::Poly>, poly: &El<Self::Poly>) -> Self::P
    {
        let d = self.code.d();
        let vc = self.polyring().indeterminate_count();
        assert!(z.len() == vc);
        let f = self.field();
        let otherpoints = [2];

        let fsclone = self.fs.borrow().clone();

        let mut polys: Vec<PolyEvals<BSCF<SC>,1>> = Vec::with_capacity(d);
        let eq = MultilinearBasis::new(f, &z).polynomial(&self.polyring);
        let mut wpoly = self.polyring.clone_el(poly);
        let mut scpoly = self.polyring.mul_ref_fst(poly, eq);
        //assert_el_eq!(self.coeffring(), sum_over_hypercube(&self.polyring, &scpoly, vc, &[]), y);
        let mut hunivar = sumcheck_sum(&self.polyring, &scpoly, vc - 1, otherpoints);
        /*assert_el_eq!(self.coeffring(), &self.coeffring().add(
            unipolyring.evaluate(&hunivar, &self.coeffring().zero(), self.coeffring().identity()),
            unipolyring.evaluate(&hunivar, &self.coeffring().one(), self.coeffring().identity())
        ), &y);*/
        polys.push(hunivar);

        let mut proofcodes: Vec<Vec<El<BSCF<SC>>>> = Vec::with_capacity(d);
        let mut topcode = &com.code_el;

        let mut last: Vec<El<BSCF<SC>>> = Vec::with_capacity(
            if self.code.k(0) == 1 {0} else {self.code.k(0)});
        
        for dind in (0..d).rev() {
            let chall = self.get_challenge();
            let curfreevc = vc - (d - dind);
            let challconst = self.polyring.create_term(self.coeffring().clone_el(&chall),
                self.polyring.create_monomial((0..vc).map(|_| 0)));
            wpoly = self.polyring().specialize(&wpoly, curfreevc, &challconst);

            proofcodes.push(
                self.code.t(dind).enumerate().map(|(i, ti)| {
                    interpdeg1(f, ti, &topcode[i], &topcode[i + self.code.n(dind)], &chall)
                }).collect()
            );
            topcode = &proofcodes[d - 1 - dind];
            /*let wpolycode = self.code.encode(&get_hypercube_coeffs(&self.polyring,
                    &wpoly, curfreevc).iter().collect_vec());
            assert!((0..self.code.n(dind)).all(|i|
                self.coeffring().eq_el(&proofcodes[d-1-dind][i], &wpolycode[i])));*/

            if dind != 0 {
                scpoly = self.polyring().specialize(&scpoly, curfreevc, &challconst);
                //let tmpsum = unipolyring.evaluate(&polys[d - 1 - dind], &chall, self.coeffring().identity());
                hunivar = sumcheck_sum(&self.polyring, &scpoly, curfreevc - 1, otherpoints);
                /*assert_el_eq!(self.coeffring(), &self.coeffring().add(
                    unipolyring.evaluate(&hunivar, &self.coeffring().zero(), self.coeffring().identity()),
                    unipolyring.evaluate(&hunivar, &self.coeffring().one(), self.coeffring().identity())
                ), &tmpsum);*/
                polys.push(hunivar);
            }
        }
    
        assert!(self.code.k(0).ilog2() as usize == vc - d);
        if self.code.k(0) > 1 {
            last = get_hypercube_coeffs(&self.polyring, &wpoly, self.code.k(0).ilog2() as usize);
        }

        // reset the FS to the state before eval so that verify can use it
        self.fs.replace(fsclone);

        BaseFoldProof {
            code_els: proofcodes,
            sumcheck_els: polys,
            sumcheck_last: last
        }
    }

    #[instrument(skip_all)]
    fn verify(&self, com: &Self::C, z: &[Coeff<Self::Poly>],
        y: Coeff<Self::Poly>, poly: &[Coeff<Self::Poly>], proof: Self::P) -> bool
    {
        let d = self.code.d();

        if proof.code_els.len() != d || proof.sumcheck_els.len() != d ||
            (proof.sumcheck_last.len() > 0) == (self.code.k(0) == 1) {
            return false;
        }

        let mut challvec: Vec<Coeff<Self::Poly>> = Vec::with_capacity(d);

        let mut tmp = y;

        let mut topcode = &com.code_el;
        let mut mu = (0..self.ver_rep.unwrap()).map(|_|
            rand::random_range(0..self.code.n(d-1))).collect_vec();

        self.open(com, &poly) &&
        proof.code_els.iter().zip(proof.sumcheck_els.iter()).enumerate().all(|(i, (code, poly))| {
            let chall = self.get_challenge();

            let dind = d - 1 - i;
            let t = self.code.t(dind).collect_vec();
            let mut rescode = (0..self.ver_rep.unwrap()).all(|j| {
                let interp = interpdeg1(self.coeffring(), t[mu[j]],
                    &topcode[mu[j]], &topcode[mu[j] + self.code.n(dind)], &chall);
                self.coeffring().eq_el(&interp, &code[mu[j]])
            });
            if dind > 0 {
                mu.iter_mut().for_each(|mu_el| if *mu_el >= self.code.n(dind - 1) {
                    *mu_el -= self.code.n(dind - 1);
                });
                topcode = &code;
            } else {
                rescode &= self.code.G0code().is_code_element(&code);
            }

            let respoly = self.coeffring().eq_el(&tmp,
                &self.coeffring().add(poly.at(self.coeffring(), 0), poly.at(self.coeffring(), 1)));
            tmp = poly.interp(self.coeffring(), &chall);

            challvec.push(chall);
            rescode && respoly
        }) && ({
            // challenges are sampled in order r_{d-1} -> r_0
            let challvec = challvec.into_iter().rev().collect_vec();

            if self.code.k(0) == 1 {
                let eqeval = MultilinearBasis::new(self.coeffring(), &z).evaluate(&challvec);
                // TODO: avoid div by zero
                let tmpenc = self.code.encode(&[self.coeffring().div(&tmp, &eqeval)]);
                (0..self.code.c()).all(|i| self.coeffring().eq_el(
                    &tmpenc[i],
                    &proof.code_els[d - 1][i]
                ))
            } else {
                let encm = self.code.encode(&proof.sumcheck_last);
                let kappa = self.code.k(0).ilog2() as usize;
                let mut eqevals = MultilinearBasisEvals::new(self.coeffring(),
                    &z[..kappa]).collect_vec();
                evalscalars_to_coeffscalars(self.coeffring(), kappa, &mut eqevals);
                let eval = sum_over_hypercube_withscalars(self.coeffring(),
                    eqevals.iter(), proof.sumcheck_last.iter());

                (0..self.code.n(0)).all(|i| {
                    self.coeffring().eq_el(&encm[i], &proof.code_els[d - 1][i])
                })
                &&
                self.coeffring().eq_el(&tmp, &self.coeffring().mul(eval,
                    MultilinearBasis::new(self.coeffring(), &z[kappa..]).evaluate(&challvec)))
            }
        })
    }

    // NOTE: if no polyeval is provided, this function will compute polyeval from polycoeff
    #[instrument(skip_all)]
    fn eval(&'b self, com: &Self::C, z: Vec<Coeff<Self::Poly>>,
        y: Coeff<Self::Poly>, polycoeff: Option<&'b [Coeff<Self::Poly>]>,
        polyeval: Option<&'b [Coeff<Self::Poly>]>) -> Self::P
    {
        assert!(polycoeff.is_some() && polyeval.is_some()); // TODO: only need one technically
        let vc = self.polyring.indeterminate_count();
        assert!([polycoeff, polyeval].iter().all(|opt| opt.is_none_or(|v| v.len() == 1 << vc)));
        let d = self.code.d();
        let f = self.field();
        
        let fsclone = self.fs.borrow().clone();

        let mut polys: Vec<PolyEvals<BSCF<SC>,1>> = Vec::with_capacity(d);

        let bsc = SC::new(f, polyeval.unwrap(), z);
        let mut hunivar = bsc.compute_round_bsc(&[], Some(f.clone_el(&y)));
        // let mut hunivar = bsc.compute_round_bsc(&[], None);
        polys.push(hunivar);

        let mut proofcodes: Vec<Vec<El<BSCF<SC>>>> = Vec::with_capacity(d);
        let mut topcode = &com.code_el;

        let mut last: Vec<El<BSCF<SC>>> = Vec::with_capacity(
            if self.code.k(0) == 1 {0} else {self.code.k(0)});

        let mut challvec: Vec<El<BSCF<SC>>> = Vec::with_capacity(d - 1);
        
        for dind in (0..d).rev() {
            let chall = self.get_challenge();

            proofcodes.push({
                let (l, r) = topcode.split_at(self.code.n(dind));
                izip!(self.code.t(dind), l, r).map(|(ti, li, ri)|
                    interpdeg1(f, ti, li, ri, &chall)
                ).collect()
            });
            topcode = &proofcodes[d - 1 - dind];

            challvec.insert(0, chall);
            if dind != 0 {
                let tmpsum = polys[d - 1 - dind].interp(self.coeffring(), &challvec[0]);
                hunivar = bsc.compute_round_bsc(&challvec, Some(tmpsum));
                // hunivar = bsc.compute_round_bsc(&challvec, None);
                polys.push(hunivar);
            }
        }
    
        assert!(self.code.k(0).ilog2() as usize == vc - d);
        if self.code.k(0) > 1 {
            last = {
                let mut tmp = evaluate_at_fromevals(&f, vc, &challvec, polyeval.unwrap());
                evals_to_coeffs_inplace(&f, vc - d, &mut tmp);
                tmp
            }
        }

        self.fs.replace(fsclone);

        BaseFoldProof {
            code_els: proofcodes,
            sumcheck_els: polys,
            sumcheck_last: last
        }
    }
}


pub trait BaseFoldSumcheck<'a>: Sumcheck<2, 1>
{
    fn new(field: &'a BSCF<Self>, evalsref: &'a [El<BSCF<Self>>], z: Vec<El<BSCF<Self>>>) -> Self;

    fn compute_round_bsc(&self, challs: &[El<BSCF<Self>>], sum: Option<El<BSCF<Self>>>)
        -> PolyEvals<BSCF<Self>,1>;
}


pub struct BaseFoldSumcheckBasic<'a, R, const TE: bool>
    where R: RingStore
{
    field: &'a R,
    vc: usize,
    evalsref: &'a [El<R>],
    ws: RefCell<Vec<El<R>>>,
    z: Vec<El<R>>,
    scalarstate: RefCell<El<R>>
}

impl<'a, F, const TE: bool> BaseFoldSumcheck<'a> for BaseFoldSumcheckBasic<'a, F, TE>
    where F: RingStore<Type: Field + FiniteRing>
{
    #[instrument(skip_all)]
    fn new(field: &'a F, evalsref: &'a [El<F>], z: Vec<El<F>>) -> Self
    {
        let vc = z.len();
        assert!(1 << vc == evalsref.len());
        Self {
            field, vc,
            evalsref,
            ws: RefCell::default(),
            z,
            scalarstate: RefCell::new(field.one())
        }
    }

    #[instrument(skip_all)]
    fn compute_round_bsc(&self, challs: &[El<F>], sum: Option<El<F>>) -> PolyEvals<F,1> {
        self.compute_round(challs, sum)
    }
}


impl<'a, F, const TE: bool> SumcheckBase<2> for BaseFoldSumcheckBasic<'a, F, TE>
    where F: RingStore<Type: Field + FiniteRing>
{
    type F = F;

    fn field(&self) -> &F {
        self.field
    }

    fn varcount(&self) -> usize {
        self.vc
    }

    fn get_challenge(&self) -> El<F> {
        // we do not intend to call execute, so not needed
        unimplemented!()
    }

    fn get_other_eval_points(&self) -> [i32; 1] {
        [-1]
    }

    #[instrument(skip_all)]
    fn get_scalars<'b, 'c>(&'c self, challs: &'b [El<F>])
        -> impl Iterator<Item = (El<F>, El<F>)> + 'b
        where 'c: 'b
    {
        let field = self.field();
        let vcmini = self.vc - challs.len();
        let mut scstmut = self.scalarstate.borrow_mut();
        if challs.len() > 0 {
            field.mul_assign(&mut scstmut,
                MultilinearBasis::new(field, &self.z[vcmini..(vcmini + 1)]).evaluate(&challs[..1]));
        }
        MultilinearBasisEvals::new(field, &self.z[..(vcmini - 1)]).map(move |eqel| {
            let tmp = field.mul_ref_snd(eqel, &scstmut);
            let ztmp = &self.z[vcmini - 1];
            (
                field.mul_ref_fst(&tmp, field.sub_ref_snd(field.one(), ztmp)),
                field.mul_ref(&tmp, ztmp)
            )
        })
    }
}


impl<'a, F, const TE: bool> Sumcheck<2, 1> for BaseFoldSumcheckBasic<'a, F, TE>
    where F: RingStore<Type: Field + FiniteRing>
{
    type SCB = Self;

    fn TE() -> bool { TE }

    fn get_base(&self) -> &Self {
        &self
    }

    fn get_reference(&self) -> [&[El<F>]; 1] {
        [self.evalsref]
    }

    fn get_workspace(&self) -> [&RefCell<Vec<El<F>>>; 1] {
        [&self.ws]
    }

    fn compute_term(ring: &F, at: [&El<F>; 1], scalar: &El<F>) -> El<F> {
        ring.mul_ref(scalar, &at[0])
    }

    fn check_eval(&self, _rX: Vec<El<F>>) -> bool {
        // handled concurrently in the Basefold sumcheck
        unimplemented!()
    }
}


pub struct BaseFoldSumcheckDoubleEfficient<'a, R>
    where R: RingStore
{
    bscb: BaseFoldSumcheckBasic<'a, R, true>,
    m: usize,
}

impl<'a, F> BaseFoldSumcheck<'a> for BaseFoldSumcheckDoubleEfficient<'a, F>
    where F: RingStore<Type: Field + FiniteRing>
{
    #[instrument(skip_all)]
    fn new(field: &'a F, evalsref: &'a [El<F>], z: Vec<El<F>>) -> Self
    {
        let zclone = z.iter().map(|el| field.clone_el(el)).collect_vec();
        let bscb = BaseFoldSumcheckBasic::<'a, F, true>::new(field, evalsref, zclone);
        let m = bscb.vc.div_ceil(2);
        {
            let mut ws = bscb.ws.borrow_mut();
            ws.shrink_to(1 << m); // NOTE: basic basefoldsumcheck reserves too much
            let vcminm = bscb.vc - m;

            // TODO: refactor this as partial evaluation but msb->lsb
            let eq = MultilinearBasisEvals::new(field, &z[..vcminm]);
            bscb.get_reference()[0].chunks_exact(1 << vcminm).for_each(|chunki| ws.push(
                chunki.iter().zip(eq.clone()).fold(field.zero(), |acc, (evalj, eqj)|
                    field.add(acc, field.mul_ref(&evalj, &eqj)))
            ));
        }
        Self { bscb, m }
    }

    #[instrument(skip_all)]
    fn compute_round_bsc(&self, challs: &[El<F>], sum: Option<El<F>>) -> PolyEvals<F,1> {
        let i = challs.len();
        let field = self.bscb.field;
        let vc = self.bscb.vc;
        let z = &self.bscb.z;

        if i >= self.m {
            if i == self.m {
                let mut ws = self.bscb.ws.borrow_mut();
                *ws = evaluate_at_fromevals(field, vc, &challs[1..], self.bscb.get_reference()[0]);
                let mut scstmut = self.bscb.scalarstate.borrow_mut();
                *scstmut = MultilinearBasis::new(field, &z[(vc - i + 1)..]).evaluate(&challs[1..]);
            }
            return self.compute_round(challs, sum)
        }

        let mut hzero = field.zero();
        let mut hone = field.zero();
        let otherpoint = self.get_base().get_other_eval_points()[0];
        let other = field.int_hom().map(otherpoint);
        let mut hother = field.zero();

        let eq1 = MultilinearBasisEvals::new(field, &z[(vc - self.m)..(vc - i - 1)]);
        let eq2 = MultilinearBasisEvals::new(field, challs);

        self.get_base().ws.borrow().chunks_exact(1<<(self.m-i)).zip(eq2).for_each(|(wschunkj, eqj)| {

            let (wsz, wso) = wschunkj.split_at(1 << (self.m - i - 1));

            let mut tmpz = field.zero();
            let mut tmpo = field.zero();
            let mut tmpother = field.zero();

            izip!(wsz, wso, eq1.clone()).for_each(|(wszk, wsok, eqk)| {
                field.add_assign(&mut tmpz, field.mul_ref(&wszk, &eqk));
                
                if sum.is_none() {
                    field.add_assign(&mut tmpo, field.mul_ref(&wsok, &eqk));
                }

                field.add_assign(&mut tmpother, field.mul_ref_fst(&eqk, PolyEvals::new(
                        [field.clone_el(&wszk), field.clone_el(&wsok)], [], []
                    ).degone_at(field, otherpoint)))
            });

            field.add_assign(&mut hzero, field.mul_ref(&tmpz, &eqj));
            if sum.is_none() { field.add_assign(&mut hone, field.mul_ref(&tmpo, &eqj)) };
            field.add_assign(&mut hother, field.mul_ref(&tmpother, &eqj));
        });

        let scalar = MultilinearBasis::new(field, &z[(vc - i)..]).evaluate(challs);
        field.mul_assign(&mut hzero,
            field.mul_ref_fst(&scalar, field.sub_ref_snd(field.one(), &z[vc - i - 1])));
        if sum.is_none() {
            field.mul_assign(&mut hone, field.mul_ref(&scalar, &z[vc - i - 1]));
        }
        field.mul_assign(&mut hother, field.mul_ref_fst(&scalar,
            MultilinearBasis::new(field, &z[(vc - i - 1)..(vc - i)]).evaluate(&[other])));

        hone = if let Some(sum) = sum { field.sub_ref_snd(sum, &hzero) } else { hone };
        PolyEvals::new([hzero, hone], [otherpoint], [hother])
    }
}

impl<'a, F> Sumcheck<2, 1> for BaseFoldSumcheckDoubleEfficient<'a, F>
    where F: RingStore<Type: Field + FiniteRing>
{
    type SCB = BaseFoldSumcheckBasic<'a, F, true>;

    fn TE() -> bool { true }

    fn get_base(&self) -> &Self::SCB {
        &self.bscb
    }

    fn get_reference(&self) -> [&[El<F>]; 1] {
        // should not be called
        unimplemented!()
    }

    fn get_workspace(&self) -> [&RefCell<Vec<El<F>>>; 1] {
        [&self.get_base().ws]
    }

    fn compute_term(ring: &F, at: [&El<F>; 1], scalar: &El<F>) -> El<F> {
        <Self::SCB as Sumcheck<2, 1>>::compute_term(ring, at, scalar)
    }

    fn check_eval(&self, rX: Vec<El<F>>) -> bool {
        self.get_base().check_eval(rX)
    }
}


// outputs f(a) where f(X) = interpolate((x, y1), (-x, y2))
// (could possibly use feanor_math::algorithms::interpolate)
pub fn interpdeg1<F>(field: &F, x: &El<F>, y1: &El<F>, y2: &El<F>, a: &El<F>) -> El<F>
    where F: RingStore<Type: Field>
{
    let mut tmpleft = field.add_ref(a, x);
    let mut tmpright = field.sub_ref(x, a);
    field.mul_assign_ref(&mut tmpleft, y1);
    field.mul_assign_ref(&mut tmpright, y2);
    field.div(
        &field.add(tmpleft, tmpright),
        &field.get_ring().mul_int_ref(x, 2)
    )
}


#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::assert_el_eq;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::seq::VectorFn;
    use feanor_math::rings::zn::zn_64::Zn;
    use feanor_math::rings::finite::FiniteRingStore;
    use feanor_math::rings::field::AsField;

    use crate::util::gen_vector;
    use crate::multilinear::{from_hypercube_coeffs, sum_over_hypercube,
        evaluate_at_fromcoeff, coeffs_to_evals_inplace};

    const VREP: Option<usize> = Some(100);
    type FieldImpl = AsField<Zn>;

    #[test]
    #[ignore]
    fn test_basefolding() {

        let field = Zn::new(65537).as_field().ok().unwrap();

        let N = 7;
        let k0 = 1;
        let c = 2;
        let bf = BaseFoldPCS::<_, BaseFoldSumcheckBasic<_, false>>::new(&field, N, k0, c, VREP);
        let vc = bf.polyring().indeterminate_count();

        let randomcoeffs = gen_vector::<El<FieldImpl>>(||
            field.random_element(rand::random::<u64>), 1 << vc);
        let poly = from_hypercube_coeffs(bf.polyring(), &randomcoeffs);

        let topcode = bf.commit(&randomcoeffs).code_el;

        let chall = field.random_element(rand::random::<u64>);

        let d = bf.code.d();
        let foldedcode = bf.code.t(d-1).enumerate().map(|(i, ti)| {
            interpdeg1(&field, ti, &topcode[i], &topcode[i + bf.code.n(d-1)], &chall)
        }).collect_vec();

        let challconst = bf.polyring().create_term(field.clone_el(&chall),
            bf.polyring().create_monomial((0..vc).map(|_| 0)));
        let foldedevals = get_hypercube_coeffs(bf.polyring(),
            &bf.polyring().specialize(&poly, vc - 1, &challconst), vc - 1);
    
        assert!(foldedcode.len() == bf.code.n(d-1));
        assert!(foldedevals.len() == bf.code.k(d-1));

        let foldedcode2 = bf.code.encode(&foldedevals);
        assert!(foldedcode2.len() == bf.code.n(d-1));

        assert!((0..bf.code.n(d-1)).all(|i| field.eq_el(&foldedcode[i], &foldedcode2[i])));
    }

    #[test]
    #[ignore]
    fn test_basefoldpcs_slow() {
        
        let field = Zn::new(65537).as_field().ok().unwrap();

        let N = 5;
        let k0 = 2;
        let c = 2;
        let bf = BaseFoldPCS::<_, BaseFoldSumcheckBasic<_, false>>::new(&field, N, k0, c, VREP);

        let randomcoeffs = gen_vector::<El<FieldImpl>>(||
            field.random_element(rand::random::<u64>), 1 << N);
        let poly = from_hypercube_coeffs(bf.polyring(), &randomcoeffs);

        let zinner = gen_vector::<El<FieldImpl>>(|| field.random_element(rand::random::<u64>), N);
        let z = (0..N).map_fn(|i| field.clone_el(&zinner[i]));
        let y = bf.polyring().evaluate(&poly, &z, bf.coeffring().identity());

        let com = bf.commit(&randomcoeffs);

        let zvec: Vec<_> = z.into_iter().collect();
        let proof = bf.eval_slow(&com, &zvec, field.clone_el(&y), &poly);

        assert!(bf.verify(&com, &zvec, y, &randomcoeffs, proof))
    }

    #[test]
    fn test_basefoldsumchecksum() {

        let field = Zn::new(65537).as_field().ok().unwrap();

        let N = 5;
        let polyring = MultivariatePolyRingImpl::new(field.clone(), N);

        let randomcoeffs = gen_vector::<El<FieldImpl>>(||
            field.random_element(rand::random::<u64>), 1 << N);
        let mut poly = from_hypercube_coeffs(&polyring, &randomcoeffs);
        
        // to make poly have variables of deg 2
        let zinner = gen_vector::<El<FieldImpl>>(|| field.random_element(rand::random::<u64>), N);
        let z = (0..N).map_fn(|i| field.clone_el(&zinner[i]));
        let zvec: Vec<_> = z.clone().into_iter().collect();
        let eq = MultilinearBasis::new(&field, &zvec).polynomial(&polyring);
        poly = polyring.mul_ref_fst(&poly, eq);
        
        let sum = sum_over_hypercube(&polyring, &poly, N, &[]);

        let mut hd = sumcheck_sum(&polyring, &poly, N - 1, [2]);

        assert_el_eq!(field, &field.add(hd.at(&field, 0), hd.at(&field, 1)), &sum);

        let mut randomevals = randomcoeffs.iter().map(|el| field.clone_el(el)).collect_vec();
        coeffs_to_evals_inplace(&field, N, &mut randomevals);
        let bsc = BaseFoldSumcheckBasic::<_, false>::new(&field, &randomevals, zvec);
        let mut hdfast = bsc.compute_round(&[], Some(sum));
        // let mut hdfast = bsc.compute_round(&[], None);
        
        assert_el_eq!(field, &field.add(hd.at(&field, 0), hd.at(&field, 1)), &sum);
        hd.eq(&field, &hdfast);

        let mut rvec: Vec<El<FieldImpl>> = vec![];
        for ind in 1..=N-1 {
            //println!("tested: {}", ind - 1);
            let r = field.random_element(rand::random::<u64>);
            poly = polyring.specialize(&poly, N - ind,
                &polyring.create_term(field.clone_el(&r), polyring.create_monomial((0..N).map(|_| 0))));
            let sum = hd.interp(&field, &r);
            hd = sumcheck_sum(&polyring, &poly, N - ind - 1, [2]);
            assert_el_eq!(field, &field.add(hd.at(&field, 0), hd.at(&field, 1)), &sum);
            rvec.insert(0, r);
            hdfast = bsc.compute_round(&rvec, Some(sum));
            // hdfast = bsc.compute_round(&rvec, None);
            hd.eq(&field, &hdfast);
        }
    }

    // use tracing_subscriber::prelude::*;

    #[test]
    fn test_basefoldpcs_fast()
    {
        // let (chrome_layer, _guard) = tracing_chrome::ChromeLayerBuilder::new().build();
        // tracing_subscriber::registry().with(chrome_layer).init();

        let field = Zn::new(65537).as_field().ok().unwrap();
        
        let N = 16;
        let k0 = 2;
        let c = 2;

        let bf = BaseFoldPCS::<_,
            // BaseFoldSumcheckBasic<_, true>
            // BaseFoldSumcheckBasic<_, false>
            BaseFoldSumcheckDoubleEfficient<_> // wow, this is almost twice as fast :)
        >::new(&field, N, k0, c, VREP);

        let randomcoeffs = gen_vector::<El<FieldImpl>>(||
            field.random_element(rand::random::<u64>), 1 << N);
        let z = gen_vector::<El<FieldImpl>>(|| field.random_element(rand::random::<u64>), N);
        let y = evaluate_at_fromcoeff(&field, N, &z, &randomcoeffs).pop().unwrap();

        let com = bf.commit(&randomcoeffs);

        let mut evals = randomcoeffs.iter().map(|el| field.clone_el(el)).collect_vec();
        coeffs_to_evals_inplace(&field, N, &mut evals);
        let clonedz = z.iter().map(|el| field.clone_el(el)).collect_vec();
        let proof = bf.eval(&com, clonedz, field.clone_el(&y), Some(&randomcoeffs), Some(&evals));

        assert!(bf.verify(&com, &z, y, &randomcoeffs, proof));
    }
    
}


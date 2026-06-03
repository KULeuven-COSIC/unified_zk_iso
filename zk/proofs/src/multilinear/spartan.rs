use itertools::{izip, Itertools};
use std::cell::{RefMut, RefCell};
use rand::Rng;

use feanor_math::integer::{BigIntRing, IntegerRingStore};
use feanor_math::field::Field;
use feanor_math::ring::{RingStore, El};
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};

use crate::{
    codes::foldablecodes::RSFoldableCode,
    commit::{
        MultilinearPCS,
        basefold::{
            BaseFoldPCS,
            BaseFoldSumcheck
        },
    },
    r1cs::R1CS,
    util::{gen_vector, Coeff, CoeffRing},
    multilinear::{
        sumcheck::{Sumcheck, SumcheckBase},
        MultilinearBasis, MultilinearBasisEvals,
        evals_to_coeffs_inplace, evaluate_at_fromcoeff
    }
};

pub struct SpartanPIOP<'a, PCS: MultilinearPCS<'a>>
{
    vc_rows: usize,
    vc_cols: usize,
    r1cs: R1CS<'a, CoeffRing<PCS::Poly>>,
    z: Vec<Coeff<PCS::Poly>>, // TODO: can also be &'a reference
    zA: Vec<Coeff<PCS::Poly>>,
    zB: Vec<Coeff<PCS::Poly>>,
    zC: Vec<Coeff<PCS::Poly>>,
    pcs: PCS,
    zcoeff: Option<Vec<Coeff<PCS::Poly>>>,
    com: Option<PCS::C>
}

impl<'a, F, BSC> SpartanPIOP<'a, BaseFoldPCS<'a, RSFoldableCode<'a, F>, BSC>>
    where F: RingStore + Clone, F::Type: Field + FiniteRing,
          BSC: BaseFoldSumcheck<'a>, <BSC as Sumcheck<2,1>>::SCB: SumcheckBase<2, F = F>
{
    pub fn new_extra(field: &'a F, z: Vec<El<F>>, r1cs: R1CS<'a, F>,
        zA: Vec<El<F>>, zB: Vec<El<F>>, zC: Vec<El<F>>, ver_rep: Option<usize>) -> Self
    {
        assert!(z.len().is_power_of_two());
        let vc_cols = z.len().ilog2() as usize;

        // TODO: set reasonable parameters here
        let k0 = 1;
        let c = 8;

        let pcs = BaseFoldPCS::<'a, RSFoldableCode<'a, F>, BSC>
            ::new(field, vc_cols, k0, c, ver_rep);

        // if none then we do not intend on actually computing the pcs at the end
        let (zcoeff, com) = if ver_rep.is_some() {
            // TODO: avoid clone here?
            let mut zcoeff = z.iter().map(|el| field.clone_el(el)).collect_vec();
            evals_to_coeffs_inplace(field, vc_cols, &mut zcoeff);
            let com = pcs.commit(&zcoeff);
            (Some(zcoeff), Some(com))
        } else {(None, None)};

        let vc_rows = r1cs.A.rowlogsize();

        Self {
            pcs,
            vc_rows,
            vc_cols,
            r1cs,
            z, zA, zB, zC,
            zcoeff,
            com
        }
    }

    pub fn new(ring: &'a F, z: Vec<El<F>>, r1cs: R1CS<'a, F>, ver_rep: usize) -> Self
    {
        let zA = r1cs.A.mul(&z);
        let zB = r1cs.B.mul(&z);
        let zC = r1cs.C.mul(&z);
        SpartanPIOP::new_extra(ring, z, r1cs, zA, zB, zC, Some(ver_rep))
    }

    pub fn proofsize(&'a self) -> usize {
        let rowchecksize = 4*self.vc_rows;
        let linchecksize = 3*self.vc_cols;
        let ZZbig: BigIntRing = BigIntRing::RING;
        let bits =
            ZZbig.abs_log2_ceil(&self.pcs.coeffring().characteristic(ZZbig).unwrap()).unwrap();
        return self.pcs.proofsize() + bits*(rowchecksize + linchecksize)
    }
}
    
impl<'a, PCS: MultilinearPCS<'a>> SpartanPIOP<'a, PCS>
{
    pub fn field(&self) -> &CoeffRing<PCS::Poly> {
        self.pcs.coeffring()
    }

    pub fn varcount_rows(&self) -> usize {
        self.vc_rows
    }

    pub fn varcount_cols(&self) -> usize {
        self.vc_cols
    }

    // pub fn tau(&self) -> &Vec<Coeff<PCS::Poly>> {
    //     &self.tau
    // }

    pub fn challenge(&mut self) -> Coeff<PCS::Poly> {
        self.pcs.get_challenge()
    }

    pub fn get_zM(&self) -> [&Vec<Coeff<PCS::Poly>>; 4] {
        [&self.z, &self.zA, &self.zB, &self.zC]
    }
}

impl<'a, F, BSC> SpartanPIOP<'a, BaseFoldPCS<'a, RSFoldableCode<'a, F>, BSC>>
    where F: RingStore + Clone, F::Type: Field + FiniteRing,
          BSC: BaseFoldSumcheck<'a>, <BSC as Sumcheck<2,1>>::SCB: SumcheckBase<2, F = F>
{
    pub fn random<RNG: Rng>(field: &'a F, mut rng: RNG,
        vc: usize, vcrows: usize, ver_rep: usize) -> Self
    {
        let mut z = gen_vector::<El<F>>(||
            field.random_element(|| rng.next_u64()), 1 << vc);
        while z.iter().all(|zi| field.is_zero(zi)) {
            z = gen_vector::<El<F>>(|| field.random_element(|| rng.next_u64()), 1 << vc);
        }
        let (r1cs, zA, zB, zC) = R1CS::random_from(field, rng, &z, 1 << vcrows);
        SpartanPIOP::new_extra(field, z, r1cs, zA, zB, zC, Some(ver_rep))
    }
}

impl<'a, PCS> SpartanPIOP<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    pub fn execute(&'a self) -> bool {
        let rowchecksum = self.field().zero();
        let rowcheck = SpartanRowcheck::for_piop(self);
        if let Some(rX) = rowcheck.execute(rowchecksum) {
            // println!("SpartanRowcheck complete!");
            rowcheck.check_eval(rX)
        } else { false }
    }
}


pub struct SpartanRowcheckBase<'a, PCS: MultilinearPCS<'a>> {
    piop: &'a SpartanPIOP<'a, PCS>,
    tau: Vec<Coeff<PCS::Poly>>
}

impl<'a, PCS: MultilinearPCS<'a>> SpartanRowcheckBase<'a, PCS>
{
    pub fn for_piop(piop: &'a SpartanPIOP<'a, PCS>) -> Self {

        let tau = (0..piop.vc_rows).map(|_| piop.pcs.get_challenge()).collect();
        Self { piop, tau }
    }

    pub fn piop(&self) -> &SpartanPIOP<'a, PCS> {
        &self.piop
    }
}

impl<'a, PCS> SumcheckBase<3> for SpartanRowcheckBase<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type F = CoeffRing<PCS::Poly>;

    fn field(&self) -> &Self::F {
        self.piop.field()
    }

    fn varcount(&self) -> usize {
        self.piop.varcount_rows()
    }

    fn get_challenge(&self) -> El<Self::F> {
        self.piop.pcs.get_challenge()
    }

    fn get_other_eval_points(&self) -> [i32; 2] {
        [-1, 2]
    }

    fn get_scalars<'d, 'c>(&'c self, challs: &'d [El<Self::F>])
        -> impl Iterator<Item = (El<Self::F>, El<Self::F>)> + 'd
        where 'c: 'd
    {
        let field = self.piop.field();
        let vc = self.varcount();
        let i = challs.len();
        let zero = field.zero();
        let tmp = MultilinearBasis::new(field, &self.tau[(vc - i)..]).evaluate(challs);
        let taudmini = if i < vc { &self.tau[vc - i - 1] } else { &zero };
        let cz = field.mul_ref_fst(&tmp, field.sub_ref_snd(field.one(), taudmini));
        let co = field.mul_ref_snd(tmp, taudmini);
        let eq = MultilinearBasisEvals::new(field, &self.tau[..(vc - i).saturating_sub(1)]);
        eq.map(move |eqi| (
            field.mul_ref(&cz, &eqi),
            field.mul_ref_fst(&co, eqi)
        ))
    }
}

pub struct SpartanRowcheck<'a, PCS: MultilinearPCS<'a>> {
    base: SpartanRowcheckBase<'a, PCS>,
    zA: RefCell<Vec<Coeff<PCS::Poly>>>,
    zB: RefCell<Vec<Coeff<PCS::Poly>>>,
    zC: RefCell<Vec<Coeff<PCS::Poly>>>
}

impl<'a, PCS: MultilinearPCS<'a>> SpartanRowcheck<'a, PCS>
{
    pub fn for_piop(piop: &'a SpartanPIOP<'a, PCS>) -> Self {
        Self {
            base: SpartanRowcheckBase::for_piop(piop),
            zA: RefCell::default(),
            zB: RefCell::default(),
            zC: RefCell::default()
        }
    }

    pub fn base(&self) -> &SpartanRowcheckBase<'a, PCS> {
        &self.base
    }

    // pub fn move_out(self) -> SpartanPIOP<'a, PCS> {
    //     self.base.piop
    // }
}

impl<'a, PCS> Sumcheck<3, 3> for SpartanRowcheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type SCB = SpartanRowcheckBase<'a, PCS>;

    fn TE() -> bool { true } // TODO: make generic const?

    fn get_base(&self) -> &Self::SCB {
        &self.base
    }

    fn get_reference(&self) -> [&[Coeff<PCS::Poly>]; 3] {
        [&self.base.piop.zA, &self.base.piop.zB, &self.base.piop.zC]
    }

    fn get_workspace(&self) -> [&RefCell<Vec<Coeff<PCS::Poly>>>; 3] {
        [&self.zA, &self.zB, &self.zC]
    }

    fn compute_term(ring: &CoeffRing<PCS::Poly>, at: [&Coeff<PCS::Poly>; 3], scalar: &Coeff<PCS::Poly>) -> Coeff<PCS::Poly> {
        ring.mul_ref_fst(&scalar, ring.sub_ref_snd(ring.mul_ref(at[0], at[1]), at[2]))
    }

    fn check_eval(&self, rX: Vec<Coeff<PCS::Poly>>) -> bool {
        let rA = self.get_base().get_challenge();
        let rB = self.get_base().get_challenge();
        let rC = self.get_base().get_challenge();
        let linchecksum = {
            let ws = self.get_workspace();
            let mut wsmut: [RefMut<'_, _>; 3] = core::array::from_fn(|i| ws[i].borrow_mut());
            SpartanLincheck::<PCS>::compute_start(self.base.field(), &rA, &rB, &rC,
                wsmut[0].pop().unwrap(), wsmut[1].pop().unwrap(), wsmut[2].pop().unwrap())
        };
        let lincheck = SpartanLincheck::for_piop(self.base.piop, &[rA], &[rB], &[rC], rX);
        if let Some(rY) = lincheck.execute(linchecksum) {
            // println!("SpartanLincheck complete!");
            lincheck.check_eval(rY)
        } else { false }
    }
}


pub struct SpartanLincheckBase<'a, PCS: MultilinearPCS<'a>>
{
    piop: &'a SpartanPIOP<'a, PCS>
}

impl<'a, PCS:MultilinearPCS<'a>> SpartanLincheckBase<'a, PCS>
{
    pub fn for_piop(piop: &'a SpartanPIOP<'a, PCS>) -> Self
    {
        Self { piop }
    }
}

impl<'a, PCS> SumcheckBase<2> for SpartanLincheckBase<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type F = CoeffRing<PCS::Poly>;

    fn field(&self) -> &Self::F {
        self.piop.field()
    }

    fn varcount(&self) -> usize {
        self.piop.varcount_cols()
    }

    fn get_challenge(&self) -> El<Self::F> {
        self.piop.pcs.get_challenge()
    }

    fn get_other_eval_points(&self) -> [i32; 1] {
        [-1]
    }

    fn get_scalars<'c, 'd>(&'d self, challs: &'c [El<Self::F>])
        -> impl Iterator<Item = (El<Self::F>, El<Self::F>)> + 'c
        where 'd: 'c
    {
        let field = self.piop.field();
        (0..(1 << (self.varcount() - challs.len()).saturating_sub(1))).map(|_|
            (field.one(), field.one()))
    }
}

pub struct SpartanLincheck<'a, PCS: MultilinearPCS<'a>>
{
    base: SpartanLincheckBase<'a, PCS>,
    M: Vec<Coeff<PCS::Poly>>,
    wsM: RefCell<Vec<Coeff<PCS::Poly>>>,
    wsz: RefCell<Vec<Coeff<PCS::Poly>>>
}

impl<'a, PCS> SpartanLincheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field>
{

    pub fn for_piop(piop: &'a SpartanPIOP<'a, PCS>, rA: &[Coeff<PCS::Poly>], rB: &[Coeff<PCS::Poly>],
        rC: &[Coeff<PCS::Poly>], rX: Vec<Coeff<PCS::Poly>>) -> Self
    {
        // TODO: can we avoid having to store M for duration 'a ?
        let M = SpartanLincheck::get_zM(&piop, rA, rB, rC, rX);
        let base = SpartanLincheckBase::for_piop(piop);
        Self { base, M, wsM: RefCell::default(), wsz: RefCell::default() }
    }

    pub fn get_zM(piop: &SpartanPIOP<'a, PCS>, rA: &[Coeff<PCS::Poly>], rB: &[Coeff<PCS::Poly>],
        rC: &[Coeff<PCS::Poly>], rX: Vec<Coeff<PCS::Poly>>) -> Vec<Coeff<PCS::Poly>>
    {
        debug_assert!(rA.len() == rB.len());
        debug_assert!(rB.len() == rC.len());
        debug_assert!(1 << (piop.vc_rows - rX.len()) == rA.len());
        // TODO: would it be faster to first make a linear combination of the matrices and only
        // then evaluate that matrix at the rowvars?
        let ArX = piop.r1cs.A.evaluate_rowvars(&rX);
        let BrX = piop.r1cs.B.evaluate_rowvars(&rX);
        let CrX = piop.r1cs.C.evaluate_rowvars(&rX);
        let field = piop.field();
        (0..(1 << piop.vc_cols)).map(|j| izip!(ArX.iter(), BrX.iter(), CrX.iter(), rA, rB, rC).fold(
            field.zero(), |acc, (ArXi, BrXi, CrXi, rAi, rBi, rCi)| field.add(acc,
                SpartanLincheck::<PCS>::compute_start(field, rAi, rBi, rCi,
                    field.clone_el(&ArXi[j]), field.clone_el(&BrXi[j]), field.clone_el(&CrXi[j])))
        )).collect()
    }

    pub fn compute_start(ring: &CoeffRing<PCS::Poly>, rA: &Coeff<PCS::Poly>, rB: &Coeff<PCS::Poly>,
        rC: &Coeff<PCS::Poly>, vA: Coeff<PCS::Poly>, vB: Coeff<PCS::Poly>, vC: Coeff<PCS::Poly>)
        -> Coeff<PCS::Poly>
    {
        ring.add(ring.mul_ref_fst(rA, vA),
            ring.add(ring.mul_ref_fst(rB, vB), ring.mul_ref_fst(rC, vC)))
    }

    // pub fn get_wsM(&self) -> &RefCell<Vec<Coeff<PCS::Poly>>> {
    //     &self.wsM
    // }
}

impl<'a, PCS> Sumcheck<2, 2> for SpartanLincheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type SCB = SpartanLincheckBase<'a, PCS>;

    fn TE() -> bool { true } // TODO: make generic const?

    fn get_base(&self) -> &Self::SCB {
        &self.base
    }

    fn get_reference(&self) -> [&[Coeff<PCS::Poly>]; 2] {
        [&self.M, &self.base.piop.z]
    }

    fn get_workspace(&self) -> [&RefCell<Vec<Coeff<PCS::Poly>>>; 2] {
        [&self.wsM, &self.wsz]
    }

    fn compute_term(ring: &CoeffRing<PCS::Poly>, at: [&Coeff<PCS::Poly>; 2], _scalar: &Coeff<PCS::Poly>) -> Coeff<PCS::Poly> {
        ring.mul_ref(at[0], at[1])
    }

    fn check_eval(&self, rX: Vec<Coeff<PCS::Poly>>) -> bool {
        // TODO: check _evalM
        let ring = self.base.field();
        let y = {
            let [_evalM, evalz] = self.get_workspace();
            let evalzref = evalz.borrow();
            debug_assert!(evalzref.len() == 1);
            ring.clone_el(&evalzref[0])
        };
        let zcoeff = self.base.piop.zcoeff.as_ref().unwrap();
        let com = self.base.piop.com.as_ref().unwrap();
        {
            let ev = evaluate_at_fromcoeff(ring, self.base.varcount(), &rX, zcoeff);
            debug_assert!(ring.eq_el(&y, &ev[0]));
        }
        let clonedrX = rX.iter().map(|el| ring.clone_el(el)).collect_vec();
        let proof = self.base.piop.pcs.eval(com, rX,
            ring.clone_el(&y), Some(zcoeff), Some(&self.base.piop.z));
        let clonedy = ring.clone_el(&y);
        self.base.piop.pcs.verify(com, &clonedrX, clonedy, zcoeff, proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::rings::zn::zn_64::Zn;
    use crate::commit::basefold::{BaseFoldSumcheckBasic, BaseFoldSumcheckDoubleEfficient};

    const VREP: usize = 100;

    #[test]
    fn test_spartan() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        let mut rng = rand::rng();

        let N = 14;
        
        let spartan: SpartanPIOP::<'_, BaseFoldPCS<'_, RSFoldableCode<_>,
            BaseFoldSumcheckDoubleEfficient<_>>>
                = SpartanPIOP::random(&field, &mut rng, N, N+1, VREP);

        assert!(spartan.execute());
    }
}

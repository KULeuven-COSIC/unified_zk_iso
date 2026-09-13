use itertools::Itertools;
use std::cell::{RefCell};

use feanor_math::integer::{BigIntRing, IntegerRingStore};
use feanor_math::field::Field;
use feanor_math::ring::{RingStore, El};
use feanor_math::rings::finite::FiniteRing;

use crate::{
    codes::foldablecodes::RSFoldableCode,
    commit::MultilinearPCS,
    commit::basefold::{BaseFoldPCS, BaseFoldSumcheck},
    util::{Coeff, CoeffRing},
    multilinear::{
        sumcheck::{Sumcheck, SumcheckBase},
        MultilinearBasisEvals,
        evals_to_coeffs_inplace,
        evaluate_at_fromevals
    },
    util::matmul::{MatrixMul, DenseMatrixMul}
};

pub struct vMMPIOP<'a, PCS: MultilinearPCS<'a>>
{
    vc_rows: usize,
    vc_cols: usize,
    tau: Vec<Coeff<PCS::Poly>>,
    z: Vec<Coeff<PCS::Poly>>,
    M: DenseMatrixMul<'a, CoeffRing<PCS::Poly>>,
    pcs: PCS,
    Mcom: PCS::C,
    Mcoeff: Vec<Coeff<PCS::Poly>>,
    zMtau: Coeff<PCS::Poly>
}

impl<'a, F, BSC> vMMPIOP<'a, BaseFoldPCS<'a, RSFoldableCode<'a, F>, BSC>>
    where F: RingStore + Clone, F::Type: Field + FiniteRing,
          BSC: BaseFoldSumcheck<'a>, <BSC as Sumcheck<2,1>>::SCB: SumcheckBase<2, F = F>
{
    pub fn new_extra(field: &'a F, z: Vec<El<F>>, zM: Vec<El<F>>, M: DenseMatrixMul<'a, F>, k0: usize, c: usize, ver_rep: Option<usize>)
        -> Self
    {
        assert!(z.len().is_power_of_two());
        let vc_cols = z.len().ilog2() as usize;
        let vc_rows = zM.len().ilog2() as usize;
        let pcs = BaseFoldPCS::new(field, vc_cols + vc_rows, k0, c, ver_rep);

        let mut Mcoeff = M.data().iter().map(|el| field.clone_el(el)).collect_vec();
        evals_to_coeffs_inplace(field, vc_cols + vc_rows, &mut Mcoeff);
        let Mcom = pcs.commit(&Mcoeff);

        let tau = (0..vc_rows).map(|_| pcs.get_challenge()).collect_vec();

        let zMtau = evaluate_at_fromevals(field, vc_rows, &tau, &zM).pop().unwrap();

        Self {
            vc_rows,
            vc_cols,
            tau,
            z,
            M,
            pcs,
            Mcom,
            Mcoeff,
            zMtau
        }
    }

    pub fn new(ring: &'a F, z: Vec<El<F>>, M: DenseMatrixMul<'a, F>,
        k0: usize, c: usize, ver_rep: usize) -> Self
    {
        let zM = M.mul(&z);
        vMMPIOP::new_extra(ring, z, zM, M, k0, c, Some(ver_rep))
    }

    pub fn proofsize(&self) -> usize {
        let linchecksize = 3*self.vc_cols;
        let ZZbig: BigIntRing = BigIntRing::RING;
        let bits = ZZbig.abs_log2_ceil(&self.pcs.coeffring().characteristic(ZZbig).unwrap()).unwrap();
        return self.pcs.proofsize() + bits*linchecksize
    }
}
    
impl<'a, PCS: MultilinearPCS<'a>> vMMPIOP<'a, PCS>
{

    pub fn matrix(&self) -> &DenseMatrixMul<'a, CoeffRing<PCS::Poly>> {
        &self.M
    }

    pub fn field(&self) -> &CoeffRing<PCS::Poly> {
        self.pcs.coeffring()
    }

    pub fn varcount_rows(&self) -> usize {
        self.vc_rows
    }

    pub fn varcount_cols(&self) -> usize {
        self.vc_cols
    }

    pub fn tau(&self) -> &Vec<Coeff<PCS::Poly>> {
        &self.tau
    }

    pub fn challenge(&mut self) -> Coeff<PCS::Poly> {
        self.pcs.get_challenge()
    }

    pub fn get_z(&self) -> &Vec<Coeff<PCS::Poly>> {
        &self.z
    }

    pub fn zMtau(&self) -> &Coeff<PCS::Poly> {
        &self.zMtau
    }

    pub fn pcs(&self) -> &PCS {
        &self.pcs
    }

    pub fn Mcom_coeff(&self) -> (&PCS::C, &Vec<Coeff<PCS::Poly>>) {
        (&self.Mcom, &self.Mcoeff)
    }
}

// NOTE: clean this when rand_seeder is updated
use rand_seeder::{Seeder, SipRng, rand_core::TryRng};
use feanor_math::rings::finite::FiniteRingStore;
use crate::util::gen_vector;

impl<'a, F, BSC> vMMPIOP<'a, BaseFoldPCS<'a, RSFoldableCode<'a, F>, BSC>>
    where F: RingStore + Clone, F::Type: Field + FiniteRing,
          BSC: BaseFoldSumcheck<'a>, <BSC as Sumcheck<2,1>>::SCB: SumcheckBase<2, F = F>
{
    pub fn random(field: &'a F, vc: usize, vcrows: usize,
        k0: usize, c: usize, ver_rep: usize) -> Self
    {
        let mut rng: SipRng = Seeder::from("vMMPIOP").into_rng();
        let mut z = gen_vector::<El<F>>(||
            field.random_element(|| rng.try_next_u64().ok().unwrap()), 1 << vc);
        while z.iter().all(|zi| field.is_zero(zi)) {
            z = gen_vector::<El<F>>(|| field.random_element(|| rng.try_next_u64().ok().unwrap()), 1 << vc);
        }
        let Mdata = gen_vector::<El<F>>(||
            field.random_element(|| rng.try_next_u64().ok().unwrap()), (1 << vcrows)*z.len());

        let M = DenseMatrixMul::new(field, z.len(), Mdata,
            format!("MMdatabase{vc}{vcrows}").as_str());
        let zM = M.mul(&z);
        vMMPIOP::new_extra(field, z, zM, M, k0, c, Some(ver_rep))
    }
}

impl<'a, PCS> vMMPIOP<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    pub fn execute(&'a self) -> bool {
        let linchecksum = self.field().clone_el(&self.zMtau);
        let lincheck = vMMLincheck::for_piop(self);
        if let Some(rX) = lincheck.execute(linchecksum) {
            lincheck.check_eval(rX)
        } else { false }
    }
}


pub struct vMMLincheckBase<'a, PCS: MultilinearPCS<'a>>
{
    piop: &'a vMMPIOP<'a, PCS>
}

impl<'a, PCS:MultilinearPCS<'a>> vMMLincheckBase<'a, PCS>
{
    pub fn for_piop(piop: &'a vMMPIOP<'a, PCS>) -> Self
    {
        Self { piop }
    }

    pub fn get_piop(&self) -> &vMMPIOP<'a, PCS> {
        &self.piop
    }
}

impl<'a, PCS> SumcheckBase<2> for vMMLincheckBase<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type F = CoeffRing<PCS::Poly>;

    fn field(&self) -> &Self::F {
        self.get_piop().field()
    }

    fn varcount(&self) -> usize {
        self.get_piop().varcount_cols()
    }

    fn get_challenge(&self) -> El<Self::F> {
        self.get_piop().pcs.get_challenge()
    }

    fn get_other_eval_points(&self) -> [i32; 1] {
        [-1]
    }

    fn get_scalars<'c, 'd>(&'d self, challs: &'c [El<Self::F>])
        -> impl Iterator<Item = (El<Self::F>, El<Self::F>)> + 'c
        where 'd: 'c
    {
        let field = self.field();
        (0..(1 << (self.varcount() - challs.len()).saturating_sub(1))).map(|_|
            (field.one(), field.one()))
    }
}

pub struct vMMLincheck<'a, PCS: MultilinearPCS<'a>>
{
    base: vMMLincheckBase<'a, PCS>,
    tauM: Vec<Coeff<PCS::Poly>>,
    wsM: RefCell<Vec<Coeff<PCS::Poly>>>,
    wsz: RefCell<Vec<Coeff<PCS::Poly>>>
}

impl<'a, PCS> vMMLincheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field>
{
    pub fn for_piop(piop: &'a vMMPIOP<'a, PCS>) -> Self
    {
        let field = piop.field();
        let M = &piop.M;
        let mut tauM = (0..M.columns()).map(|_| field.zero()).collect_vec();

        let eqevals = MultilinearBasisEvals::new(field, &piop.tau);
        
        M.data().chunks_exact(M.columns()).zip(eqevals).for_each(|(Mrow, eqi)|
            Mrow.iter().zip(tauM.iter_mut()).for_each(|(Mj, rj)|
                field.add_assign(rj, field.mul_ref_fst(Mj, field.clone_el(&eqi)))
            )
        );
        
        let base = vMMLincheckBase::for_piop(piop);
        Self { base, tauM,
            wsM: RefCell::default(), wsz: RefCell::default() }
    }

    pub fn get_wsM(&self) -> &RefCell<Vec<Coeff<PCS::Poly>>> {
        &self.wsM
    }
}

impl<'a, PCS> Sumcheck<2, 2> for vMMLincheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type SCB = vMMLincheckBase<'a, PCS>;

    fn TE() -> bool { true } // TODO: make generic const?

    fn get_base(&self) -> &Self::SCB {
        &self.base
    }

    fn get_reference(&self) -> [&[Coeff<PCS::Poly>]; 2] {
        [&self.tauM, &self.base.piop.z]
    }

    fn get_workspace(&self) -> [&RefCell<Vec<Coeff<PCS::Poly>>>; 2] {
        [&self.wsM, &self.wsz]
    }

    fn compute_term(ring: &CoeffRing<PCS::Poly>, at: [&Coeff<PCS::Poly>; 2], _scalar: &Coeff<PCS::Poly>) -> Coeff<PCS::Poly> {
        ring.mul_ref(at[0], at[1])
    }

    fn check_eval(&self, rX: Vec<Coeff<PCS::Poly>>) -> bool {
        let ring = self.base.field();
        let (u, MtaurX) = {
            let [evalM, evalz] = self.get_workspace();
            let evalzref = evalz.borrow();
            let evalMref = evalM.borrow();
            debug_assert!(evalzref.len() == 1 && evalMref.len() == 1);
            (ring.clone_el(&evalzref[0]), ring.clone_el(&evalMref[0]))
        };

        let z = self.get_base().get_piop().get_z();
        let z_at_rX = evaluate_at_fromevals(ring, self.base.piop.varcount_cols(), &rX, z).pop().unwrap();
        if !ring.eq_el(&u, &z_at_rX) { return false }

        let taurX = rX.iter().chain(self.base.piop.tau.iter()).map(|el|
            ring.clone_el(el)).collect_vec();
        let taurXclone = taurX.iter().map(|el| ring.clone_el(el)).collect_vec();
        let proof = self.base.piop.pcs.eval(&self.base.piop.Mcom, taurXclone,
            ring.clone_el(&MtaurX), Some(&self.base.piop.Mcoeff), Some(self.base.piop.matrix().data()));
        self.base.piop.pcs.verify(&self.base.piop.Mcom, &taurX, MtaurX,
            &self.base.piop.Mcoeff, proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::rings::zn::zn_64::Zn;

    const VREP: usize = 100;

    #[test]
    fn test_vmm() {

        let field = Zn::new(65537).as_field().ok().unwrap();

        // let N = 4;
        let N = 10;
        
        let vmm: vMMPIOP<'_, BaseFoldPCS<'_, RSFoldableCode<'_, _>,
            crate::commit::basefold::BaseFoldSumcheckDoubleEfficient<_>>>
                = vMMPIOP::random(&field, N, N+1, 4, 2, VREP);

        assert!(vmm.execute());
    }
}

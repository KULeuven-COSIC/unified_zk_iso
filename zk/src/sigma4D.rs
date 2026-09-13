use itertools::{izip, Itertools};
use std::cell::RefCell;
use rand::Rng;

use feanor_math::ring::{RingStore, RingBase, El};
use feanor_math::field::{Field, FieldStore};
use feanor_math::divisibility::DivisibilityRingStore;
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};
use feanor_math::rings::zn::{zn_static::{Zn, ZnBase}, ZnRing};
use feanor_math::homomorphism::{Homomorphism, CanHomFrom};
use feanor_math::rings::field::AsField;
use feanor_math::integer::{BigIntRingBase, IntegerRingStore};

use proofs::{
    FSRng,
    lattice::{RejSamplModes, sigma::{LatSigma, LatSigmaDefault, LatSigmaProof}},
    commit::{
        MultilinearPCS,
        abdlop::{ZZbig, ABDLOP, ABDLOPmessage, ABDLOPcommitment, ABDLOPRingTrait, ABDLOPRing}
    },
    multilinear::{
        evaluate_at_fromevals_inplace, MultilinearBasisEvals,
        sumcheck::{Sumcheck, SumcheckBase, PolyEvals},
        spartan::{
            SpartanPIOP,
            SpartanRowcheckBase,
            SpartanLincheck, SpartanLincheckBase
        }
    },
    util::{
        Coeff, CoeffRing,
        matmul::{MatrixMul, SparseMatrixMul, DenseMatrixMul}
    }
};

use crate::{
    construct_r1cs_Fp, smaller_densemm,
    pcs::{BaseFoldPCSDefault, SpartanPIOPDefault}
};


const Z2: Zn<2> = Zn::from(ZnBase::new());


pub struct ZKisoRowcheck<'a, PCS: MultilinearPCS<'a>> {
    base: SpartanRowcheckBase<'a, PCS>,
    z1: RefCell<Vec<Coeff<PCS::Poly>>>,
    z2: RefCell<Vec<Coeff<PCS::Poly>>>
}

impl<'a, PCS: MultilinearPCS<'a>> ZKisoRowcheck<'a, PCS>
{
    pub fn for_piop(piop: &'a SpartanPIOP<'a, PCS>) -> Self {
        Self {
            base: SpartanRowcheckBase::for_piop(piop),
            z1: RefCell::default(),
            z2: RefCell::default()
        }
    }
}

impl<'a, PCS> Sumcheck<3, 2> for ZKisoRowcheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type SCB = SpartanRowcheckBase<'a, PCS>;

    fn TE() -> bool { true }

    fn get_base(&self) -> &Self::SCB {
        &self.base
    }

    fn get_reference(&self) -> [&[Coeff<PCS::Poly>]; 2] {
        [&self.base.piop().get_zM()[1], &self.base.piop().get_zM()[3]]
    }

    fn get_workspace(&self) -> [&RefCell<Vec<Coeff<PCS::Poly>>>; 2] {
        [&self.z1, &self.z2]
    }

    fn compute_term(ring: &CoeffRing<PCS::Poly>, at: [&Coeff<PCS::Poly>; 2], scalar: &Coeff<PCS::Poly>) -> Coeff<PCS::Poly> {
        ring.mul_ref_fst(&scalar, ring.sub_ref_snd(ring.mul_ref(at[0], at[0]), at[1]))
    }

    fn check_eval(&self, _rX: Vec<Coeff<PCS::Poly>>) -> bool {
        unimplemented!()
    }
}


pub struct ZKisoLincheck<'a, PCS: MultilinearPCS<'a>>
{
    base: SpartanLincheckBase<'a, PCS>,
    M: Vec<Coeff<PCS::Poly>>,
    wsM: RefCell<Vec<Coeff<PCS::Poly>>>,
    wsz: RefCell<Vec<Coeff<PCS::Poly>>>
}

impl<'a, PCS> ZKisoLincheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field>
{

    pub fn for_piop(piop: &'a SpartanPIOP<'a, PCS>, r1: &Coeff<PCS::Poly>,
        r2: &Coeff<PCS::Poly>, rX: Vec<Coeff<PCS::Poly>>,
        smallA: &DenseMatrixMul<'a, Zn<2>>, smallC: &DenseMatrixMul<'a, Zn<2>>) -> Self
    {
        let M = ZKisoLincheck::get_zM(&piop, r1, r2, rX, smallA, smallC);
        let base = SpartanLincheckBase::for_piop(piop);
        Self { base, M, wsM: RefCell::default(), wsz: RefCell::default() }
    }

    pub fn get_zM(piop: &SpartanPIOP<'a, PCS>, r1: &Coeff<PCS::Poly>, r2: &Coeff<PCS::Poly>,
        rX: Vec<Coeff<PCS::Poly>>,
        smallA: &DenseMatrixMul<'a, Zn<2>>, smallC: &DenseMatrixMul<'a, Zn<2>>
        ) -> Vec<Coeff<PCS::Poly>>
    {
        debug_assert!(piop.varcount_rows() == rX.len());
        let field = piop.field();
        let mut res = (0..smallA.columns()).map(|_| field.zero()).collect_vec();

        let eqevals = MultilinearBasisEvals::new(field, &rX);
        
        izip!(smallA.data().chunks_exact(smallA.columns()), smallC.data().chunks_exact(smallC.columns()), eqevals).for_each(|(Arow, Crow, eqi)|
            izip!(Arow.iter(), Crow.iter(), res.iter_mut()).for_each(|(aj, cj, rj)| {
                if Z2.is_one(aj) {
                    field.add_assign(rj, field.mul_ref_fst(r1, field.clone_el(&eqi)));
                } else if Z2.is_neg_one(aj) {
                    field.sub_assign(rj, field.mul_ref_fst(r1, field.clone_el(&eqi)));
                };
                if Z2.is_one(cj) {
                    field.add_assign(rj, field.mul_ref_fst(r2, field.clone_el(&eqi)));
                } else if Z2.is_neg_one(cj) {
                    field.sub_assign(rj, field.mul_ref_fst(r2, field.clone_el(&eqi)));
                }
            })
        );
        res
    }

    pub fn compute_start(ring: &CoeffRing<PCS::Poly>, rA: &Coeff<PCS::Poly>, rB: &Coeff<PCS::Poly>,
        rC: &Coeff<PCS::Poly>, vA: Coeff<PCS::Poly>, vB: Coeff<PCS::Poly>, vC: Coeff<PCS::Poly>)
        -> Coeff<PCS::Poly>
    {
        ring.add(ring.mul_ref_fst(rA, vA),
            ring.add(ring.mul_ref_fst(rB, vB), ring.mul_ref_fst(rC, vC)))
    }
}

impl<'a, PCS> Sumcheck<2, 2> for ZKisoLincheck<'a, PCS>
    where PCS: MultilinearPCS<'a>, CoeffRing<PCS::Poly>: RingStore<Type: Field + FiniteRing>
{
    type SCB = SpartanLincheckBase<'a, PCS>;

    fn TE() -> bool { true } // TODO: make generic const?

    fn get_base(&self) -> &Self::SCB {
        &self.base
    }

    fn get_reference(&self) -> [&[Coeff<PCS::Poly>]; 2] {
        [&self.M, &self.base.piop().get_zM()[0]]
    }

    fn get_workspace(&self) -> [&RefCell<Vec<Coeff<PCS::Poly>>>; 2] {
        [&self.wsM, &self.wsz]
    }

    fn compute_term(ring: &CoeffRing<PCS::Poly>, at: [&Coeff<PCS::Poly>; 2], _scalar: &Coeff<PCS::Poly>) -> Coeff<PCS::Poly> {
        ring.mul_ref(at[0], at[1])
    }

    fn check_eval(&self, _rX: Vec<Coeff<PCS::Poly>>) -> bool {
        unimplemented!()
    }
}


pub struct IsoProverSigmaDIM4<'a, R, const N: usize, const PP: bool, RNTT = ABDLOPRing<R, N>>
    where R: RingStore + Clone, R::Type: CanHomFrom<BigIntRingBase> + ZnRing,
          RNTT: ABDLOPRingTrait<N, BaseRing = R>
{
    piop: SpartanPIOPDefault<'a, AsField<R>>,
    sigma: LatSigmaDefault<'a, RNTT, N>,
    smallA: DenseMatrixMul<'a, Zn<2>>,
    smallC: DenseMatrixMul<'a, Zn<2>>
}

impl<'a, R, RNTT, const N: usize, const PP: bool> IsoProverSigmaDIM4<'a, R, N, PP, RNTT>
    where R: RingStore + Clone, R::Type: CanHomFrom<BigIntRingBase> + ZnRing,
          RNTT: ABDLOPRingTrait<N, BaseRing = R>
{
    pub fn new(ring_ntt: &'a RNTT, field: &'a AsField<R>,
        v: &[El<AsField<R>>], rng: FSRng) -> Self
    {
        println!("");
        println!("IsoProverSigma: Generating public parameters...");
        let (z, r1cs) = construct_r1cs_Fp::<AsField<R>, 4, PP>(field, v);

        // this counts as precomp imo
        let zA = r1cs.A.mul(&z);
        let zB = Vec::new();
        let zC = r1cs.C.mul(&z);

        let smallA = smaller_densemm(&Z2, &r1cs.A.matrix());
        let smallC = smaller_densemm(&Z2, &r1cs.C.matrix());

        let piop = SpartanPIOP::new_extra(field, z, r1cs, zA, zB, zC, None);

        // let n = 1 << 6;
        let n = 1 << 13;
        let l = (1 << piop.varcount_cols())
            + 4*(piop.varcount_rows()) + 3*(piop.varcount_cols()) + 14;

        // println!("logrows: {}", piop.varcount_rows());
        // println!("logcols: {}", piop.varcount_cols());
        println!("l: {l}");

        let m2 = (1 << 14) + (1 << 12) + n + l;
        let bnd2 = ZZbig.power_of_two(28);

        // TODO: this is slow but its precomp
        println!("IsoProverSigma:   Generating ABDLOP public parameters...");
        let abdlop = ABDLOP::random(ring_ntt, rng,
            n.div_ceil(N), Some(l.div_ceil(N) + 1), None, m2.div_ceil(N), None, bnd2);

        let gamma = (None, 13f64);
        let challbnd = ZZbig.power_of_two(128);
        let rsmode = RejSamplModes::Mode1; // TODO

        println!("IsoProverSigma:   Setting up LatSigma protocol...");
        let sigma: LatSigmaDefault<'a, RNTT, N> = LatSigma::new(abdlop, gamma, challbnd, rsmode);

        println!("IsoProverSigma: Finished generating public parameters.");
        Self { piop, sigma, smallA, smallC }
    }

    fn get_challenge(&self) -> El<AsField<R>> {
        self.sigma.get_fs().borrow_mut().challenge(self.piop.field())
    }

    pub fn proofsize(&self) -> usize {
        self.sigma.proofsize() + self.sigma.comsize()
    }

    pub fn prover_precomp(&self) {
        println!("IsoProverSigma: Started precomputation...");
        println!("IsoProverSigma:   Started ABDLOP precomputation...");
        self.sigma.abdlop().precomp();
        println!("IsoProverSigma:   Started LatSigma precomputation...");
        self.sigma.precomp();
        println!("IsoProverSigma: Finished precomputation.");
    }

    pub fn prove(&'a self) -> (ABDLOPcommitment<RNTT,N>, LatSigmaProof<RNTT,N>) {
        println!("");
        println!("IsoProverSigma: Generating proof...");

        let field = self.piop.field();
        let fieldbase = field.get_ring();
        let sigma = &self.sigma;
        let ring = sigma.ring();
        let basering = sigma.ring().base_ring();

        let numlinrel = 30;
        let mut u = Vec::<El<R>>::with_capacity(numlinrel);
        let mut Rmdata = Vec::<Vec<(usize, El<R>)>>::with_capacity(numlinrel);
        let mut curcol = 0;

        let zref = self.piop.get_zM()[0];
        assert!(zref.len() % N == 0);
        let mut m = Vec::with_capacity((sigma.abdlop().get_B().unwrap().rows()-1)*N);
        m.extend(self.to_ring_els_ref(zref.into_iter()));

        let mes = ring.to_ntt_ring_ref(&m, None);
        let (mut com, op) = sigma.abdlop().commit(&ABDLOPmessage::new(&ring, None, Some(mes)));
        curcol += zref.len();

        println!("IsoProverSigma:   Proving Spartan Rowcheck...");
        let rowcheck = ZKisoRowcheck::for_piop(&self.piop);
        let rcvc = rowcheck.get_base().varcount();
        let rcotherpoints = rowcheck.get_base().get_other_eval_points();
        let rcpoints = [&0, &1, &rcotherpoints[0], &rcotherpoints[1]];
        let mut rcchallvec = Vec::new();
        let mut sum = field.zero();
        Rmdata.push(vec![(curcol, basering.one()), (curcol+1, basering.one())]);
        u.push(basering.zero());

        (0..rcvc).for_each(|i| {
            let hdi = rowcheck.compute_round(&rcchallvec, Some(field.clone_el(&sum)));

            m.extend(self.to_ring_els_ref(hdi.get_evals()));
            let actlen = (curcol % N != 0).then(|| curcol);
            sigma.abdlop().append_commit_base(&mut com, &op, &m[curcol..], actlen);
            curcol += 4;

            let chall = self.get_challenge();

            let lagr = PolyEvals::<AsField<R>, 2>::get_lagrange_polys_at(field, &chall, &rcpoints).collect_vec();
            sum = hdi.get_evals().zip(lagr.iter()).fold(field.zero(), |acc, (e, l)|
                field.add(acc, field.mul_ref(e, l)));

            if i != rcvc - 1 {
                let tmp = [basering.neg_one(), basering.neg_one()];
                Rmdata.push(self.to_ring_els(lagr.into_iter()).chain(tmp.into_iter()).enumerate().map(|(j, el)| (curcol-4+j, el)).collect());
                u.push(basering.zero());
            }
            rcchallvec.insert(0, chall);
        });

        println!("IsoProverSigma:   Proving quadratic relation...");
        let ws = rowcheck.get_workspace();
        ws.into_iter().for_each(|wsi| {
            let mut wsimut = wsi.borrow_mut();
            evaluate_at_fromevals_inplace(field, 1, &rcchallvec[..1], &mut wsimut);
            wsimut.truncate(1);
        });

        let (mut sc, _): (Vec<_>, Vec<_>) = rowcheck.get_base().get_scalars(&rcchallvec).unzip();
        let eqtaur = sc.pop().unwrap();
        let a = [
            field.clone_el(&ws[0].borrow()[0]),
            field.mul_ref(&ws[0].borrow()[0], &ws[0].borrow()[0]),
            field.random_element(|| sigma.abdlop().rng().borrow_mut().random::<u64>()),
            field.clone_el(&ws[1].borrow()[0])
        ];

        m.extend(self.to_ring_els_ref(a.iter()));

        let actlen = (curcol % N != 0).then(|| curcol);
        sigma.abdlop().append_commit_base(&mut com, &op, &m[curcol..], actlen);
        curcol += 4;

        Rmdata.push(self.to_ring_els(PolyEvals::<AsField<R>, 2>::get_lagrange_polys_at(field, &rcchallvec[0], &rcpoints).map(|el| field.div(&el, &eqtaur))).chain([basering.zero(), basering.neg_one(), basering.zero(), basering.one()].into_iter()).enumerate().map(|(j, el)| (curcol-8+j, el)).collect());
        u.push(basering.zero());

        // TODO: put all p,q stuff in some struct?
        let q = compute_qY(field, &a);

        let y = self.get_challenge();
        let yinv = field.invert(&y).unwrap();

        let ypow = (1..=3).rev().map(|i| field.pow(field.clone_el(&yinv), i)).chain(
            (1..=6).map(|i| field.pow(field.clone_el(&y), i))).collect_vec();
        let qy = ypow.iter().zip(q.iter()).fold(field.zero(),
            |acc, (yi, qi)| field.add(acc, field.mul_ref(yi, qi)));
        let py = ypow[2..=5].iter().zip([&a[0], &a[0], &a[1], &a[2]]).fold(field.zero(),
            |acc, (ai, yi)| field.add(acc, field.mul_ref(ai, yi)));
        assert!(field.eq_el(&qy,
            &field.mul_ref_fst(&py, field.sub_ref_fst(&py, fieldbase.mul_int_ref(&ypow[1], 2))))
        );

        m.extend(self.to_ring_els_ref(q.iter()));
        let actlen = (curcol % N != 0).then(|| curcol);
        sigma.abdlop().append_commit_base(&mut com, &op, &m[curcol..], actlen);
        curcol += 9;

        Rmdata.push(self.to_ring_els(std::iter::once(field.add_ref(&ypow[2], &ypow[3]))).chain(self.to_ring_els_ref(ypow[4..=5].iter())).enumerate().map(|(j, el)| (curcol-13+j, el)).collect());
        u.push(self.to_ring_el(py));

        Rmdata.push(self.to_ring_els(ypow.into_iter()).enumerate().map(|(j, el)| (curcol-9+j, el)).collect());
        u.push(self.to_ring_el(qy));

        println!("IsoProverSigma:   Proving Spartan Lincheck...");

        let rstar1 = self.get_challenge();
        let rstar2 = self.get_challenge();

        sum = SpartanLincheck::<BaseFoldPCSDefault<AsField<R>>>::compute_start(field,
            &rstar1, &rstar2, &field.zero(),
            field.clone_el(&a[0]), field.clone_el(&a[3]), field.zero());

        let lincheck = ZKisoLincheck::for_piop(&self.piop, &rstar1, &rstar2, rcchallvec,
            &self.smallA, &self.smallC);

        let mut lcchallvec = Vec::new();
        let lcvc = lincheck.get_base().varcount();
        let lcotherpoins = lincheck.get_base().get_other_eval_points();
        let lcpoints = [&0, &1, &lcotherpoins[0]];
        
        Rmdata.push(vec![(curcol-13, self.to_ring_el(rstar1)),(curcol-10, self.to_ring_el(rstar2)),(curcol, basering.neg_one()), (curcol+1, basering.neg_one())]);
        u.push(basering.zero());

        (0..lcvc).for_each(|i| {
            let hdi = lincheck.compute_round(&lcchallvec, Some(field.clone_el(&sum)));

            m.extend(self.to_ring_els_ref(hdi.get_evals()));
            let actlen = (curcol % N != 0).then(|| curcol);
            sigma.abdlop().append_commit_base(&mut com, &op, &m[curcol..], actlen);
            curcol += 3;

            let chall = self.get_challenge();

            let lagr = PolyEvals::<AsField<R>, 1>::get_lagrange_polys_at(field, &chall, &lcpoints).collect_vec();
            sum = hdi.get_evals().zip(lagr.iter()).fold(field.zero(), |acc, (e, l)|
                field.add(acc, field.mul_ref(e, l)));

            if i != lcvc - 1 {
                let tmp = [basering.neg_one(), basering.neg_one()];
                Rmdata.push(self.to_ring_els(lagr.into_iter()).chain(tmp.into_iter()).enumerate().map(|(j, el)| (curcol-3+j, el)).collect());
                u.push(basering.zero());
            }
            lcchallvec.insert(0, chall);
        });

        // TODO: make this a sumcheck provided function?
        let ws = lincheck.get_workspace();
        ws.into_iter().for_each(|wsi| {
            let mut wsimut = wsi.borrow_mut();
            evaluate_at_fromevals_inplace(field, 1, &lcchallvec[..1], &mut wsimut);
            wsimut.truncate(1);
        });

        m.extend(self.to_ring_els_ref(std::iter::once(&ws[1].borrow()[0])));
        m.extend((0..(N - (m.len()%N))).map(|_| basering.zero()));
        let actlen = (curcol % N != 0).then(|| curcol);
        sigma.abdlop().append_commit_base(&mut com, &op, &m[curcol..], actlen);
        curcol += 1;

        Rmdata.push(self.to_ring_els(MultilinearBasisEvals::new(field, &lcchallvec)).enumerate().map(|(j, el)| (j, el)).chain([(curcol-1, basering.neg_one())]).collect());
        u.push(basering.zero());

        println!("IsoProverSigma:   Proving LatSigma ...");

        let Rm = SparseMatrixMul::new(basering,
            N*(sigma.abdlop().get_B().unwrap().rows()-1), Rmdata, "Rm");

        sigma.set_linrel(None, Some(Rm), u);

        let proof = sigma.prove(&mut com, &op,
            &ABDLOPmessage::new(ring, None, Some(sigma.abdlop().gen_m(m))));

        println!("IsoProverSigma: Finished generating proof.");
        sigma.abdlop().wipe_precomp();
        (com, proof)
    }

    pub fn verify(&'a self, com: &ABDLOPcommitment<RNTT,N>, proof: &LatSigmaProof<RNTT,N>) -> bool 
    {
        println!("");
        println!("IsoProverSigma: Verifying proof...");
        println!("IsoProverSigma:   Verifying LatSigma proof...");
        let res = self.sigma.verify(com, proof);
        println!("IsoProverSigma: Finished verifying proof.");
        res
    }

    fn to_ring_el(&self, m: El<AsField<R>>) -> El<R> {
        self.piop.field().get_ring().unwrap_element(m)
    }

    fn to_ring_els<I>(&self, m: I) -> impl Iterator<Item = El<R>>
        where I: Iterator<Item = El<AsField<R>>>
    {
        m.map(|el| self.to_ring_el(el))
    }

    fn to_ring_els_ref<'b, I>(&self, m: I) -> impl Iterator<Item = El<R>>
        where I: Iterator<Item = &'b El<AsField<R>>>, R: 'b
    {
        self.to_ring_els(m.map(|el| self.piop.field().clone_el(el)))
    }
}

//NOTE: don't feel like implementing R[X^{-1}]
fn compute_qY<F>(field: &F, a: &[El<F>]) -> [El<F>; 9]
    where F: RingStore
{
    let inthom = field.int_hom();

    let mintwoxa1 = field.mul_ref_fst(&a[0], inthom.map(-2));
    let a1sq = field.mul_ref(&a[0], &a[0]);
    let twoxa1xa2 = field.mul(field.mul_ref(&a[0], &a[1]), inthom.map(2));
    let twoxa1xa3 = field.mul(field.mul_ref(&a[0], &a[2]), inthom.map(2));

    [
        field.clone_el(&mintwoxa1),
        field.clone_el(&a1sq),
        mintwoxa1, // TODO: use the fact that this is the same as first coeff
        field.sub_ref_fst(&twoxa1xa2, field.mul_ref_fst(&a[2], inthom.map(2))),
        field.add_ref_snd(a1sq, &twoxa1xa3),
        twoxa1xa2,
        field.add(field.mul_ref(&a[1], &a[1]), twoxa1xa3),
        field.mul(field.mul_ref(&a[1], &a[2]), inthom.map(2)),
        field.mul_ref(&a[2], &a[2])
    ]
}


#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::ring::RingValue;
    use proofs::commit::abdlop::{ABDLOPRingExtBase};
    use crate::parseFp;

    #[test]
    fn test_iso4D_sigma() {

        const PP: bool = true;

        // let rng = rand::rng();
        let rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();

        let (ring, field, trans) = parseFp::<4, PP>();
        const N: usize = 1 << 7;
        let abdlopring = RingValue::from(ABDLOPRingExtBase::<_, N>::new_promise_is_perfect_field(ring.clone()));
        
        let iso4d = IsoProverSigmaDIM4::<_, _, PP, _>::new(&abdlopring, &field, &trans, rng);

        use std::time::SystemTime;
        // let samples = 10;
        let samples = 1;
        let mut totalp = 0;
        let mut totalv = 0;
        for _ in 0..samples {
            iso4d.prover_precomp();
            let now = SystemTime::now();
            let (com, proof) = iso4d.prove();
            totalp += now.elapsed().unwrap().as_millis();
            let now = SystemTime::now();
            assert!(iso4d.verify(&com, &proof));
            totalv += now.elapsed().unwrap().as_millis();
        }
        println!("TEST IsoProverSigma: Prover time: {}ms", totalp/samples);
        println!("TEST IsoProverSigma: Proof size: {}KiB", iso4d.proofsize() >> (3 + 10));

        println!("TEST IsoProverSigma: Verifier time: {}ms", totalv/samples);
    }
}

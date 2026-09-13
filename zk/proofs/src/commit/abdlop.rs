use std::cell::RefCell;
use std::ops::{Deref, DerefMut};
use itertools::Itertools;

use feanor_math::seq::VectorFn;
use feanor_math::delegate::{DelegateRing, DelegateRingImplFiniteRing};
use feanor_math::homomorphism::{Homomorphism, CanHomFrom, Identity, CanIsoFromTo};
use feanor_math::integer::{BigIntRing, BigIntRingBase};
use feanor_math::ring::{ RingStore, RingBase, RingValue, RingExtension, El};
use feanor_math::rings::{
    extension::{
        extension_impl::{FreeAlgebraImpl, FreeAlgebraImplBase},
        FreeAlgebraStore
    },
    zn::{ ZnRing, ZnRingStore },
    finite::FiniteRing,
    direct_power::{DirectPowerRing, DirectPowerRingBase}
};
use feanor_math::divisibility::DivisibilityRing;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::algorithms::{
    fft::{FFTAlgorithm, cooley_tuckey::CooleyTuckeyFFT},
    unity_root::{get_prim_root_of_unity, is_prim_root_of_unity}
};

use crate::{
    FSRng,
    lattice::gen_vector_infbnd,
    util::matmul::{MatrixMul, DenseMatrixMul},
};


pub const ZZbig: BigIntRing = BigIntRing::RING;


pub struct ABDLOPRingBase<R: RingStore, const N: usize>
{
    pr: DirectPowerRing<R, N>,
    fft: CooleyTuckeyFFT<R::Type, R::Type, Identity<R>>,
}

impl<R, const N: usize> PartialEq for ABDLOPRingBase<R, N>
    where R: RingStore<Type: DivisibilityRing>
{
    fn eq(&self, other: &Self) -> bool {
        self.fft.eq(&other.fft) && self.pr.get_ring().eq(other.pr.get_ring())
    }
}

impl<R, const N: usize> DelegateRing for ABDLOPRingBase<R, N>
    where R: RingStore<Type: DivisibilityRing>
{
    type Base = DirectPowerRingBase<R, N>;
    type Element = El<DirectPowerRing<R, N>>;
 
    fn get_delegate(&self) -> &Self::Base {
        self.pr.get_ring()
    }
 
    fn delegate_ref<'a>(&self, el: &'a Self::Element) -> &'a <Self::Base as RingBase>::Element
    { el }
 
    fn delegate_mut<'a>(&self, el: &'a mut Self::Element)
        -> &'a mut <Self::Base as RingBase>::Element { el }
 
    fn delegate(&self, el: Self::Element) -> <Self::Base as RingBase>::Element { el }

    fn rev_delegate(&self, el: <Self::Base as RingBase>::Element) -> Self::Element { el }
}

impl<R, const N: usize> DelegateRingImplFiniteRing  for ABDLOPRingBase<R, N>
    where R: RingStore<Type: DivisibilityRing>
{}

impl<R, const N: usize> ABDLOPRingBase<R, N>
    where R: RingStore<Type: DivisibilityRing> + Clone
{
    pub fn new(basering: R, root: El<R>) -> Self {
        assert!(N.is_power_of_two());
        assert!(is_prim_root_of_unity(&basering, &root, N));

        let fft = CooleyTuckeyFFT::new(basering.clone(), root, N.ilog2() as usize);
        let pr = DirectPowerRing::new(basering);

        Self { pr, fft }
    }
}

impl<R, const N: usize> ABDLOPRingBase<R, N>
    where R: RingStore<Type: ZnRing> + Clone
{
    pub fn new_promise_is_perfect_field(basering: R) -> Self {

        let field = basering.clone().as_field().ok().expect("Provided ring is not a field");
        let root = get_prim_root_of_unity(&field, N)
            .expect(format!("Field does not have {}th primitive root of unity", N).as_str());
        Self::new(basering, field.get_ring().unwrap_element(root))
    }
}

pub type ABDLOPRing<R, const N: usize> = RingValue<ABDLOPRingBase<R,N>>;


type ExtRb<R> = FreeAlgebraImplBase<R, [El<R>; 2]>;
type ExtR<R> = RingValue<ExtRb<R>>;

pub struct ABDLOPRingExtBase<R: RingStore, const N: usize>
    where R: RingStore, ExtRb<R>: DivisibilityRing
{
    pr: DirectPowerRing<ExtR<R>, N>,
    fft: CooleyTuckeyFFT<ExtRb<R>, ExtRb<R>, Identity<ExtR<R>>>,
}

impl<R, const N: usize> PartialEq for ABDLOPRingExtBase<R, N>
    where R: RingStore, ExtRb<R>: DivisibilityRing
{
    fn eq(&self, other: &Self) -> bool {
        self.fft.eq(&other.fft) && self.pr.get_ring().eq(other.pr.get_ring())
    }
}

impl<R, const N: usize> DelegateRing for ABDLOPRingExtBase<R, N>
    where R: RingStore, ExtRb<R>: DivisibilityRing
{
    type Base = DirectPowerRingBase<ExtR<R>, N>;
    type Element = El<DirectPowerRing<ExtR<R>, N>>;
 
    fn get_delegate(&self) -> &Self::Base {
        self.pr.get_ring()
    }
 
    fn delegate_ref<'a>(&self, el: &'a Self::Element) -> &'a <Self::Base as RingBase>::Element
    { el }
 
    fn delegate_mut<'a>(&self, el: &'a mut Self::Element)
        -> &'a mut <Self::Base as RingBase>::Element { el }
 
    fn delegate(&self, el: Self::Element) -> <Self::Base as RingBase>::Element { el }

    fn rev_delegate(&self, el: <Self::Base as RingBase>::Element) -> Self::Element { el }
}

impl<R, const N: usize> DelegateRingImplFiniteRing  for ABDLOPRingExtBase<R, N>
    where R: RingStore, ExtRb<R>: DivisibilityRing
{}

pub type ABDLOPRingExt<R, const N: usize> = RingValue<ABDLOPRingExtBase<R,N>>;


impl<R, const N: usize> ABDLOPRingExtBase<R, N>
    where R: RingStore + Clone, ExtRb<R>: DivisibilityRing
{
    pub fn new(basering: R, root: El<ExtR<R>>) -> Self {
        assert!(N.is_power_of_two());
        let fring = FreeAlgebraImpl::new(basering.clone(), 2,
            [basering.neg_one(), basering.zero()]);
        assert!(is_prim_root_of_unity(&fring, &root, N));

        let fft = CooleyTuckeyFFT::new(fring, root, N.ilog2() as usize);
        let fring2 = FreeAlgebraImpl::new(basering.clone(), 2,
            [basering.neg_one(), basering.zero()]);
        let pr = DirectPowerRing::<_, N>::new(fring2);

        Self { pr, fft }
    }

    fn fring(&self) -> &ExtR<R> { &self.pr.get_ring().base_ring() }
}

impl<R, const N: usize> ABDLOPRingExtBase<R, N>
    where R: RingStore<Type: ZnRing + CanIsoFromTo<R::Type>> + Clone
{
    pub fn new_promise_is_perfect_field(basering: R) -> Self {
        assert!(N.is_power_of_two());

        let field = basering.clone().as_field().ok().expect("Provided ring is not a field");

        let fring = FreeAlgebraImpl::new(field.clone(), 2, [field.neg_one(), field.zero()]);
        let gf = fring.as_field().ok().unwrap();

        let root = get_prim_root_of_unity(&gf, N)
            .expect("Fp2 does not have primitive root of unity");
        let fring = FreeAlgebraImpl::new(field.clone(), 2, [field.neg_one(), field.zero()]);
        let fring2 = FreeAlgebraImpl::new(basering.clone(), 2,
            [basering.neg_one(), basering.zero()]);
        let root2 = fring2.from_canonical_basis(fring.wrt_canonical_basis(
            &gf.get_ring().unwrap_element(root)).into_iter().map(|el|
                field.get_ring().unwrap_element(el)));

        Self::new(basering, root2)
    }
}


pub trait ABDLOPRingTrait<const N: usize>: RingStore<Type: FiniteRing> {

    type BaseRing: RingStore<Type: CanHomFrom<BigIntRingBase> + ZnRing>;
    type NTTRing: RingStore<Type: DivisibilityRing>;

    fn base_ring(&self) -> &Self::BaseRing;

    fn NTT_ring(&self) -> &Self::NTTRing;
    
    fn to_NTTRing(&self, inp: El<Self::BaseRing>) -> El<Self::NTTRing>;
    fn to_NTTRing_ref(&self, inp: &El<Self::BaseRing>) -> El<Self::NTTRing> {
        self.to_NTTRing(self.base_ring().clone_el(inp))
    }
    fn to_BaseRing(&self, inp: El<Self::NTTRing>) -> El<Self::BaseRing>;
    fn to_BaseRing_ref(&self, inp: &El<Self::NTTRing>) -> El<Self::BaseRing> {
        self.to_BaseRing(self.NTT_ring().clone_el(inp))
    }

    fn NTTer(&self) -> &CooleyTuckeyFFT<<Self::NTTRing as RingStore>::Type,
        <Self::NTTRing as RingStore>::Type, Identity<Self::NTTRing>>;

    // NOTE: weird that these methods are needed
    fn to_array(inp: El<Self>) -> El<DirectPowerRing<Self::NTTRing, N>>;
    fn to_array_ref(inp: &El<Self>) -> &El<DirectPowerRing<Self::NTTRing, N>>;
    fn to_array_mut(inp: &mut El<Self>) -> &mut El<DirectPowerRing<Self::NTTRing, N>>;
    fn from_array(inp: El<DirectPowerRing<Self::NTTRing, N>>) -> El<Self>;
    fn from_array_ref(inp: &El<DirectPowerRing<Self::NTTRing, N>>) -> &El<Self>;
    fn from_array_mut(inp: &mut El<DirectPowerRing<Self::NTTRing, N>>) -> &mut El<Self>;

    fn ntt(&self, el: &mut El<Self>) {
        self.NTTer().fft(Self::to_array_mut(el), self.NTT_ring())
    }
    fn ntt_vec(&self, vec: &mut [El<Self>]) { vec.iter_mut().for_each(|el| self.ntt(el)) }

    fn intt(&self, el: &mut El<Self>) {
        self.NTTer().inv_fft(Self::to_array_mut(el), self.NTT_ring())
    }
    fn intt_vec(&self, vec: &mut [El<Self>]) { vec.iter_mut().for_each(|el| self.intt(el)) }

    fn from_constant(&self, c0: &El<Self::BaseRing>) -> El<Self> {
        Self::from_array(core::array::from_fn(|_| self.to_NTTRing_ref(c0)))
    }

    fn scalar_mul_assign_ref(&self, inp: &mut El<Self>, scalar: &El<Self::BaseRing>) {
        Self::to_array_mut(inp).iter_mut().for_each(|el|
            self.NTT_ring().mul_assign(el, self.to_NTTRing_ref(scalar)));
    }

    fn scalar_mul_ref(&self, inp: &El<Self>, scalar: &El<Self::BaseRing>) -> El<Self> {
        self.scalar_mul(self.clone_el(inp), scalar)
    }

    fn scalar_mul(&self, inp: El<Self>, scalar: &El<Self::BaseRing>) -> El<Self> {
        Self::from_array(Self::to_array(inp).map(|el|
            self.NTT_ring().mul(el, self.to_NTTRing_ref(scalar)))) }

    fn to_ntt_ring_ref(&self, inp: &[El<Self::BaseRing>], prefixlen: Option<usize>)
        -> Vec<El<Self>>
    {
        assert!(prefixlen.is_none_or(|x| x < N));
        let tmp = prefixlen.unwrap_or(0);
        self.to_ntt_ring(
            (0..tmp).map(|_| self.base_ring().zero())
            .chain(inp.iter().map(|el| self.base_ring().clone_el(el)))
            .chain(((inp.len() + tmp)..(inp.len() + tmp).next_multiple_of(N))
                .map(|_| self.base_ring().zero()))
        )
    }

    fn to_ntt_ring(&self, inp: impl Iterator<Item = El<Self::BaseRing>>) -> Vec<El<Self>>
    {
        // assert!(inp.len() % N == 0);
        inp.map(|el| self.to_NTTRing(el)).collect_vec()
            .into_chunks::<N>().into_iter().map(|el| Self::from_array(el)).collect_vec()
    }

    fn to_base_ring_ref(&self, inp: &[El<Self>]) -> Vec<El<Self::BaseRing>>
    {
        self.to_base_ring(inp.iter().map(|el| self.clone_el(el)))
    }

    fn to_base_ring(&self, inp: impl Iterator<Item = El<Self>>) -> Vec<El<Self::BaseRing>>
    {
        inp.flat_map(|el| Self::to_array(el)).map(|el| self.to_BaseRing(el)).collect()
    }
}

impl<R, const N: usize> ABDLOPRingTrait<N> for ABDLOPRing<R, N>
    where R: RingStore<Type: ZnRing + CanHomFrom<BigIntRingBase>>
{
    type BaseRing = R;
    type NTTRing = R;

    fn base_ring(&self) -> &Self::BaseRing { self.get_ring().base_ring() }

    fn NTT_ring(&self) -> &Self::NTTRing { self.base_ring() }

    fn to_NTTRing(&self, inp: El<Self::BaseRing>) -> El<Self::NTTRing> { inp }

    fn to_BaseRing(&self, inp: El<Self::NTTRing>) -> El<Self::BaseRing> { inp }

    fn NTTer(&self) -> &CooleyTuckeyFFT<R::Type, R::Type, Identity<R>>
    { &self.get_ring().fft }

    fn to_array(inp: El<Self>) -> El<DirectPowerRing<Self::NTTRing, N>> { inp }
    fn to_array_ref(inp: &El<Self>) -> &El<DirectPowerRing<Self::NTTRing, N>> { inp }
    fn to_array_mut(inp: &mut El<Self>) -> &mut El<DirectPowerRing<Self::NTTRing, N>> { inp }
    fn from_array(inp: El<DirectPowerRing<Self::NTTRing, N>>) -> El<Self> { inp }
    fn from_array_ref(inp: &El<DirectPowerRing<Self::NTTRing, N>>) -> &El<Self> { inp }
    fn from_array_mut(inp: &mut El<DirectPowerRing<Self::NTTRing, N>>) -> &mut El<Self> { inp }
}

impl<R, const N: usize> ABDLOPRingTrait<N> for ABDLOPRingExt<R, N>
    where R: RingStore<Type: ZnRing + CanHomFrom<BigIntRingBase>> + Clone
{
    type BaseRing = R;
    type NTTRing = ExtR<R>;

    fn base_ring(&self) -> &Self::BaseRing { self.get_ring().base_ring().get_ring().base_ring() }

    fn NTT_ring(&self) -> &Self::NTTRing { self.get_ring().base_ring() }

    fn to_NTTRing(&self, inp: El<Self::BaseRing>) -> El<Self::NTTRing> {
        self.get_ring().fring().from_canonical_basis([inp, self.base_ring().zero()])
    }

    fn to_BaseRing(&self, inp: El<Self::NTTRing>) -> El<Self::BaseRing> {
        self.get_ring().fring().wrt_canonical_basis(&inp).at(0)
    }

    fn NTTer(&self) -> &CooleyTuckeyFFT<<Self::NTTRing as RingStore>::Type,
        <Self::NTTRing as RingStore>::Type, Identity<Self::NTTRing>>
    { &self.get_ring().fft }

    fn to_array(inp: El<Self>) -> El<DirectPowerRing<Self::NTTRing, N>> { inp }
    fn to_array_ref(inp: &El<Self>) -> &El<DirectPowerRing<Self::NTTRing, N>> { inp }
    fn to_array_mut(inp: &mut El<Self>) -> &mut El<DirectPowerRing<Self::NTTRing, N>> { inp }
    fn from_array(inp: El<DirectPowerRing<Self::NTTRing, N>>) -> El<Self> { inp }
    fn from_array_ref(inp: &El<DirectPowerRing<Self::NTTRing, N>>) -> &El<Self> { inp }
    fn from_array_mut(inp: &mut El<DirectPowerRing<Self::NTTRing, N>>) -> &mut El<Self> { inp }
}


pub struct ABDLOPcommitment<R, const N: usize>
    where R: ABDLOPRingTrait<N>
{
    // NOTE: always assumed to be in coeff form
    t: Vec<El<R>>
}

impl<R, const N: usize> Deref for ABDLOPcommitment<R, N>
    where R: ABDLOPRingTrait<N>
{
    type Target = Vec<El<R>>;

    fn deref(&self) -> &Self::Target { &self.t }
}

impl<R, const N: usize> DerefMut for ABDLOPcommitment<R, N>
    where R: ABDLOPRingTrait<N>
{
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.t }
}


pub struct ABDLOPmessage<R, const N: usize>
    where R: ABDLOPRingTrait<N>
{
    // NOTE: assumed to be in NTT form
    s1: Option<Vec<El<R>>>,
    // NOTE: assumed to be in coeff form
    m: Option<Vec<El<R>>>
}

impl<'a, R, const N: usize> ABDLOPmessage<R, N>
    where R: ABDLOPRingTrait<N>
{
    // NOTE: both inputs assumed to be in coefficient form
    pub fn new(ring: &R, mut s1: Option<Vec<El<R>>>, m: Option<Vec<El<R>>>) -> Self
        where R: ABDLOPRingTrait<N>
    {
        assert!(s1.is_some() || m.is_some());
        s1.as_mut().map(|x| ring.ntt_vec(x));
        Self { s1, m }
    }

    pub fn s1(&self) -> &Option<Vec<El<R>>> { &self.s1 }

    pub fn m(&self) -> &Option<Vec<El<R>>> { &self.m }

    // NOTE: m is assumed to be in coeff form
    pub fn append_m(&mut self, app: Vec<El<R>>) {
        self.m.as_mut().map(|x| x.extend(app));
    }
}


pub struct ABDLOPopening<R, const N: usize>
    where R: ABDLOPRingTrait<N>
{
    // NOTE: always assumed to be in NTT form
    s2: Vec<El<R>>
}

impl<R, const N: usize> Deref for ABDLOPopening<R, N>
    where R: ABDLOPRingTrait<N>
{
    type Target = Vec<El<R>>;

    fn deref(&self) -> &Self::Target { &self.s2 }
}


#[derive(Clone, Copy)]
pub enum ABDLOPparts { Ajtai, BDLOP }


struct ABDLOPprecomp<R, const N: usize>
    where R: ABDLOPRingTrait<N>
{
    // NOTE: assumed to be in NTT form
    s2: RefCell<ABDLOPopening<R,N>>,
    // NOTE: assumed to be in coeff form
    A2s2: RefCell<Vec<El<R>>>,
    Bs2: Option<Vec<El<R>>>
}

impl<R, const N: usize> ABDLOPprecomp<R,N>
    where R: ABDLOPRingTrait<N>
{
    fn empty() -> Self {
        Self {
            s2: RefCell::new(ABDLOPopening{s2: Vec::new() }),
            A2s2: RefCell::new(Vec::new()),
            Bs2: None
        }
    }

    fn is_some_Bs2(&self) -> bool {
        self.Bs2.is_some()
    }

    fn is_some_s2(&self) -> bool {
        self.s2.borrow().len() > 0
    }

    fn get_ref(&self) -> (ABDLOPopening<R,N>, Vec<El<R>>, &Option<Vec<El<R>>>)
    {
        assert!(self.is_some_s2());
        let s2 = self.s2.replace(ABDLOPopening{s2: Vec::new() });
        let A2s2 = self.A2s2.replace(Vec::new());
        (s2, A2s2, &self.Bs2)
    }
}


pub struct ABDLOP<'a, R, const N: usize>
    where R: ABDLOPRingTrait<N>
{
    ring: &'a R,
    // TODO: is there is noticable difference in performance when using RefCell for the RNG?
    rng: RefCell<FSRng>,
    bnd1: Option<El<BigIntRing>>, // TODO: add possibility for 2norm bounds
    bnd2: El<BigIntRing>,
    A1: Option<DenseMatrixMul<'a, R>>, // NOTE: matrix elements stored in NTT form
    A2: DenseMatrixMul<'a, R>,
    B: Option<DenseMatrixMul<'a, R>>,
    precomp: RefCell<ABDLOPprecomp<R,N>>
}

impl<'a, R, const N: usize> ABDLOP<'a, R, N>
    where R: ABDLOPRingTrait<N>
{
    pub fn random(ring: &'a R, mut rng: FSRng,
        n: usize, l: Option<usize>, m1: Option<usize>, m2: usize,
        bnd1: Option<El<BigIntRing>>, bnd2: El<BigIntRing>) -> Self
    {
        // TODO: doing way to much in the extension field, should just keep everything in basefield
        // and only switch to extension right before NTTs
        let A1 = if bnd1.is_none() { None }
            else { Some(DenseMatrixMul::random(ring, &mut rng, n, m1.unwrap(), "ABDLOP_A1")) };
        let A2 = DenseMatrixMul::random(ring, &mut rng, n, m2, "ABDLOP_A2");
        let B = if let Some(l) = l {
            Some(DenseMatrixMul::random(ring, &mut rng, l, m2, "ABDLOP_B")) } else { None };
        let precomp = RefCell::new(ABDLOPprecomp::empty());
        Self { ring, rng: RefCell::new(rng), bnd1, bnd2, A1, A2, B, precomp }
    }
}

impl<'a, R, const N: usize> ABDLOP<'a, R, N>
    where R: ABDLOPRingTrait<N>
{
    pub fn ring(&self) -> &R { self.ring }

    pub fn rng(&self) -> &RefCell<FSRng> { &self.rng }

    pub fn has_ajtai(&self) -> bool { self.A1.is_some() }

    pub fn has_bdlop(&self) -> bool { self.B.is_some() }

    pub fn get_m1(&self) -> Option<usize> { self.A1.as_ref().map(|x| x.columns()) }

    pub fn get_m2(&self) -> usize { self.A2.columns() }

    pub fn get_bnd1(&self) -> Option<&El<BigIntRing>> { self.bnd1.as_ref() }

    pub fn get_bnd2(&self) -> &El<BigIntRing> { &self.bnd2 }

    pub fn get_A1(&self) -> Option<&DenseMatrixMul<'a, R>> { self.A1.as_ref() }

    pub fn get_A2(&self) -> &DenseMatrixMul<'a, R> { &self.A2 }

    pub fn get_B(&self) -> Option<&DenseMatrixMul<'a, R>> { self.B.as_ref() }

    pub fn comlen(&self) -> usize { self.A2.rows() + self.get_B().map_or(0, |x| x.rows()) }

    pub fn gen_m(&self, inp: Vec<El<<R as ABDLOPRingTrait<N>>::BaseRing>>) -> Vec<El<R>> {
        if !(inp.len() % N == 0) {
            panic!("Input to ABDLOP::gen_m must have length divisible by N");
        }
        self.ring().to_ntt_ring(inp.into_iter())
    }

    pub fn gen_s1(&self, inp: Vec<El<<R as ABDLOPRingTrait<N>>::BaseRing>>) -> Vec<El<R>> {
        if !(inp.len() % N == 0) {
            panic!("Input to ABDLOP::gen_s1 must have length divisible by N");
        }
        let res = self.ring().to_ntt_ring(inp.into_iter());
        if !self.check_inf_norm::<false>(&res, self.bnd1.as_ref().unwrap()) {
            panic!("Input to ABDLOP::gen_s1 must be bounded by ABDLOP::get_bnd1");
        }
        res
    }

    pub fn precomp(&self) {
        let s2 = ABDLOPopening{ s2: self.gen_s2() };
        let mut A2s2 = self.A2.mul(&s2);
        self.ring().intt_vec(&mut A2s2);
        let mut Bs2 = self.B.as_ref().map(|x| x.mul(&s2));
        if let Some(Bs2coeffmut) = Bs2.as_mut() {
            self.ring().intt_vec(Bs2coeffmut);
        }
        self.precomp.replace(ABDLOPprecomp{ s2: RefCell::new(s2), A2s2: RefCell::new(A2s2), Bs2 });
    }

    pub fn wipe_precomp(&self) {
        self.precomp.replace(ABDLOPprecomp::empty());
    }

    fn commit_precomp(&self, mes: &ABDLOPmessage<R,N>)
        -> (ABDLOPcommitment<R,N>, ABDLOPopening<R,N>)
    {
        let precomp = self.precomp.borrow();
        if !precomp.is_some_s2() {
            panic!("Call ABDLOP::precomp before calling ABDLOP::commit_precomp!");
        }
        let (s2, A2s2, Bs2) = precomp.get_ref();

        let mut t = Vec::with_capacity(self.comlen());
        if let Some(A1) = self.get_A1() {
            let mut A1s1 = A1.mul(mes.s1().as_ref().unwrap());
            self.ring().intt_vec(&mut A1s1);
            t.extend(A1s1.into_iter().zip(A2s2.into_iter()).map(|(l, r)| self.ring.add(l, r)))
        } else { t.extend(A2s2) };

        if let Some(m) = mes.m.as_ref() {
            t.extend(Bs2.as_ref().unwrap().into_iter().zip(m).map(|(l,r)| self.ring.add_ref(l,r)))
        }
        (ABDLOPcommitment{ t }, s2)
    }

    // inputs and output is in NTT form
    fn commit_ajtai(&'a self, s1opt: Option<&'a Vec<El<R>>>, s2: &'a [El<R>])
        -> Box<dyn Iterator<Item = El<R>> + 'a>
    {
        let s2iter = self.A2.mulit(s2);
        if let Some(s1) = s1opt {
            Box::new(self.get_A1().unwrap().mulit(s1).zip(s2iter).map(|(l, r)| self.ring.add(l, r)))
        } else { Box::new(s2iter) }
    }

    // s2 is in NTT form, m and output are in coeff form
    fn commit_bdlop(&self, m: &[El<R>], s2: &[El<R>], offset: Option<usize>)
        -> impl Iterator<Item = El<R>>
    {
        assert!(self.has_bdlop());
        let B = self.get_B().unwrap();
        assert!(B.rows() >= m.len());
        let ofs = offset.unwrap_or(0);
        let mut Bs2 = B.submatmul(ofs..(ofs+m.len()), 0..B.columns(), s2).collect_vec();
        self.ring().intt_vec(&mut Bs2);
        Bs2.into_iter().zip(m).map(|(l, r)| self.ring.add_ref_snd(l, r))
    }

    fn gen_s2(&self) -> Vec<El<R>> {
        let mut rngmut = self.rng.borrow_mut();
        let mut s2 = self.ring().to_ntt_ring(gen_vector_infbnd(self.ring().base_ring(),
            &mut rngmut, &self.bnd2, self.A2.columns()*N).into_iter());
        self.ring().ntt_vec(&mut s2);
        s2
    }

    pub fn commit(&self, mes: &ABDLOPmessage<R,N>) -> (ABDLOPcommitment<R,N>, ABDLOPopening<R,N>)
    {
        assert!(!self.has_ajtai() || mes.s1.is_some());

        if self.precomp.borrow().is_some_s2() {
            return self.commit_precomp(mes)
        } else {
            println!("ABDLOP: call precomp first for faster committing!");
        }

        let s2 = self.gen_s2();
        let mut t = Vec::with_capacity(self.comlen());
        t.extend(self.commit_ajtai(mes.s1().as_ref(), &s2));
        self.ring().intt_vec(&mut t);
        if let Some(m) = &mes.m {
            t.extend(self.commit_bdlop(m, &s2, None));
        }
        (ABDLOPcommitment{ t }, ABDLOPopening{ s2 })
    }

    fn check_inf_norm<const INTT: bool>(&self, inp: &[El<R>], bnd: &El<BigIntRing>) -> bool {
        let basering = self.ring().base_ring();
        let intring = basering.integer_ring();
        let hom = intring.can_hom(&ZZbig).unwrap();
        let bnd = hom.map_ref(bnd);
       
        inp.into_iter().all(|el| {
            let mut tmp = self.ring().clone_el(el);
            if INTT {self.ring().intt(&mut tmp)};
            R::to_array(tmp).into_iter().all(|ell|
                intring.is_leq(&basering.smallest_lift(self.ring().to_BaseRing(ell)), &bnd)
            )
        })
    }

    pub fn open(&self, com: &ABDLOPcommitment<R,N>,
        mes: &ABDLOPmessage<R,N>, op: &ABDLOPopening<R,N>) -> bool
    {
        let c1 = mes.s1.as_ref().is_none_or(|x| {
            self.check_inf_norm::<true>(&x, self.bnd1.as_ref().unwrap())
        });
        let c2 = self.check_inf_norm::<true>(op, &self.bnd2);
        if !(c1 && c2 && com.len() <= self.comlen()) { return false };

        let mut ajtai = self.commit_ajtai(mes.s1().as_ref(), op).collect_vec();
        self.ring().intt_vec(&mut ajtai);
        
        if let Some(m) = mes.m.as_ref() {
            ajtai.extend(self.commit_bdlop(m, op, None));
        }

        ajtai.into_iter().zip(com.iter()).all(|(l, r)| self.ring.eq_el(&l, r))
    }

    // m and output are assumed to be in coeff form
    fn append_commit_internal<'b>(&'b self, op: &'b ABDLOPopening<R,N>, m: &'b [El<R>],
        precomp: &'b ABDLOPprecomp<R, N>, offs: usize)
        -> Box<dyn Iterator<Item = El<R>> + 'b>
    {
        if precomp.is_some_Bs2() {
            Box::new(precomp.Bs2.as_ref().unwrap()[offs..offs+m.len()].iter().zip(m)
                .map(|(l,r)| self.ring.add_ref(l, r)))
        } else {
            println!("ABDLOP: call precomp first for faster committing!");
            Box::new(self.commit_bdlop(&m, op, Some(offs)))
        }
    }

    // NOTE: m is assumed to be in coeff form
    pub fn append_commit(&self, com: &mut ABDLOPcommitment<R,N>, op: &ABDLOPopening<R,N>,
        m: &[El<R>])
    {
        let comlen = com.len();
        let n = self.A2.rows();
        assert!(comlen >= n);
        assert!(self.has_bdlop());

        assert!(self.comlen() >= comlen + m.len());

        let offs = comlen - n;

        let precomp = self.precomp.borrow();
        com.extend(self.append_commit_internal(op, m, &precomp, offs));
    }

    // NOTE: mb elements are assumed to be coefficients 
    pub fn append_commit_base(&self, com: &mut ABDLOPcommitment<R,N>, op: &ABDLOPopening<R,N>,
        mb: &[El<<R as ABDLOPRingTrait<N>>::BaseRing>], actlen: Option<usize>)
    {
        let comlen = com.len();
        let n = self.A2.rows();
        assert!(comlen >= n);
        assert!(self.has_bdlop());

        assert!(actlen.is_none_or(|x| x < (comlen-n)*N && x >= (comlen-n-1)*N ));
        assert!(self.comlen()*N >= n*N + mb.len() + actlen.unwrap_or(0));

        let m = self.ring().to_ntt_ring_ref(mb, actlen.map(|x| x % N));

        let offs = actlen.map_or(comlen - n, |x| x/N);

        let precomp = self.precomp.borrow();
        let mut newcom = self.append_commit_internal(op, &m, &precomp, offs);

        // NOTE: deal with previous partial commitment
        if let Some(actlen) = actlen {
            let mut first = newcom.next().unwrap();
            R::to_array_mut(&mut first)[..(actlen % N)].iter_mut()
                .for_each(|el| *el = self.ring().NTT_ring().zero());
            self.ring().add_assign_ref(&mut com[comlen-1], &first);
        }

        com.extend(newcom);

        // NOTE: prevent partial leakage of Bs2 mask in the clear
        let totlen = actlen.unwrap_or(0) + mb.len();
        if totlen % N != 0 {
            let comlen = com.len();
            let tmp = &mut com[comlen-1];
            R::to_array_mut(tmp)[(totlen % N)..].iter_mut().for_each(|el|
                *el = self.ring().NTT_ring().zero());
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::zn::zn_big::Zn;
    use feanor_math::integer::IntegerRing;

    use crate::util::gen_random;

    #[test]
    fn test_abdlop_ring() {

        let ring = feanor_math::rings::zn::zn_64::Zn::new(65537);

        const N: usize = 1 << 12;
        let abdlopring = RingValue::from(ABDLOPRingBase::<_, N>::new_promise_is_perfect_field(ring.clone()));

        let n = 2;
        let l = 2;
        let m2 = 1;

        let inthom = ZZbig.int_hom();
        let bnd2 = inthom.map(1 << 10);

        // let m1 = None;
        // let s1 = None;
        // let bnd1 = None;
        let m1 = Some(1);
        let bnd1 = Some(inthom.map(1 << 10));

        // let rng = rand::rng();
        let rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();
        let abdlop = ABDLOP::random(&abdlopring, rng, n, Some(l), m1, m2, bnd1, bnd2);

        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();
        let s1 = abdlop.gen_s1(gen_vector_infbnd(&ring, &mut rng,
                abdlop.get_bnd1().as_ref().unwrap(), m2*N));
        let m = abdlop.gen_m(gen_random(&ring, &mut rng, l*N));

        abdlop.precomp();

        let mes = ABDLOPmessage::new(&abdlopring, Some(s1), Some(m));
        let now = std::time::SystemTime::now();
        let (com, op) = abdlop.commit(&mes);
        println!("TEST commit time: {}ms", now.elapsed().unwrap().as_millis());

        assert!(abdlop.open(&com, &mes, &op));
    }

    #[test]
    fn test_abdlop_append() {

        let ring = feanor_math::rings::zn::zn_64::Zn::new(65537);

        const N: usize = 1 << 12;
        let abdlopring = RingValue::from(ABDLOPRingBase::<_, N>::new_promise_is_perfect_field(ring.clone()));

        let n = 2;
        let l = 3;
        let m2 = 1;

        let inthom = ZZbig.int_hom();
        let bnd2 = inthom.map(1 << 10);

        // let m1 = None;
        // let s1 = None;
        // let bnd1 = None;
        let m1 = Some(1);
        let bnd1 = Some(inthom.map(1 << 10));

        // let rng = rand::rng();
        let rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();
        let abdlop = ABDLOP::random(&abdlopring, rng, n, Some(l), m1, m2, bnd1, bnd2);

        abdlop.precomp();

        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();
        let s1 = abdlop.gen_s1(gen_vector_infbnd(&ring, &mut rng,
                abdlop.get_bnd1().as_ref().unwrap(), m2*N));
        let m = abdlop.gen_m(gen_random(&ring, &mut rng, N));
        let mut mes = ABDLOPmessage::new(&abdlopring, Some(s1), Some(m));
        let (mut com, op) = abdlop.commit(&mes);

        let mut mext = gen_random(&ring, &mut rng, N - 15);
        abdlop.append_commit_base(&mut com, &op, &mext, None);

        let mext2 = gen_random(&ring, &mut rng, N + 10);
        abdlop.append_commit_base(&mut com, &op, &mext2, Some(2*N - 15));

        let mext3 = gen_random(&ring, &mut rng, 5);
        abdlop.append_commit_base(&mut com, &op, &mext3, Some(l*N - 5));

        mext.extend(mext2);
        mext.extend(mext3);
        let tmp = abdlop.gen_m(mext);
        mes.append_m(tmp);

        assert!(abdlop.open(&com, &mes, &op));
    }

    #[test]
    fn test_abdlop_ext() {

        let p = ZZbig.get_ring().parse("864175120484581453683482079962486176185193500155369104423588921177379322250834082489183304374038697487834084609675858746433355728113743766078731283595263", 10).unwrap();
        let ring = Zn::new(ZZbig, p);
        const N: usize = 1 << 8;
        let abdlopring = RingValue::from(ABDLOPRingExtBase::<_, N>::new_promise_is_perfect_field(ring.clone()));

        let n = 2;
        let l = 2;
        let m2 = 1;

        let inthom = ZZbig.int_hom();
        let bnd2 = inthom.map(1 << 10);

        // let m1 = None;
        // let s1 = None;
        // let bnd1 = None;
        let m1 = Some(1);
        let bnd1 = Some(inthom.map(1 << 10));

        // let rng = rand::rng();
        let rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();
        let abdlop = ABDLOP::random(&abdlopring, rng, n, Some(l), m1, m2, bnd1, bnd2);


        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();
        let s1 = abdlop.gen_s1(gen_vector_infbnd(&ring, &mut rng,
                abdlop.get_bnd1().as_ref().unwrap(), m2*N));
        let m = abdlop.gen_m(gen_random(&ring, &mut rng, l*N));

        abdlop.precomp();

        let mes = ABDLOPmessage::new(&abdlopring, Some(s1), Some(m));
        let now = std::time::SystemTime::now();
        let (com, op) = abdlop.commit(&mes);
        println!("TEST commit time: {}ms", now.elapsed().unwrap().as_millis());

        assert!(abdlop.open(&com, &mes, &op));
    }
}


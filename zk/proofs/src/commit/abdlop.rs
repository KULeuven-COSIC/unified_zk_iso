use std::cell::RefCell;
use std::ops::{Deref, DerefMut};

use feanor_math::homomorphism::{Homomorphism, CanHomFrom};
use feanor_math::integer::{BigIntRing, BigIntRingBase};
use feanor_math::ring::{ RingStore, El };
use feanor_math::rings::{
    zn::{ ZnRing, ZnRingStore },
    finite::FiniteRing
};
use feanor_math::ordered::OrderedRingStore;

use crate::{
    FSRng,
    lattice::gen_vector_infbnd,
    util::matmul::{MatrixMul, DenseMatrixMul},
};


pub const ZZbig: BigIntRing = BigIntRing::RING;


pub struct ABDLOPcommitment<R>
    where R: RingStore
{
    t: Vec<El<R>>
}

impl<R: RingStore> Deref for ABDLOPcommitment<R> {
    type Target = Vec<El<R>>;
    fn deref(&self) -> &Self::Target { &self.t }
}

impl<R: RingStore> DerefMut for ABDLOPcommitment<R> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.t }
}


pub struct ABDLOPmessage<'a, R>
    where R: RingStore
{
    s1: Option<&'a Vec<El<R>>>,
    m: Option<&'a Vec<El<R>>>
}

impl<'a, R: RingStore> ABDLOPmessage<'a, R> {
    pub fn new(s1: &'a Option<Vec<El<R>>>, m: &'a Option<Vec<El<R>>>) -> Self {
        assert!(s1.is_some() || m.is_some());
        Self { s1: s1.as_ref(), m: m.as_ref() }
    }

    // TODO: use ABDLOPparts here?
    pub fn s1(&self) -> Option<&'a Vec<El<R>>> { self.s1 }

    pub fn m(&self) -> Option<&'a Vec<El<R>>> { self.m }
}


pub struct ABDLOPopening<R>
    where R: RingStore
{
    s2: Vec<El<R>>
}

impl<R: RingStore> Deref for ABDLOPopening<R> {
    type Target = Vec<El<R>>;

    fn deref(&self) -> &Self::Target { &self.s2 }
}

#[derive(Clone, Copy)]
pub enum ABDLOPparts {
    Ajtai,
    BDLOP
}


struct ABDLOPprecomp<R>
    where R: RingStore
{
    s2: RefCell<Vec<El<R>>>,
    A2s2: RefCell<Vec<El<R>>>,
    Bs2: Option<Vec<El<R>>>
}

impl<R: RingStore> ABDLOPprecomp<R> {
    fn empty() -> Self {
        Self { s2: RefCell::new(Vec::new()), A2s2: RefCell::new(Vec::new()), Bs2: None }
    }

    fn is_some(&self) -> bool {
        self.A2s2.borrow().len() > 0
    }

    fn into_inner(&self) -> (Vec<El<R>>, Vec<El<R>>, &Option<Vec<El<R>>>) {
        let s2 = self.s2.replace(Vec::new());
        let A2s2 = self.A2s2.replace(Vec::new());
        (s2, A2s2, &self.Bs2)
    }
}


pub struct ABDLOP<'a, R>
    where R: RingStore
{
    ring: &'a R,
    // TODO: is there is noticable difference in performance when using RefCell for the RNG?
    rng: RefCell<FSRng>,
    bnd1: Option<El<BigIntRing>>, // TODO: add possibility for 2norm bounds
    bnd2: El<BigIntRing>,
    A1: Option<DenseMatrixMul<'a, R>>,
    A2: DenseMatrixMul<'a, R>,
    B: Option<DenseMatrixMul<'a, R>>,
    precomp: RefCell<ABDLOPprecomp<R>>
}

impl<'a, R> ABDLOP<'a, R>
    where R: RingStore<Type: FiniteRing>
{
    pub fn random(ring: &'a R, mut rng: FSRng,
        n: usize, l: Option<usize>, m1: Option<usize>, m2: usize,
        bnd1: Option<El<BigIntRing>>, bnd2: El<BigIntRing>) -> Self
    {
        let A1 = if bnd1.is_none() { None }
            else { Some(DenseMatrixMul::random(ring, &mut rng, n, m1.unwrap(), "ABDLOP_A1")) };
        let A2 = DenseMatrixMul::random(ring, &mut rng, n, m2, "ABDLOP_A2");
        let B = if let Some(l) = l {
            Some(DenseMatrixMul::random(ring, &mut rng, l, m2, "ABDLOP_B")) } else { None };
        let precomp = RefCell::new(ABDLOPprecomp::empty());
        Self { ring, rng: RefCell::new(rng), bnd1, bnd2, A1, A2, B, precomp }
    }
}

impl<'a, R: RingStore> ABDLOP<'a, R>
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
}

impl<'a, R> ABDLOP<'a, R>
    // where R: RingStore<Type: FiniteRing>
    // TODO: this is not general
    where R: RingStore<Type: FiniteRing + CanHomFrom<BigIntRingBase> + ZnRing>
{
    fn commit_ajtai(&'a self, s1opt: Option<&'a Vec<El<R>>>, s2: &'a [El<R>])
        -> Box<dyn Iterator<Item = El<R>> + 'a>
    {
        let s2iter = self.A2.mulit(s2);
        if let Some(s1) = s1opt {
            Box::new(self.get_A1().unwrap().mulit(s1).zip(s2iter).map(|(l, r)| self.ring.add(l, r)))
        } else { Box::new(s2iter) }
    }

    fn commit_bdlop(&self, m: &[El<R>], s2: &[El<R>], offset: Option<usize>)
        -> impl Iterator<Item = El<R>>
    {
        assert!(self.has_bdlop());
        let B = self.get_B().unwrap();
        assert!(B.rows() >= m.len());
        let ofs = offset.unwrap_or(0);
        B.submatmul(ofs..(ofs+m.len()), 0..B.columns(), s2).zip(m)
            .map(|(l, r)| self.ring.add_ref_snd(l, r))
    }

    pub fn commit(&self, mes: &ABDLOPmessage<R>) -> (ABDLOPcommitment<R>, ABDLOPopening<R>)
    {
        assert!(!self.has_ajtai() || mes.s1.is_some());

        if self.precomp.borrow().is_some() {
            return self.commit_precomp(mes)
        } else {
            println!("ABDLOP: call precomp first for faster committing!");
        }

        let mut rngmut = self.rng.borrow_mut();
        let s2 = gen_vector_infbnd(self.ring, &mut rngmut, &self.bnd2, self.A2.columns());
        let mut t = Vec::with_capacity(self.comlen());
        t.extend(self.commit_ajtai(mes.s1(), &s2));
        if let Some(m) = &mes.m {
            t.extend(self.commit_bdlop(m, &s2, None));
        }
        (ABDLOPcommitment{ t }, ABDLOPopening{ s2 })
    }

    pub fn open(&self, com: &ABDLOPcommitment<R>, mes: &ABDLOPmessage<R>, op: &ABDLOPopening<R>)
        -> bool
    {
        let intring = self.ring.integer_ring();
        let hom = intring.can_hom(&ZZbig).unwrap();
        let c1 = mes.s1.as_ref().is_none_or(|x| {
            let bnd1 = hom.map_ref(self.bnd1.as_ref().unwrap());
            x.iter().all(|el|
                intring.is_leq(&self.ring.smallest_lift(self.ring.clone_el(el)), &bnd1))
        });
        let bnd2 = hom.map_ref(&self.bnd2);
        let c2 = op.iter().all(|el|
            intring.is_leq(&self.ring.smallest_lift(self.ring.clone_el(&el)), &bnd2));
        if !(c1 && c2 && com.len() == self.comlen()) { return false };

        let mut iter: Box<dyn Iterator<Item = El<R>>> = self.commit_ajtai(mes.s1(), op);
        if let Some(m) = &mes.m {
            iter = Box::new(iter.chain(self.commit_bdlop(m, op, None)));
        }
        iter.zip(com.iter()).all(|(l, r)| self.ring.eq_el(&l, r))
    }

    pub fn append_commit(&self, com: &mut ABDLOPcommitment<R>, op: &ABDLOPopening<R>, m: &[El<R>])
    {
        assert!(self.has_bdlop());
        let comlen = com.len();
        assert!(self.A2.rows() + self.get_B().unwrap().rows() >= comlen + m.len());
        let precomp = self.precomp.borrow();
        let offs = comlen - self.A2.rows();
        if precomp.is_some() {
            com.extend(precomp.Bs2.as_ref().unwrap()[offs..offs+m.len()].iter().zip(m).map(|(l,r)|
                self.ring.add_ref(l, r)));
        } else {
            com.extend(self.commit_bdlop(m, op, Some(offs)));
        }
    }

    pub fn precomp(&self) {
        let mut rngmut = self.rng.borrow_mut();
        let s2 = gen_vector_infbnd(self.ring, &mut rngmut, &self.bnd2, self.A2.columns());
        let A2s2 = RefCell::new(self.A2.mul(&s2));
        let Bs2 = self.B.as_ref().map(|x| x.mul(&s2));
        self.precomp.replace(ABDLOPprecomp{ s2: RefCell::new(s2), A2s2, Bs2 });
    }

    fn commit_precomp(&self, mes: &ABDLOPmessage<R>) -> (ABDLOPcommitment<R>, ABDLOPopening<R>) {
        let precomp = self.precomp.borrow();
        assert!(precomp.is_some());
        let (s2, A2s2, Bs2) = precomp.into_inner();

        let mut t = Vec::with_capacity(self.comlen());
        if let Some(A1) = self.get_A1() {
            t.extend(A1.mulit(mes.s1().unwrap()).zip(A2s2.into_iter()).map(|(l, r)|
                self.ring.add(l, r)))}
        else { t.extend(A2s2) };

        if let Some(m) = mes.m {
            t.extend(Bs2.as_ref().unwrap().into_iter().zip(m).map(|(l,r)|
                self.ring.add_ref(l,r)))
        }
        (ABDLOPcommitment{ t }, ABDLOPopening{ s2 })
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    use crate::util::gen_random;

    #[test]
    fn test_abdlop() {

        let field = feanor_math::rings::zn::zn_64::Zn::new(65537).as_field().ok().unwrap();

        // let mut rng = rand::rng();
        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::from_os_rng();
        
        let n = 1 << 12;
        let l = 3000;
        let m2 = 100;

        let inthom = ZZbig.int_hom();
        let bnd2 = inthom.map(1 << 10);
        
        // let m1 = None;
        // let s1 = None;
        // let bnd1 = None;
        let m1 = Some(200);
        let bnd1_ = inthom.map(1 << 10);
        let s1 = Some(gen_vector_infbnd(&field, &mut rng, &bnd1_, m2));
        let bnd1 = Some(bnd1_);
        
        let mut m = Some(gen_random(&field, &mut rng, l-100));
        let mext = gen_random(&field, &mut rng, 100);

        let abdlop = ABDLOP::random(&field, rng, n, Some(l), m1, m2, bnd1, bnd2);
        let (mut com, op) = {
            let mes = ABDLOPmessage::new(&s1, &m);
            abdlop.commit(&mes)
        };

        abdlop.append_commit(&mut com, &op, &mext);

        m.as_mut().map(|x| x.extend(mext));
        let mes = ABDLOPmessage::new(&s1, &m);
        assert!(abdlop.open(&com, &mes, &op));
    }
}

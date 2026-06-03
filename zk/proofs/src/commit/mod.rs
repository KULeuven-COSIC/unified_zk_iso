use feanor_math::ring::{RingExtension, RingStore, El};
use feanor_math::rings::multivariate::{
    MultivariatePolyRing,
};
use crate::util::{CoeffRing, Coeff};

pub mod basefold;

pub mod abdlop;


pub trait Proof {}

pub trait Commitment {}

pub trait MultilinearPCS<'a> {

    type Poly: RingStore<Type: MultivariatePolyRing>;
    type C: Commitment;
    type P: Proof;

    fn polyring(&self) -> &Self::Poly;

    fn coeffring<'b>(&'b self) -> &'b CoeffRing<Self::Poly>
        where 'a: 'b
    {
        self.polyring().get_ring().base_ring()
    }

    fn get_challenge(&self) -> Coeff<Self::Poly>;

    fn commit(&self, poly: &[Coeff<Self::Poly>]) -> Self::C;
    
    fn open(&self, com: &Self::C, poly: &[Coeff<Self::Poly>]) -> bool;

    fn eval_slow(&self, com: &Self::C, z: &[Coeff<Self::Poly>],
        y: Coeff<Self::Poly>, poly: &El<Self::Poly>) -> Self::P;

    fn verify(&self, com: &Self::C, z: &[Coeff<Self::Poly>],
        y: Coeff<Self::Poly>, poly: &[Coeff<Self::Poly>], proof: Self::P) -> bool;

    fn eval(&'a self, com: &Self::C, z: Vec<Coeff<Self::Poly>>,
        y: Coeff<Self::Poly>, polycoeff: Option<&'a[Coeff<Self::Poly>]>,
        polyeval: Option<&'a[Coeff<Self::Poly>]>) -> Self::P;
}


use std::ops::{RangeBounds, Range, Bound};
use std::ops::Bound::{Included, Excluded};
use rand::{CryptoRng, Rng, SeedableRng, rngs::{ThreadRng, StdRng}};

use feanor_math::ring::{El, RingStore, RingExtension};
use feanor_math::rings::finite::{FiniteRingStore, FiniteRing};

pub type CoeffRing<P> = <<P as RingStore>::Type as RingExtension>::BaseRing;
pub type Coeff<P> = El<CoeffRing<P>>;


pub mod matmul;


pub fn gen_vector<EL>(mut f: impl FnMut() -> EL, len: usize) -> Vec<EL> {
    (0..len).map(|_| f()).collect()
}

pub fn gen_random<R, RNG>(ring: &R, mut rng: RNG, len: usize) -> Vec<El<R>>
    where R: RingStore<Type: FiniteRing>, RNG: Rng
{
    gen_vector::<El<R>>(|| ring.random_element(|| rng.next_u64()), len)
}

// TODO: check where we can use this instead of calling bits_from_int for all ints
pub fn bits(bitlen: usize) -> impl Iterator<Item = Vec<usize>>
{
    let mut cur = vec![1; bitlen];
    let mut cnt = 0;
    std::iter::from_fn(move || {
        let mut carry = 1;
        (0..bitlen).for_each(|i| {
            let tmp = cur[i] ^ carry;
            carry &= cur[i];
            cur[i] = tmp;
        });
        cnt += 1;
        if cnt > 1 << bitlen { None }
        else { Some(cur.clone()) }
    })
}

// outputs bits from lsb to msb
pub fn bits_from_int(inp: usize, bitlen: usize)
    -> impl ExactSizeIterator<Item = usize> + DoubleEndedIterator<Item = usize> + Clone
{
    (0..bitlen).map(move |n| (inp >> n) & 1)
}


// outputs integer from lsb to msb bits
pub fn int_from_bits<I>(bits: I) -> usize
    where I: Iterator<Item = usize>
{
    bits.enumerate().fold(0, |acc, (i, b)| if b != 0 {acc + (1 << i)} else {acc})
}


pub struct FiatShamirSim<RNG: Rng + CryptoRng> {
    rng: RNG
}

impl<RNG: Rng + CryptoRng> FiatShamirSim<RNG> {
    pub fn challenge<R: RingStore<Type: FiniteRing>>(&mut self, ring: &R) -> El<R> {
        let mut el = ring.random_element(|| self.rng.next_u64());
        while ring.is_zero(&el) {
            el = ring.random_element(|| self.rng.next_u64());
        }
        el
    }

    pub fn get_rng(&mut self) -> &mut RNG { &mut self.rng }
}

impl FiatShamirSim<StdRng> {
    fn new_rng() -> StdRng {
        StdRng::seed_from_u64(69)
    }
    pub fn new() -> Self {
        Self { rng: Self::new_rng() }
    }
    pub fn reset(&mut self) {
        self.rng = Self::new_rng()
    }
}

impl FiatShamirSim<ThreadRng> {
    fn new_rng() -> ThreadRng {
        rand::rng()
    }
    pub fn new() -> Self {
        Self { rng: Self::new_rng() }
    }
    pub fn reset(&mut self) {
        self.rng = Self::new_rng()
    }
}

// TODO: is this not possible with derive?
impl<RNG: Rng + CryptoRng + Clone> Clone for FiatShamirSim<RNG> {
    fn clone(&self) -> Self {
        Self {
            rng: self.rng.clone()
        }
    } 
}


pub fn test_rot<R: RingStore>(ring: &R, inp: &Vec<El<R>>, out: &Vec<El<R>>, by: usize) {
    assert!(inp.len() == out.len());
    assert!((0..inp.len()).all(|i| ring.eq_el(&inp[i], &out[(i+by)%out.len()])))
}


pub fn contains_range<A>(this: Range<usize>, other: &A) -> bool
    where A: RangeBounds<usize>
{
    let bound_in_range = |range: &Range<usize>, b: Bound<&usize>| -> bool {
        match b {
            Included(v) => range.contains(&v),
            Excluded(v) => range.contains(&(v-1)),
            _ => false
        }
    };
    bound_in_range(&this, other.start_bound()) && bound_in_range(&this, other.end_bound())
}


#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::rings::zn::zn_64::Zn;

    #[test]
    fn test_util_bits() {

        let N = 7;
        let int = rand::rng().random_range(0..(1 << N));
        
        assert_eq!(int_from_bits((0..N).map(|_| 0)), 0);
        assert_eq!(int_from_bits((0..N).map(|_| 1)), (1 << N) - 1);
        assert_eq!(int_from_bits(bits_from_int(int, N)), int);
        assert!(bits(N).count() == 1 << N);
        assert!(bits(N).zip(0..(1 << N)).all(|(bv, i)|
            bits_from_int(i, N).enumerate().all(|(ind, b)| bv[ind] == b)));
    }

    #[test]
    fn test_util_fiatshamirsim() {

        let N = 10;
        let field = Zn::new(65537).as_field().ok().unwrap();

        let mut fs1 = FiatShamirSim::<StdRng>::new();
        let mut fs2 = FiatShamirSim::<StdRng>::new();

        (0..N).all(|_| field.eq_el(&fs1.challenge(&field), &fs2.challenge(&field)));

        (0..N).for_each(|_| {fs1.challenge(&field);});

        let mut fs3 = fs1.clone();

        (0..N).all(|_| field.eq_el(&fs1.challenge(&field), &fs3.challenge(&field)));
    }
}

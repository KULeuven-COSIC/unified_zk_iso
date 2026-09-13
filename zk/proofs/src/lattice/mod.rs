use rand::{Rng, CryptoRng};
use rand_distr::StandardNormal;
use itertools::izip;

use feanor_math::primitive_int::StaticRing;
use feanor_math::homomorphism::{Homomorphism, CanHomFrom, CanHom};
use feanor_math::integer::{IntCast, BigIntRing, BigIntRingBase, IntegerRingStore};
use feanor_math::ring::{ RingStore, El };
use feanor_math::rings::{
    zn::{ ZnRingStore, zn_big::Zn, ZnRing },
    finite::{FiniteRing, FiniteRingStore}
};
use feanor_math::ordered::OrderedRingStore;

use crate::{
    FSRng,
    util::{gen_vector, FiatShamirSim},
    commit::abdlop::ZZbig
};


pub mod sigma;


const ZZi128: StaticRing<i128> = StaticRing::<i128>::RING;


fn gen_infbnd<R, Rb, RNG>(mut rng: RNG, Rbnd: &Rb, hom: &CanHom<&BigIntRing, &R>) -> El<R>
    where R: RingStore<Type: CanHomFrom<BigIntRingBase>>, RNG: Rng + CryptoRng,
          Rb: RingStore<Type: FiniteRing + ZnRing<IntegerRing = BigIntRing>>
{
    hom.map(Rbnd.smallest_lift(Rbnd.random_element(|| rng.next_u64())))
}

pub fn gen_vector_infbnd<R, RNG>(ring: &R, mut rng: RNG, bnd: &El<BigIntRing>, size: usize)
    -> Vec<El<R>>
    where R: RingStore<Type: CanHomFrom<BigIntRingBase>>, RNG: Rng + CryptoRng
{
    let Rbnd = Zn::new(ZZbig, ZZbig.clone_el(bnd));
    let hom = ring.can_hom(&ZZbig).unwrap();
    gen_vector::<El<R>>(|| gen_infbnd(&mut rng, &Rbnd, &hom), size)
}


pub fn gen_vector_dgauss<R, RNG>(ring: &R, mut rng: RNG, sigma: f64, size: usize)
    -> Vec<El<R>>
    where R: RingStore<Type: CanHomFrom<BigIntRingBase>>, RNG: Rng + CryptoRng
{
    let ZZi128base = ZZi128.get_ring();
    let ZZbigbase = ZZbig.get_ring();
    let hom = ring.can_hom(&ZZbig).unwrap();
    // TODO: using this method, the distribution saturates at ~2^128
    gen_vector::<El<R>>(|| hom.map(ZZbigbase.cast(ZZi128base,
        (rng.sample::<f64, _>(StandardNormal) * sigma).round() as i128)), size)
}


type IntRing<R> = <<R as RingStore>::Type as ZnRing>::IntegerRing;

pub fn inner_prod<'a, R, I>(ring: &R, intring: &IntRing<R>, left: I, right: I) -> El<IntRing<R>>
    where R: RingStore<Type: CanHomFrom<BigIntRingBase> + ZnRing>,
          I: Iterator<Item = &'a El<R>>, El<R>: 'a
{
    left.zip(right).fold(intring.zero(), |acc, (li, ri)| intring.add(acc,
        intring.mul(ring.smallest_lift(ring.clone_el(li)), ring.smallest_lift(ring.clone_el(ri)))))
}

pub fn norm2<R>(ring: &R, intring: &IntRing<R>, vec: &[El<R>]) -> f64
    where R: RingStore<Type: CanHomFrom<BigIntRingBase> + ZnRing>
{
    intring.to_float_approx(&inner_prod(ring, intring, vec.iter(), vec.iter())).sqrt()
}


#[derive(PartialEq, Clone, Copy)]
pub enum RejSamplModes {
    // Mode0, TODO
    Mode1,
    Mode2
}

pub fn rejsamplrep(gamma: f64, rsmode: RejSamplModes) -> f64 {
    (match rsmode {
        RejSamplModes::Mode1 => (14f64/gamma).exp(),
        _ => 1f64,
    }) * (2f64*gamma.powi(2)).recip().exp()
}


// TODO: implement the second version of rej sampl
pub fn gen_vector_latrejsampl<R, RNG, const N: usize>(ring: &R,
    mut rng: RNG, fs: &mut FiatShamirSim<FSRng>,
    challbnd: &El<BigIntRing>, gamma: [f64; N], sigma: [f64; N], rsmode: RejSamplModes,
    y: [&[El<R>]; N], s: [&[El<R>]; N] // TODO: take y as iterators?
) -> ([Vec<El<R>>; N], usize)
    where R: RingStore<Type: CanHomFrom<BigIntRingBase> + ZnRing>, RNG: Rng + CryptoRng
{
    let Rbnd = Zn::new(ZZbig, ZZbig.clone_el(challbnd));
    let hom = ring.can_hom(&ZZbig).unwrap();
    let intring = ring.integer_ring();
    let inthom = intring.int_hom();

    let M: [f64; N] = core::array::from_fn(|i| rejsamplrep(gamma[i], rsmode));

    let mut z: [Vec<El<R>>; N] = core::array::from_fn(|i| Vec::with_capacity(y[i].len()));
    let mut v: [Vec<El<R>>; N] = core::array::from_fn(|i| Vec::with_capacity(y[i].len()));

    let mut u = 2f64;
    let mut res1 = [0f64; N];
    let mut cnt = 0;

    while res1.iter().any(|resi| u > *resi) {
        let chall = gen_infbnd(fs.get_rng(), &Rbnd, &hom);

        (0..N).for_each(|i|
            if cnt == 0 {
                izip!(y[i].iter(), s[i].iter()).for_each(|(yij, sij)| {
                    let tmp = ring.mul_ref(sij, &chall);
                    z[i].push(ring.add_ref(yij, &tmp));
                    v[i].push(tmp);
                })
            } else {
                izip!(z[i].iter_mut(), v[i].iter_mut(), y[i].iter(), s[i].iter()).for_each(
                |(zij, vij, yij, sij)| {
                    *vij = ring.mul_ref(sij, &chall);
                    *zij = ring.add_ref(yij, vij);
                })
            }
        );

        // TODO: can we move to floats sooner?
        (0..N).for_each(|i| {
            let zinnerv = inner_prod(ring, &intring, z[i].iter(), v[i].iter());
            // TODO: fix Mode2: zinnerv is never positive for some reason, maybe just bad bnd's for
            // characteristic of ring used in tests
            if rsmode == RejSamplModes::Mode1 || !intring.is_neg(&zinnerv) {
                let vnorm2 = inner_prod(ring, &intring, v[i].iter(), v[i].iter());
                res1[i] = M[i].recip() * (intring.to_float_approx(&intring.sub(vnorm2,
                    intring.mul(inthom.map(2), zinnerv)))/(2f64 * sigma[i].powi(2))).exp();
            }
        });
        u = rng.random_range(0f64..1f64);
        cnt += 1;
    }
    (z, cnt)
}


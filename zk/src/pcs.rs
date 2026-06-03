use feanor_math::ring::{RingStore, El};
use feanor_math::rings::finite::FiniteRing;
use feanor_math::field::Field;

use proofs::{
    codes::foldablecodes::RSFoldableCode,
    commit::basefold::{BaseFoldPCS, BaseFoldSumcheckDoubleEfficient},
    multilinear::spartan::SpartanPIOP
};

use crate::{construct_r1cs_Fp, construct_r1cs_Fp2_dim2, construct_r1cs_Fp2_dim1};


pub type BaseFoldPCSDefault<'a, F> =
    BaseFoldPCS<'a, RSFoldableCode<'a, F>, BaseFoldSumcheckDoubleEfficient<'a, F>>;
pub type SpartanPIOPDefault<'a, F> = SpartanPIOP<'a, BaseFoldPCSDefault<'a, F>>;


pub struct IsoProverBaseFoldCGL<'a, F, const AsFp2: bool>
    where F: RingStore + Clone, F::Type: Field + FiniteRing,
{
    spartanpiop: SpartanPIOPDefault<'a, F>
}

impl<'a, F, const AsFp2: bool> IsoProverBaseFoldCGL<'a, F, AsFp2>
    where F: RingStore + Clone, F::Type: Field + FiniteRing
{
    pub fn new(field: &'a F, v: &[El<F>]) -> Self
    {
        let ((z, r1cs), ver_rep) = if AsFp2 {
            (construct_r1cs_Fp::<F, 2>(field, v), 445) // TODO
        } else {
            (construct_r1cs_Fp2_dim2::<F>(field, v), 470) // from basefold code 2^14
        };

        assert!(r1cs.satisfies(&z));

        Self {
            spartanpiop: SpartanPIOP::new(field, z, r1cs, ver_rep)
        }
    }

    pub fn execute(&'a self) -> bool {
        self.spartanpiop.execute()
    }
}


pub struct IsoProverBaseFold<'a, F, const DIM: usize, const AsFp2: bool>
    where F: RingStore + Clone, F::Type: Field + FiniteRing,
{
    spartanpiop: SpartanPIOPDefault<'a, F>
}

impl<'a, F, const DIM: usize, const AsFp2: bool> IsoProverBaseFold<'a, F, DIM, AsFp2>
    where F: RingStore + Clone, F::Type: Field + FiniteRing
{
    pub fn new(field: &'a F, v: &[El<F>]) -> Self
    {
        let ((z, r1cs), ver_rep) = if DIM == 4 {
            (construct_r1cs_Fp::<F, DIM>(field, v), 445) // from basefold code 2^13
        } else if DIM == 2 {
            if AsFp2 {
                (construct_r1cs_Fp::<F, DIM>(field, v), 445) // TODO
            } else {
                (construct_r1cs_Fp2_dim2::<F>(field, v), 470) // from basefold code 2^14
            }
        } else if DIM == 1 {
            if AsFp2 {
                (construct_r1cs_Fp::<F, DIM>(field, v), 445) // TODO
            } else {
                (construct_r1cs_Fp2_dim1::<F>(field, v), 422) // from basefold code 2^12
            }
        } else {
            panic!("Invalid dimension")
        };

        assert!(r1cs.satisfies(&z));

        Self {
            spartanpiop: SpartanPIOP::new(field, z, r1cs, ver_rep)
        }
    }

    pub fn execute(&'a self) -> bool {
        self.spartanpiop.execute()
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cgl_pcs() {
        
        let (_ring, field, trans) = crate::parseFp2_cgl();
        let zkiso = IsoProverBaseFoldCGL::<_, true>::new(&field, &trans);

        // let (_ring, field, trans) = crate::parseFp_cgl();
        // let zkiso = IsoProverBaseFoldCGL::<_, false>::new(&field, &trans);

        // println!("proof size: {} KiB", zkiso.spartanpiop.proofsize() >> (3 + 10));

        use std::time::SystemTime;
        let start = SystemTime::now();
        assert!(zkiso.execute());
        println!("Prover time: {}ms", start.elapsed().unwrap().as_millis());

    }

    #[test]
    fn test_iso_pcs() {

        const DIM: usize = 4;
        
        // let (_ring, field, trans) = crate::parseFp2::<DIM>();
        // let zkiso = IsoProverBaseFold::<_, DIM, true>::new(&field, &trans);

        let (_ring, field, trans) = crate::parseFp::<DIM>();
        let zkiso = IsoProverBaseFold::<_, DIM, false>::new(&field, &trans);

        println!("proof size: {} KiB", zkiso.spartanpiop.proofsize() >> (3 + 10));

        use std::time::SystemTime;
        let start = SystemTime::now();
        assert!(zkiso.execute());
        println!("Prover time: {}ms", start.elapsed().unwrap().as_millis());

        // use std::time::SystemTime;
        // let samplesize = 30;
        // let mut avg = 0f64;
        // for _i in 0..samplesize {
        //     // println!("iso4D prover started");
        //     let start = SystemTime::now();
        //     assert!(iso4d.execute());
        //     let duration = start.elapsed().unwrap().as_secs_f64();
        //     avg += duration/(samplesize as f64);
        //     // println!("iso4D prover finished in {}s", duration);
        // }
        // println!("On average this takes {}s", avg)
    }
}

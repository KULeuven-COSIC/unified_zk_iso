use tracing::instrument;

use feanor_math::matrix::OwnedMatrix;
use feanor_math::algorithms::linsolve::{LinSolveRing, LinSolveRingStore};
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::{RingStore, RingBase, El};

use crate::util::matmul::{MatrixMul, DenseMatrixMul};

pub mod foldablecodes;

pub trait LinearCode {

    type R: RingStore<Type: LinSolveRing>;
    type MM: MatrixMul<R = Self::R>;

    fn ring(&self) -> &Self::R;

    fn generator(&self) -> &Self::MM;

    fn encode(&self, input: &[El<Self::R>]) -> Vec<El<Self::R>> {
        self.generator().mul(input)
    }

    fn is_code_element(&self, input: &[El<Self::R>]) -> bool {
        let genr = self.generator();
        assert!(input.len() == genr.rows());
        let mut lhs = OwnedMatrix::from_fn(genr.rows(), genr.columns(), |i, j| self.ring().clone_el(genr.get(i, j)));
        let mut rhs = OwnedMatrix::from_fn(genr.rows(), 1, |i, _| self.ring().clone_el(&input[i]));
        let mut out = OwnedMatrix::zero(genr.columns(), 1, self.ring());
        self.ring().solve_right(lhs.data_mut(), rhs.data_mut(), out.data_mut()).is_solved()
    }

}

pub struct RScode<'a, R: RingStore<Type: LinSolveRing>> {
    ring: &'a R,
    genr: DenseMatrixMul<'a, R>,
}

impl<'a, R: RingStore<Type: LinSolveRing>> RScode<'a, R> {

    #[instrument(skip_all)]
    pub fn new(ring: &'a R, input_len: usize, output_len: usize) -> Self {
        RScode::from_domain(ring, input_len,
            (1..=output_len).map(|i| ring.get_ring().from_int(i as i32)).collect())
    }

    fn from_domain(ring: &'a R, input_len: usize, domain: Vec<El<R>>) -> Self {
        let output_len = domain.len();
        let mut data: Vec<El<R>> = Vec::with_capacity(input_len*output_len);
        (0..output_len).for_each(|i| (0..input_len).for_each(|j|
            data.push(ring.pow_gen(ring.clone_el(&domain[i]), &(j as i64), StaticRing::<i64>::RING))
        ));

        let genr = DenseMatrixMul::new(ring, input_len, data,
            format!("RS_Generator_{input_len}_{output_len}").as_str());

        Self {
            ring,
            genr
        }
    }
}

impl<'a, Rg: RingStore<Type: LinSolveRing>> Clone for RScode<'a, Rg> {
    fn clone(&self) -> Self {
        Self {
            ring: self.ring,
            genr: self.genr.clone()
        }
    }
}

impl<'a, Rg: RingStore<Type: LinSolveRing>> LinearCode for RScode<'a, Rg> {

    type R = Rg;
    type MM = DenseMatrixMul<'a, Rg>;

    fn ring(&self) -> &Rg {
        self.ring
    }

    fn generator(&self) -> &DenseMatrixMul<'a, Rg> {
        &self.genr
    }

}

#[cfg(test)]
pub mod tests {
    use super::*;
    use feanor_math::rings::field::AsField;
    use feanor_math::rings::zn::ZnRingStore;
    use feanor_math::rings::zn::zn_64::Zn;
    use feanor_math::rings::finite::FiniteRingStore;
    use crate::util::gen_vector;

    #[test]
    fn test_rscode_basics() {

        let field = Zn::new(65537).as_field().ok().unwrap();
        pub type Field = AsField<Zn>;

        let k0 = 5;
        let c = 2;

        let rscode = RScode::new(&field, k0, k0*c);

        let input = gen_vector::<El<Field>>(||
            field.random_element(rand::random::<u64>), k0);
       
        let code = rscode.encode(&input);

        assert!(rscode.is_code_element(&code));
    }

}


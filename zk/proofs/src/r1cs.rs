use itertools::{izip, Itertools};
use rand::Rng;

use feanor_math::field::{Field, FieldStore};
use feanor_math::ring::{RingStore, El};
use feanor_math::rings::finite::FiniteRing;

use crate::util::{bits_from_int, int_from_bits};
use crate::multilinear::{MultilinearBasis, MultilinearBasisEvals};

use crate::util::matmul::{MatrixMul, SparseMatrixMul};

pub struct R1CSMatrix<'a, R: RingStore> {
    rowlogsize: usize,
    mm: SparseMatrixMul<'a, R>
}

impl<'a, R: RingStore> R1CSMatrix<'a, R>
{
    pub fn new(mm: SparseMatrixMul<'a, R>) -> Self {
        assert!(mm.rows().is_power_of_two());
        assert!(mm.columns().is_power_of_two());
        Self {
             rowlogsize: mm.rows().ilog2() as usize,
             mm
        }
    }

    pub fn matrix(&self) -> &SparseMatrixMul<'a, R> {
        &self.mm
    }

    pub fn mul(&self, rhs: &[El<R>]) -> Vec<El<R>> {
        self.mm.mul(rhs)
    }

    fn mulit(&self, rhs: &[El<R>]) -> impl Iterator<Item = El<R>> {
        self.mm.mulit(rhs)
    }

    pub fn rowlogsize(&self) -> usize { self.rowlogsize }
}

impl<'a, R: RingStore<Type: Field>> R1CSMatrix<'a, R>
{
    // this is O(NlogN) since we compute each evaluation of eq from scratch
    // next algorithm is O(N) by using the streaming algorithm to compute the eq evaluations
    pub fn evaluate_rowvars_slow(&self, at: &[El<R>]) -> Vec<Vec<El<R>>> {
        let ring = self.mm.ring();
        let mut res = (0..(1 << (self.rowlogsize - at.len()))).map(|_|
            (0..self.mm.columns()).map(|_| ring.zero()).collect_vec()).collect_vec();
        let eq = MultilinearBasis::new(ring, at);
        self.mm.iter().for_each(|(i, j, el)| {
            let mut bi_first = bits_from_int(i, self.rowlogsize).collect_vec();
            let bi_last = bi_first.split_off(self.rowlogsize - at.len());
            debug_assert!(bi_last.len() == at.len());
            ring.add_assign(&mut res[int_from_bits(bi_first.into_iter())][j],
                ring.mul_ref_fst(el, eq.evaluate_athc(bi_last)))
        });
        res
    }

    // interpret as multilinear extension and evaluate at the variables that represent rows index
    pub fn evaluate_rowvars(&self, at: &[El<R>]) -> Vec<Vec<El<R>>> {
        let ring = self.mm.ring();
        let mut res = (0..(1 << (self.rowlogsize - at.len()))).map(|_|
            (0..self.mm.columns()).map(|_| ring.zero()).collect_vec()).collect_vec();
        let eqevals = MultilinearBasisEvals::new(ring, at);
        let mut rowiter = self.mm.iter_rows();
        // eqevals.zip(bits(at.len())).for_each(|(eqeval, _bi_last)|
        //     res.iter_mut().zip(bits(self.logsize - at.len())).for_each(|(rif, _bi_first)|
        //         rowiter.next().unwrap().into_iter().for_each(|(j, el)|
        //             ring.add_assign(&mut rif[*j], ring.mul_ref_fst(el, ring.clone_el(&eqeval)))
        //         )
        //     )
        // );
        eqevals.for_each(|eqeval| res.iter_mut().for_each(|rif|
            rowiter.next().unwrap().into_iter().for_each(|(j, el)|
                ring.add_assign(&mut rif[*j], ring.mul_ref_fst(el, ring.clone_el(&eqeval)))
            )
        ));
        res
    }
}

pub struct R1CS<'a, R: RingStore> {
    pub A: R1CSMatrix<'a, R>,
    pub B: R1CSMatrix<'a, R>,
    pub C: R1CSMatrix<'a, R>
}

impl<'a, R: RingStore> R1CS<'a, R>
{
    pub fn new(A: SparseMatrixMul<'a, R>, B: SparseMatrixMul<'a, R>,
        C: SparseMatrixMul<'a, R>) -> Self {
        Self {
             A: R1CSMatrix::new(A),
             B: R1CSMatrix::new(B),
             C: R1CSMatrix::new(C)
        }
    }

    pub fn satisfies(&self, z: &[El<R>]) -> bool {
        let ring = self.A.mm.ring();
        // izip!(self.A.mulit(z), self.B.mulit(z), self.C.mulit(z)).all(|(ai, bi, ci)|
        //     ring.eq_el(&ring.mul(ai, bi), &ci))
        izip!(self.A.mulit(z), self.B.mulit(z), self.C.mulit(z)).enumerate()
        .all(|(i, (ai, bi, ci))| {
            let res = ring.eq_el(&ring.mul_ref(&ai, &bi), &ci);
            if !res {
                println!("R1CS row {i} is not satisfied!");
                println!("ai: {}, bi: {}, ci: {}",
                    ring.format(&ai), ring.format(&bi), ring.format(&ci))
            };
            res
        })
    }
}

impl<'a, F> R1CS<'a, F>
    where F: RingStore<Type: Field + FiniteRing>
{
    // Generates random R1CS instances such that z is a valid transcript
    // we assume that the input vectors are ordered from lsb to msb
    pub fn random_from<RNG: Rng>(field: &'a F, mut rng: RNG, z: &[El<F>], rowlen: usize)
        -> (Self, Vec<El<F>>, Vec<El<F>>, Vec<El<F>>)
    {
        debug_assert!(!z.iter().all(|zi| field.is_zero(zi)));
        let N = z.len();
        let A = SparseMatrixMul::random(field, &mut rng, rowlen, N, 3, "A");
        let B = SparseMatrixMul::random(field, &mut rng, rowlen, N, 3, "B");
        let zA = A.mul(&z);
        let zB = B.mul(&z);
        let zC: Vec<_> = zA.iter().zip(zB.iter()).map(|(zAi, zBi)|
            field.mul_ref(zAi, zBi)).collect();
        let C = SparseMatrixMul::new(field, z.len(), zC.iter().enumerate().map(|(i, zCi)|
            if i < N && !field.is_zero(&z[i]) { vec![(i, field.div(&zCi, &z[i]))] } else {
                z.iter().enumerate().find_map(|(j, zj)|
                    (!field.is_zero(zj)).then(|| vec![(j, field.div(&zCi, &zj))])).unwrap() }
            ).collect(), "C");
        (R1CS::new(A, B, C), zA, zB, zC)
    }
}


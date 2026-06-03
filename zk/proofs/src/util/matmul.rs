use std::collections::HashSet;
use std::ops::Range;
use rand::Rng;

use feanor_math::ring::*;
use feanor_math::homomorphism::{CanHom, Homomorphism, CanHomFrom};
use feanor_math::rings::finite::{FiniteRing, FiniteRingStore};

use crate::util::{gen_random, contains_range};

pub trait MatrixMul: Clone {
    type R: RingStore;

    fn ring(&self) -> &Self::R;
    fn desc(&self) -> &String;
    fn rows(&self) -> usize;
    fn columns(&self) -> usize;
    fn get(&self, i: usize, j: usize) -> &El<Self::R>;

    // TODO: change mul to mulit where can be used
    fn mulit(&self, rhs: &[El<Self::R>]) -> impl Iterator<Item = El<Self::R>>;

    fn mul(&self, rhs: &[El<Self::R>]) -> Vec<El<Self::R>>;

    fn get_map<Rout>(&self, i: usize, j: usize, hom: &CanHom<&Self::R, &Rout>) -> El<Rout>
        where Rout: RingStore, <Rout as RingStore>::Type: CanHomFrom<<Self::R as RingStore>::Type>
    {
        hom.map_ref(self.get(i, j))
    }

    // WTH does this not work??
    fn print(&self) {
        for i in 0..self.rows() {
            for j in 0..self.columns() {
                print!("{} ", self.ring().format(self.get(i, j)));
            }
            println!();
        }
    }
}


pub struct SparseMatrixMul<'a, R: RingStore> {
    ring: &'a R,
    rows: usize,
    columns: usize,
    data: Vec<Vec<(usize, El<R>)>>,
    zero: El<R>,
    desc: String
}

impl<'a, R: RingStore> SparseMatrixMul<'a, R>
{
    pub fn new(ring: &'a R, columns: usize, data: Vec<Vec<(usize, El<R>)>>, desc: &str) -> Self {
        assert!(data.iter().all(|row| row.iter().all(|(j, _)| *j < columns)));
        assert!(data.iter().all(|row| row.iter().is_sorted_by(|(jl, _), (jr, _)| *jl < *jr)));
        Self {
            ring,
            rows: data.len(),
            columns,
            data,
            zero: ring.zero(),
            desc: desc.to_string()
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, usize, &El<R>)> {
        self.data.iter().enumerate().flat_map(|(i, row)|
            row.iter().map(move |(j, el)| (i, *j, el)))
    }

    pub fn iter_rows(&self) -> impl Iterator<Item = &Vec<(usize, El<R>)>> {
        self.data.iter()
    }

    pub fn get_data(&self) -> &Vec<Vec<(usize, El<R>)>> {
        &self.data
    }
}

// TODO: implement data structure differently so that its size does not depend on dimensions
impl<'a, R> SparseMatrixMul<'a, R>
    where R: RingStore<Type: FiniteRing>
{
    pub fn random<RNG: Rng>(ring: &'a R, mut rng: RNG,
        rows: usize, columns: usize, rowhw: usize, desc: &str) -> Self
    {
        Self {
            ring,
            rows,
            columns,
            data:   (0..rows).map(|_| {
                        let mut seen = HashSet::<usize>::new();
                        while seen.len() < rowhw {
                            seen.insert(rng.random_range(0..columns));
                        }
                        let mut sorted = seen.into_iter().collect::<Vec<_>>();
                        sorted.sort();
                        sorted.into_iter().map(|j|
                            (j, ring.random_element(|| rng.random::<u64>()))).collect()
                    }).collect(),
            zero: ring.zero(),
            desc: desc.to_string()
        }
    }
}

impl<'a, R> SparseMatrixMul<'a, R>
    where R: RingStore
{
    pub fn from<MM: MatrixMul<R = R>>(mm: &'a MM) -> Self {

        let data = (0..mm.rows()).map(|i| (0..mm.columns()).map(|j|
            (j, mm.ring().clone_el(mm.get(i,j)))).collect()).collect();
        
        Self {
            ring: mm.ring(),
            rows: mm.rows(),
            columns: mm.columns(),
            data,
            zero: mm.ring().zero(),
            desc: mm.desc().clone()
        }
    }
}

impl<'a, Rg: RingStore> Clone for SparseMatrixMul<'a, Rg> {
    fn clone(&self) -> Self {
        Self {
            ring: self.ring,
            rows: self.rows,
            columns: self.columns,
            data: self.data.iter().map(|v| v.iter().map(|(j, el)|
                    (*j, self.ring.clone_el(el))).collect()).collect(),
            zero: self.ring.zero(),
            desc: self.desc.clone()
        }
    }
}

impl<'a, Rg: RingStore> MatrixMul for SparseMatrixMul<'a, Rg> {

    type R = Rg;

    fn ring(&self) -> &Rg {
        self.ring
    }

    fn desc(&self) -> &String {
        &self.desc
    }

    fn rows(&self) -> usize {
        self.rows
    }

    fn columns(&self) -> usize {
        self.columns
    }

    fn get(&self, i: usize, j: usize) -> &El<Rg> {
        if let Some((_, x)) = self.data[i].iter().filter(|(jp, _)| *jp == j).next()
        { &x } else { &self.zero }
    }

    fn mulit(&self, rhs: &[El<Self::R>]) -> impl Iterator<Item = El<Self::R>> {
        debug_assert!(rhs.len() == self.columns());
        self.data.iter().map(|row| row.iter().fold(self.ring.zero(),
            |acc, (j, el)| self.ring.add(acc, self.ring.mul_ref(el, &rhs[*j]))))
    }
    // fn mul(&self, rhs: &[El<Rg>]) -> Vec<El<Rg>> {
    //     debug_assert!(rhs.len() == self.columns());
    //     (0..self.rows).map(|i| self.data[i].iter().map(|(j, el)|
    //         self.ring().mul_ref(el, &rhs[*j])).fold(
    //         self.ring.zero(), |acc, x| self.ring.add(acc, x))).collect::<Vec<_>>()
    // }
    
    fn mul(&self, rhs: &[El<Self::R>]) -> Vec<El<Self::R>> { self.mulit(rhs).collect() }
}


pub struct DenseMatrixMul<'a, R: RingStore> {
    ring: &'a R,
    rows: usize,
    columns: usize,
    data: Vec<El<R>>,
    desc: String
}

impl<'a, R: RingStore> DenseMatrixMul<'a, R> {

    pub fn new(ring: &'a R, columns: usize, data: Vec<El<R>>, desc: &str) -> Self
    {
        assert!(data.len() % columns == 0);
        Self {
            ring,
            rows: data.len() / columns,
            columns,
            data,
            desc: desc.to_string()
        }
    }

    // TODO: add to MatrixMul trait?
    pub fn submatmul(&self, rows: Range<usize>, columns: Range<usize>, rhs: &[El<R>])
        -> impl Iterator<Item = El<R>>
    {
        assert!(contains_range(0..self.rows(), &rows)
            && contains_range(0..self.columns(), &columns));
        debug_assert!(rhs.len() == columns.clone().len());
        let ncol = self.columns();
        let subrows = &self.data[rows.start*ncol..rows.end*ncol];
        subrows.chunks_exact(self.columns()).map(move |row|
            row[columns.clone()].iter().zip(rhs.iter()).fold(self.ring().zero(), |acc, (ri, rhsi)|
                self.ring().add(acc, self.ring().mul_ref(ri, rhsi))))
    }
}

impl<'a, R: RingStore<Type: FiniteRing>> DenseMatrixMul<'a, R> {
    pub fn random<RNG: Rng>(ring: &'a R, rng: RNG, rows: usize, columns: usize, desc: &str) -> Self
    {
        Self {
            ring,
            rows,
            columns,
            data: gen_random(ring, rng, rows*columns),
            desc: desc.to_string()
        }
    }
}

impl<'a, Rg: RingStore> Clone for DenseMatrixMul<'a, Rg> {
    fn clone(&self) -> Self {
        Self {
            ring: self.ring,
            rows: self.rows,
            columns: self.columns,
            data: self.data.iter().map(|el| self.ring.clone_el(el)).collect(),
            desc: self.desc.clone()
        }
    }
}


impl<'a, Rg: RingStore> MatrixMul for DenseMatrixMul<'a, Rg> {
    
    type R = Rg;

    fn ring(&self) -> &Rg {
        self.ring
    }

    fn desc(&self) -> &String {
        &self.desc
    }

    fn rows(&self) -> usize {
        self.rows
    }

    fn columns(&self) -> usize {
        self.columns
    }

    fn get(&self, i: usize, j: usize) -> &El<Rg> {
        &self.data[i*self.columns + j]
    }

    fn mulit(&self, rhs: &[El<Self::R>]) -> impl Iterator<Item = El<Rg>> {
        debug_assert!(rhs.len() == self.columns());
        self.submatmul(0..self.rows(), 0..self.columns(), rhs)
    }

    fn mul(&self, rhs: &[El<Self::R>]) -> Vec<El<Rg>> { self.mulit(rhs).collect() }
}


pub struct DiagMatrixMul<'a, R: RingStore> {
    ring: &'a R,
    size: usize,
    data: Vec<El<R>>,
    zero: El<R>,
    desc: String
}

impl<'a, R: RingStore> DiagMatrixMul<'a, R> {
    pub fn new(ring: &'a R, size: usize, data: Vec<El<R>>, desc: &str) -> Self {
        assert!(data.len() == size);
        Self {
            ring,
            size,
            data,
            zero: ring.zero(),
            desc: desc.to_string()
        }
    }
}

impl<'a, Rg: RingStore> Clone for DiagMatrixMul<'a, Rg> {
    fn clone(&self) -> Self {
        Self {
            ring: self.ring,
            size: self.size,
            data: self.data.iter().map(|el| self.ring.clone_el(el)).collect(),
            zero: self.ring.zero(),
            desc: self.desc.clone()
        }
    }
}

impl<'a, Rg: RingStore> MatrixMul for DiagMatrixMul<'a, Rg> {

    type R = Rg;

    fn ring(&self) -> &Rg {
        self.ring
    }

    fn desc(&self) -> &String {
        &self.desc
    }

    fn rows(&self) -> usize {
        self.size
    }

    fn columns(&self) -> usize {
        self.size
    }

    fn get(&self, i: usize, j: usize) -> &El<Rg> {
        if i != j {
            &self.zero
        } else {
            &self.data[i]
        }
    }

    fn mulit(&self, rhs: &[El<Rg>]) -> impl Iterator<Item = El<Rg>> {
        debug_assert!(rhs.len() == self.columns());
        self.data.iter().zip(rhs).map(|(d, r)| self.ring().mul_ref(d, r))
    }

    fn mul(&self, rhs: &[El<Rg>]) -> Vec<El<Rg>> { self.mulit(rhs).collect() }
}


pub struct RepeatMatrixMul<'a, MM: MatrixMul> {
    basemm: MM,
    repmm: DenseMatrixMul<'a, MM::R>,
    data: Vec<El<MM::R>>, // TODO: can this be avoided?
    desc: String
}

impl<'a, MM: MatrixMul> RepeatMatrixMul<'a, MM>
{
    pub fn new(basemm: &'a MM, rowrep: usize, columnrep: usize) -> Self
    {
        assert!(rowrep > 0 && columnrep > 0);
        let repmm = DenseMatrixMul::new(basemm.ring(), columnrep,
            (0..columnrep*rowrep).map(|_| basemm.ring().one()).collect(),
            format!("onesrep_{}{}", rowrep, columnrep).as_str());
        let mut desc = basemm.desc().clone();
        desc.push_str(&format!("_repeatmm_{}", repmm.desc()));
        Self {
            basemm: basemm.clone(),
            repmm,
            data: Vec::with_capacity(0),
            desc
        }
    }

    pub fn new_extra(basemm: &MM, repmm: DenseMatrixMul<'a, MM::R>) -> Self
    {
        let mut desc = basemm.desc().clone();
        desc.push_str(&format!("_repeat_{}", repmm.desc()));
        let tmp = &repmm;
        let data = (0..basemm.rows()*repmm.rows()).flat_map(|i|
                    (0..basemm.columns()*repmm.columns()).map(move |j|
                        RepeatMatrixMul::get_noref(basemm, tmp, i, j))).collect();
        Self {
            basemm: basemm.clone(),
            repmm,
            data,
            desc
        }
    }

    fn get_noref(basemm: &'a MM, repmm: &DenseMatrixMul<'a, MM::R>, i: usize, j: usize) -> El<MM::R> {
        basemm.ring().mul_ref(
            basemm.get(
                i.rem_euclid(basemm.rows()),
                j.rem_euclid(basemm.columns())),
            repmm.get(
                i.div_euclid(basemm.rows()),
                j.div_euclid(basemm.columns()))
        )
    }

}


impl<'a, MM: MatrixMul> Clone for RepeatMatrixMul<'a, MM> {
    fn clone(&self) -> Self {
        Self {
            basemm: self.basemm.clone(),
            repmm: self.repmm.clone(),
            data: self.data.iter().map(|el| self.basemm.ring().clone_el(el)).collect(),
            desc: self.desc.clone()
        }
    }
}


impl<'a, MM: MatrixMul> MatrixMul for RepeatMatrixMul<'a, MM>
{
    type R = MM::R;

    fn ring(&self) -> &MM::R {
        self.basemm.ring()
    }

    fn desc(&self) -> &String {
        &self.desc
    }

    fn rows(&self) -> usize {
        self.basemm.rows()*self.repmm.rows()
    }

    fn columns(&self) -> usize {
        self.basemm.columns()*self.repmm.columns()
    }

    fn get(&self, i: usize, j: usize) -> &El<MM::R> {
        if self.data.len() > 0 {
            &self.data[i*self.columns() + j]
        } else {
            self.basemm.get(
                i.rem_euclid(self.basemm.rows()),
                j.rem_euclid(self.basemm.columns()))
        }
    }

    fn mulit(&self, rhs: &[El<Self::R>]) -> impl Iterator<Item = El<Self::R>> {
        // TODO: can this be faster?
        self.mul(rhs).into_iter()
    }

    fn mul(&self, rhs: &[El<MM::R>]) -> Vec<El<MM::R>> {
        let mut res: Vec<_> = (0..self.basemm.rows()*self.repmm.rows()).map(|_|
            self.ring().zero()).collect();
        res.chunks_exact_mut(self.basemm.rows()).enumerate().for_each(|(i, ri)| {
            let reprow = (0..self.repmm.columns()).map(|k| self.repmm.get(i, k));
            let tmp = rhs.chunks_exact(self.basemm.columns()).zip(reprow).fold(
                (0..self.basemm.columns()).map(|_| self.ring().zero()).collect::<Vec<_>>(),
                |acc, (rhschunk, rri)| acc.into_iter().zip(rhschunk).map(|(a, r)|
                    self.ring().add(a, self.ring().mul_ref(r, rri))).collect());

            ri.iter_mut().zip(self.basemm.mul(&tmp)).for_each(|(rii, el)| *rii = el)
        });
        res
    }
}


pub struct HadamardMatrixMul<'a, R: RingStore> {
    mm: RepeatMatrixMul<'a, DenseMatrixMul<'a, R>>
}

impl<'a, R: RingStore> HadamardMatrixMul<'a, R>
{
    pub fn new(ring: &'a R, logsize: usize) -> Self
    {
        assert!(logsize > 0);
        let repmm = DenseMatrixMul::new(ring, 2,
            vec![ring.one(), ring.one(), ring.one(), ring.neg_one()],
            "hadamard1");
        let basemm = if logsize == 1 {
            DenseMatrixMul::new(ring, 1, vec![ring.one()], "hadamard0")
        } else {
            let tmp = HadamardMatrixMul::new(ring, logsize - 1);
            DenseMatrixMul::new(ring, 1 << (logsize - 1), tmp.mm.data,
                format!("hadamard{}", logsize - 1).as_str())
        };
        let mm = RepeatMatrixMul::new_extra(&basemm, repmm);
        Self { mm }
    }
}


impl<'a, R: RingStore> Clone for HadamardMatrixMul<'a, R> {
    fn clone(&self) -> Self {
        Self { mm: self.mm.clone() }
    }
}


impl<'a, Rg: RingStore> MatrixMul for HadamardMatrixMul<'a, Rg> {
    
    type R = Rg;

    fn ring(&self) -> &Rg {
        self.mm.ring()
    }

    fn desc(&self) -> &String {
        &self.mm.desc()
    }

    fn rows(&self) -> usize {
        self.mm.rows()
    }

    fn columns(&self) -> usize {
        self.mm.columns()
    }

    fn get(&self, i: usize, j: usize) -> &El<Rg> {
        self.mm.get(i, j)
    }

    fn mulit(&self, rhs: &[El<Self::R>]) -> impl Iterator<Item = El<Self::R>> {
        self.mm.mulit(rhs)
    }

    fn mul(&self, rhs: &[El<Rg>]) -> Vec<El<Rg>> {
        self.mm.mul(rhs)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use feanor_math::rings::zn::zn_64::Zn;
    use feanor_math::rings::zn::ZnRingStore;

    use crate::util::test_rot;

    #[test]
    fn test_matmul_repeat() {
        let field = Zn::new(65537).as_field().ok().unwrap();
        let mut rng = rand::rng();
        
        let rowcount = 11;
        let columncount = 23;

        let seed = format!("test_plainmatmul_{}{}", rowcount, columncount);
        let data = gen_random(&field, &mut rng, rowcount*columncount);
        let mm = DenseMatrixMul::new(&field, columncount, data, &seed);

        let rowrep = 2;
        let columnrep = 4;

        let mut repdata = (0..rowcount*rowrep*columncount*columnrep).map(|_|
            field.zero()).collect::<Vec<_>>();
        for bi in 0..rowrep {
            for bj in 0..columnrep {
                for i in 0..rowcount {
                    for j in 0..columncount {
                        repdata[(bi*rowcount + i)*columncount*columnrep + bj*columncount + j] = field.clone_el(&mm.get(i, j));
                    }
                }
            }
        }
        let mmrepdense = DenseMatrixMul::new(&field, columnrep*columncount, repdata, "_");

        let mmrep = RepeatMatrixMul::new(&mm, rowrep, columnrep);

        let testin = gen_random(&field, &mut rng, columncount*columnrep);

        test_rot(&field, &mmrep.mul(&testin), &mmrepdense.mul(&testin), 0);
    }

    #[test]
    fn test_submatmul() {
        let field = Zn::new(65537).as_field().ok().unwrap();
        let mut rng = rand::rng();
        
        let r = 10;
        let c = 12;

        let mm = DenseMatrixMul::random(&field, &mut rng, r, c, "test_submatmul");

        let mut rhs1 = gen_random(&field, &mut rng, c-4);
        let rhs2 = gen_random(&field, &mut rng, 4);

        let res11 = mm.submatmul(0..5, 0..(c-4), &rhs1).collect::<Vec<_>>();
        let res12 = mm.submatmul(0..5, (c-4)..c, &rhs2).collect::<Vec<_>>();

        rhs1.extend(rhs2);
        let res2 = mm.submatmul(5..r, 0..c, &rhs1);

        let rest = mm.mul(&rhs1);
       
        assert!(res11.iter().zip(res12).map(|(l,r)| field.add_ref_fst(l, r))
            .chain(res2).zip(rest).all(|(l,r)| field.eq_el(&l, &r)));
    }

    #[test]
    fn test_matmulit() {
        let field = Zn::new(65537).as_field().ok().unwrap();
        let mut rng = rand::rng();
        
        let r = 10;
        let c = 12;

        let mm = DenseMatrixMul::random(&field, &mut rng, r, c, "test_matmulit");

        let rhs1 = gen_random(&field, &mut rng, c);
        let rhs2 = gen_random(&field, &mut rng, c);

        let c = gen_random(&field, &mut rng, 1).pop().unwrap();

        let rhs3 = rhs1.iter().zip(rhs2.iter()).map(|(l,r)|
            field.add_ref_fst(l, field.mul_ref(&c, r))).collect::<Vec<_>>();
       
        assert!(mm.mulit(&rhs1).zip(mm.mulit(&rhs2)).map(|(l,r)| field.add(l,field.mul_ref_snd(r, &c)))
            .zip(mm.mulit(&rhs3)).all(|(l,r)| field.eq_el(&l, &r)))
    }
}


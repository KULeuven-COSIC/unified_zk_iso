#![feature(generic_const_exprs)]
#![feature(trusted_len)]

#![allow(incomplete_features)]
#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]

use itertools::Itertools;

use std::fs::File;
use std::io::{BufReader, BufRead};

use feanor_math::homomorphism::{Homomorphism, IntHom};
use feanor_math::ring::{RingStore, RingBase, El};
use feanor_math::rings::zn::ZnRingStore;
use feanor_math::rings::zn::zn_big::Zn;
use feanor_math::integer::{BigIntRing, IntegerRing, IntegerRingStore};
use feanor_math::rings::field::{FieldEl, AsField};
use feanor_math::field::{Field, FieldStore};
use feanor_math::rings::extension::{FreeAlgebraStore, extension_impl::FreeAlgebraImpl};
use feanor_math::rings::extension::galois_field::GaloisField;

use proofs::{
    commit::abdlop::ZZbig,
    util::{test_rot,
    matmul::{MatrixMul, HadamardMatrixMul, SparseMatrixMul, DenseMatrixMul}},
    r1cs::R1CS,
};


pub mod pcs;

pub mod sigma4D;


pub fn smaller_densemm<'a, R, Ro>(ring: &'a R, mm: &SparseMatrixMul<'a, Ro>)
    -> DenseMatrixMul<'a, R>
    where R: RingStore, Ro: RingStore
{
    let mut data = (0..mm.rows()*mm.columns()).map(|_| ring.zero()).collect_vec();
    mm.iter_rows().enumerate().for_each(|(i, row)| row.into_iter().for_each(|(j, el)| {
        data[i*mm.rows() + j] = if mm.ring().is_one(el) {
            ring.one()
        } else if mm.ring().is_neg_one(el) {
            ring.neg_one()
        } else {
            mm.ring().println(el);
            panic!("This should not happen")
        };
    }));
    DenseMatrixMul::new(ring, mm.columns(), data, mm.desc().clone().as_str())
}


fn get_p<const DIM: usize>() -> El<BigIntRing> {
    if DIM == 1 || DIM == 2 {
        ZZbig.sub(ZZbig.get_ring().mul_int(ZZbig.power_of_two(248), 5), ZZbig.one())
    } else if DIM == 4 {
        // ZZbig.get_ring().parse("864175120484581453683482079962486176185193500155369104423588921177379322250834082489183304374038697487834084609675858746433355728113743766078731283595263", 10).unwrap()
        ZZbig.sub(ZZbig.get_ring().mul_int(ZZbig.power_of_two(500), 27), ZZbig.one())
    } else {
        panic!("Invalid dimension")
    }
}

type RImpl = Zn<BigIntRing>;
type FieldImpl = AsField<RImpl>;

pub fn parseFp<const DIM: usize, const PP: bool>() -> (RImpl, FieldImpl, Vec<El<FieldImpl>>) {

    let p = get_p::<DIM>();
    let ring = Zn::new(ZZbig, p);
    let field = ring.clone().as_field().ok().unwrap();

    let transfilename = format!("../dim{}/zk_radical.txt", DIM);
    let br = BufReader::new(File::open(&transfilename).unwrap());

    let v = if DIM == 1 {
        let vFp2 = br.lines().next().unwrap().unwrap()
            .strip_prefix("A_is = [(").unwrap().to_string()
            .strip_suffix(")]").unwrap().to_string()
            .split("), (").flat_map(|x| x.split(", ")).map(|s| s.to_string())
            .collect_vec();
        
        vFp2.into_iter().flat_map(|s| {
            if let Some((im, re)) = s.split_once("*i") {
                [re.strip_prefix(" + ").unwrap_or("").to_string(), im.to_string()]
            } else {
                [s, String::from("")]
            }
        }).map(|s| field.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap()))
        .take(1024).collect_vec()
    } else if DIM == 2 {
        let vFp2 = br.lines().flat_map(|s|
            s.unwrap().split_terminator(";").map(|s|
                s.to_string()
                .strip_prefix("a").unwrap().to_string()
                .trim_start_matches(char::is_numeric).to_string()
                .strip_prefix("=").unwrap().to_string()
            ).collect_vec()).collect_vec();

        vFp2.into_iter().flat_map(|s| {
            if let Some((im, re)) = s.split_once("*i") {
                [re.strip_prefix(" + ").unwrap_or("").to_string(), im.to_string()]
            } else {
                [s, String::from("")]
            }
        }).map(|s| field.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap()))
        .take(2048).collect_vec()
    } else if DIM == 4 {
        let aFp2 = br.lines().flat_map(|s|
            s.unwrap().split_terminator(";").filter_map(|s|
                s.to_string()
                .strip_prefix("a").map(|x|
                    x.to_string()
                    .trim_start_matches(char::is_numeric).to_string()
                    .strip_prefix("=").unwrap().to_string()
                )
            ).collect_vec()).collect_vec();
        let mut aFp2 = aFp2.into_iter().map(|s| field.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap())).collect_vec();

        if PP {

            let br = BufReader::new(File::open(&transfilename).unwrap());
            let pFp2 = br.lines().flat_map(|s|
                s.unwrap().split_terminator(";").filter_map(|s|
                    s.to_string()
                    .strip_prefix("p").map(|x|
                        x.to_string()
                        .trim_start_matches(char::is_numeric).to_string()
                        .strip_prefix("=").unwrap().to_string()
                    )
                ).collect_vec()).collect_vec();
            let pFp2 = pFp2.into_iter().map(|s| field.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap())).collect_vec();
            aFp2.extend(pFp2);

            let br = BufReader::new(File::open(&transfilename).unwrap());
            let nzFp2 = br.lines().last().unwrap().unwrap().split_terminator(";").filter_map(|s|
                s.to_string().strip_prefix("nz").map(|x|
                    x.to_string()
                    .trim_start_matches(char::is_numeric).to_string()
                    .strip_prefix("=").unwrap().to_string()
                )
            ).collect_vec();
            let nzFp2 = nzFp2.into_iter().map(|s| field.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap())).collect_vec();
            aFp2.extend(nzFp2);

            let br = BufReader::new(File::open(&transfilename).unwrap());
            let sFp2 = br.lines().last().unwrap().unwrap().split_terminator(";").filter_map(|s|
                s.to_string().strip_prefix("s").map(|x|
                    x.to_string()
                    .trim_start_matches(char::is_numeric).to_string()
                    .strip_prefix("=").unwrap().to_string()
                )
            ).collect_vec();
            let sFp2 = sFp2.into_iter().map(|s| field.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap())).collect_vec();

            // getting N
            let Nfilename = "../dim4/tmpN.txt".to_string();
            let br = BufReader::new(File::open(&Nfilename).unwrap());
            let N = br.lines().take(2).map(|s|
                s.unwrap()
                .strip_prefix("(").unwrap().to_string()
                .strip_suffix(")").unwrap().to_string()
                .split_terminator(", ").map(|s| {
                    let x = s.to_string();
                    field.coerce(&ZZbig, ZZbig.get_ring().parse(&x, 10).unwrap())
                }).collect_vec()).collect_vec();

            let Nmod = (0..DIM*DIM).map(|i|
                field.sub(field.mul_ref(&N[0][i], &sFp2[1]), field.mul_ref(&N[1][i], &sFp2[0]))
            ).collect_vec();
            aFp2.extend(Nmod);
        }
        aFp2
    } else {
        panic!("Invalid dimension")
    };

    (ring, field, v)
}


type RImpl2 = FreeAlgebraImpl<AsField<RImpl>, [FieldEl<RImpl>; 2]>;
// type FieldImpl2 = AsField<RImpl2>;
type FieldImpl2 = GaloisField<AsField<RImpl2>>;

pub fn parseFp2<const DIM: usize>() -> (RImpl2, FieldImpl2, Vec<El<FieldImpl2>>) {

    let p = get_p::<DIM>();
    let basering = Zn::new(ZZbig, p).as_field().ok().unwrap();

    let powrank = [basering.neg_one(), basering.zero()];
    let ring = FreeAlgebraImpl::new(basering.clone(), 2, powrank);
    let field = ring.clone().as_field().ok().unwrap();
    let gf = GaloisField::create(field);
    let hom = gf.can_hom(&ring).unwrap();

    let br = BufReader::new(File::open(format!("../dim{}/zk_radical.txt", DIM)).unwrap());
    
    let v = if DIM == 1 {
        let vFp2 = br.lines().next().unwrap().unwrap()
            .strip_prefix("A_is = [(").unwrap().to_string()
            .strip_suffix(")]").unwrap().to_string()
            .split("), (").flat_map(|x| x.split(", ")).map(|s| s.to_string())
            .collect_vec();
        
        vFp2.into_iter().flat_map(|s| {
            if let Some((im, re)) = s.split_once("*i") {
                [re.strip_prefix(" + ").unwrap_or("").to_string(), im.to_string()]
            } else {
                [s, String::from("")]
            }
        }).map(|s| basering.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap()))
        .chunks(2).into_iter().map(|mut c|
            hom.map(ring.from_canonical_basis([c.next().unwrap(), c.next().unwrap()])))
        .take(512).collect_vec()
    } else if DIM == 2 {
        let vFp2 = br.lines().flat_map(|s|
            s.unwrap().split_terminator(";").map(|s|
                s.to_string()
                .strip_prefix("a").unwrap().to_string()
                .trim_start_matches(char::is_numeric).to_string()
                .strip_prefix("=").unwrap().to_string()
            ).collect_vec()).collect_vec();

        vFp2.into_iter().flat_map(|s| {
            if let Some((im, re)) = s.split_once("*i") {
                [re.strip_prefix(" + ").unwrap_or("").to_string(), im.to_string()]
            } else {
                [s, String::from("")]
            }
        }).map(|s| basering.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap()))
        .chunks(2).into_iter().map(|mut c|
            hom.map(ring.from_canonical_basis([c.next().unwrap(), c.next().unwrap()])))
        .take(1024).collect_vec()
    } else {
        panic!("Invalid dimension")
    };

    (ring, gf, v)
}


pub fn parseFp_cgl() -> (RImpl, FieldImpl, Vec<El<FieldImpl>>) {

    let p = ZZbig.sub(ZZbig.power_of_two(127), ZZbig.one());
    let ring = Zn::new(ZZbig, p);
    let field = ring.clone().as_field().ok().unwrap();

    let br = BufReader::new(File::open("../theta_cgl_py/zk_radical.txt").unwrap());

    let vFp2 = br.lines().flat_map(|s|
        s.unwrap().split_terminator(";").map(|s|
            s.to_string()
            .strip_prefix("a").unwrap().to_string()
            .trim_start_matches(char::is_numeric).to_string()
            .strip_prefix(" = ").unwrap().to_string()
        ).collect_vec()).collect_vec();

    let v = vFp2.into_iter().flat_map(|s| {
        if let Some((im, re)) = s.split_once("i") {
            let tmp = im.trim_end_matches("*").to_string();
            [re.strip_prefix(" + ").unwrap_or("").to_string(),
                if tmp.is_empty() {"1".to_string()} else {tmp}]
        } else {
            [s, String::from("")]
        }
    }).map(|s| field.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap()))
    .collect_vec();

    (ring, field, v)
}


pub fn parseFp2_cgl() -> (RImpl2, FieldImpl2, Vec<El<FieldImpl2>>) {

    let p = ZZbig.sub(ZZbig.power_of_two(127), ZZbig.one());
    let basering = Zn::new(ZZbig, p).as_field().ok().unwrap();

    let powrank = [basering.neg_one(), basering.zero()];
    let ring = FreeAlgebraImpl::new(basering.clone(), 2, powrank);
    let field = ring.clone().as_field().ok().unwrap();
    let gf = GaloisField::create(field);
    // let hom = field.can_hom(&ring).unwrap();
    let hom = gf.can_hom(&ring).unwrap();

    let br = BufReader::new(File::open("../theta_cgl_py/zk_radical.txt").unwrap());
    
    let vFp2 = br.lines().flat_map(|s|
        s.unwrap().split_terminator(";").map(|s|
            s.to_string()
            .strip_prefix("a").unwrap().to_string()
            .trim_start_matches(char::is_numeric).to_string()
            .strip_prefix(" = ").unwrap().to_string()
        ).collect_vec()).collect_vec();

    let v = vFp2.into_iter().flat_map(|s| {
        if let Some((im, re)) = s.split_once("i") {
            let tmp = im.trim_end_matches("*").to_string();
            [re.strip_prefix(" + ").unwrap_or("").to_string(),
                if tmp.is_empty() {"1".to_string()} else {tmp}]
        } else {
            [s, String::from("")]
        }
    }).map(|s| basering.coerce(&ZZbig, ZZbig.get_ring().parse(&s, 10).unwrap()))
    .chunks(2).into_iter().map(|mut c|
        hom.map(ring.from_canonical_basis([c.next().unwrap(), c.next().unwrap()])))
    .collect_vec();

    (ring, gf, v)
}


pub fn construct_r1cs_Fp<'a, F, const DIM: usize, const PP: bool>(field: &'a F, v: &[El<F>])
    -> (Vec<El<F>>, R1CS<'a, F>)
    where F: RingStore + Clone
{
    let D = 1 << DIM;
    let vlen = if PP { (v.len() - (D+1))/2 } else { v.len() };
    // also Nmod and nz are passed through v vector but only nz is part of witness
    debug_assert!(vlen % D == 0);

    let H = HadamardMatrixMul::new(&field, DIM);

    let mut z = Vec::with_capacity(vlen);
    let mut z2 = Vec::with_capacity(vlen);
    
    (0..(vlen/D - 1)).for_each(|i| {
        let vcur = &v[i*D..(i+1)*D];
        let mut vcur2 = vcur.iter().map(|el| field.mul_ref(el, el)).collect_vec();
        let rhs = H.mul(&vcur2);

        z.extend(vcur.into_iter().map(|el| field.clone_el(el)));
        z2.append(&mut vcur2);

        if cfg!(debug_assertions) {
            let vnext = &v[(i+1)*D..(i+2)*D];
            let vnexth = H.mul(&vnext);
            let lhs = vnexth.iter().map(|el| field.mul_ref(el, el)).collect_vec();

            test_rot(&field, &lhs, &rhs, 0);
        }
    });

    let vlast = &v[(vlen - D)..vlen];
    z.extend(vlast.iter().map(|el| field.clone_el(el)));
    z2.extend(vlast.iter().map(|el| field.mul_ref(el, el)));

    z.append(&mut z2);
    debug_assert!(z.len() == 2*vlen);
    let numcols = (2*vlen).next_power_of_two();
    z.extend((0..(numcols-(2*vlen))).map(|_| field.zero()));

    let Hsparse = SparseMatrixMul::from(&H);

    let mut Adata = Vec::with_capacity(2*vlen);
    Adata.extend((0..vlen).map(|i| vec![(i, field.one())]));
    (0..(vlen - D)/D).for_each(|i|
        Adata.extend(Hsparse.get_data().into_iter().map(|vrow|
            vrow.into_iter().map(|(j, el)| (j + i*D + D, field.clone_el(el))).collect()
        ))
    );
    Adata.extend((0..D).map(|_| Vec::new()));
    Adata.extend((0..(numcols-(2*vlen))).map(|_| vec![]));

    let mut Cdata = Vec::with_capacity(2*vlen);
    Cdata.extend((0..vlen).map(|i| vec![(i + vlen, field.one())]));
    (0..(vlen - D)/D).for_each(|i|
        Cdata.extend(Hsparse.get_data().into_iter().map(|vrow|
            vrow.into_iter().map(|(j, el)| (vlen + j + i*D, field.clone_el(el))).collect()
        ))
    );
    Cdata.extend((0..D).map(|_| Vec::new()));
    Cdata.extend((0..(numcols-(2*vlen))).map(|_| vec![]));

    let (A, B, C) = if !PP {
        let A = SparseMatrixMul::new(field, numcols, Adata, format!("iso{}D_AB", D).as_str());
        let B = A.clone(); // TODO: make custom Spartan where A==B
        let C = SparseMatrixMul::new(field, numcols, Cdata, format!("iso{}D_C", D).as_str());
        (A, B, C)
    } else {

        let numrows = Adata.len();
        let mut Bdata = Adata.iter().map(|row| row.iter().map(|(j, el)| (*j, field.clone_el(el))).collect_vec()).collect_vec();
        Bdata.extend(Bdata[..vlen].iter().map(|row| row.iter().map(|(j, el)|
            (*j + numrows, field.clone_el(el))).collect()).collect_vec());
        Bdata.extend(Bdata[vlen..numrows].iter().map(|row| row.iter().map(|(j, el)|
            (*j, field.clone_el(el))).collect()).collect_vec());

        Adata.extend(Adata.iter().map(|row| row.iter().map(|(j, el)|
                (j+numrows, field.clone_el(el))).collect()).collect_vec());
        Cdata.extend(Cdata.iter().map(|row| row.iter().map(|(j, el)|
                (j+numrows, field.clone_el(el))).collect()).collect_vec());

        // adding last relations
        assert!(numcols-(2*vlen) >= 2);

        Adata[numcols-1] = vec![(numcols + 2*vlen, field.one())];
        Bdata[numcols-1] = ((numcols+vlen-D)..(numcols+vlen)).zip(v[2*vlen+1..].iter()).map(|(j, el)|
            (j, field.clone_el(el))).collect();
        Cdata[numcols-1] = vec![(numcols + 2*vlen + 1, field.one())];

        let mut zPP = Vec::with_capacity(vlen);
        let mut z2PP = Vec::with_capacity(vlen);

        (0..(vlen/D - 1)).for_each(|i| {
            let vcur = &v[vlen+i*D..vlen+(i+1)*D];
            let mut vcur2 = vcur.iter().map(|el| field.mul_ref(el, el)).collect_vec();
            let rhs = H.mul(&vcur2);

            zPP.extend(vcur.into_iter().map(|el| field.clone_el(el)));
            z2PP.append(&mut vcur2);

            if cfg!(debug_assertions) {
                let anext = &v[(i+1)*D..(i+2)*D];
                let anexth = H.mul(&anext);
                let pnext = &v[vlen+(i+1)*D..vlen+(i+2)*D];
                let pnexth = H.mul(&pnext);
                let lhs = anexth.iter().zip(pnexth.iter()).map(|(ael, pel)|
                    field.mul_ref(ael, pel)).collect_vec();

                test_rot(&field, &lhs, &rhs, 0);
            }
        });

        let vlast = &v[(2*vlen - D)..2*vlen];
        zPP.extend(vlast.iter().map(|el| field.clone_el(el)));
        z2PP.extend(vlast.iter().map(|el| field.mul_ref(el, el)));

        zPP.append(&mut z2PP);
        debug_assert!(zPP.len() == 2*vlen);
        zPP.push(field.clone_el(&v[2*vlen])); // adding nz
        zPP.push(field.one()); // adding one
        zPP.extend((0..(numcols-(2*vlen)-2)).map(|_| field.zero()));

        z.append(&mut zPP);

        let A = SparseMatrixMul::new(field, 2*numcols, Adata, format!("iso{}D_A", D).as_str());
        let B = SparseMatrixMul::new(field, 2*numcols, Bdata, format!("iso{}D_B", D).as_str());
        let C = SparseMatrixMul::new(field, 2*numcols, Cdata, format!("iso{}D_C", D).as_str());
        (A, B, C)
    };

    // println!("m: {}", A.rows());
    println!("m: {}", 2*vlen + if PP {2*vlen + 2} else {0});
    println!("n: {}", 2*vlen + if PP {2*vlen} else {0});
    println!("nz: {}", A.nonzero_entries() + C.nonzero_entries()
        + if PP {B.nonzero_entries()} else {0});

    (z, R1CS::new(A, B, C))
}


fn squareFp2<'a, R: RingStore>(ring: &'a R, coeff: &[El<R>], d: &El<R>, inthom: &IntHom<&'a R>)
    -> [El<R>; 2]
{
    let p = &coeff[0];
    let q = &coeff[1];
    [
        ring.mul(ring.add_ref(p, q), ring.add_ref_fst(p, ring.mul_ref(q, d))),
        ring.mul(ring.mul_ref(p, q), inthom.map(2))
    ]
}

fn crossFp2dim1<'a, R: RingStore, I>(ring: &'a R, coeff: &mut I) -> [El<R>; 4]
    where I: Iterator<Item = &'a El<R>>
{
    let xi = coeff.next().unwrap();
    let yi = coeff.next().unwrap();
    let xj = coeff.next().unwrap();
    let yj = coeff.next().unwrap();
    [ ring.mul_ref(xi, xj), ring.mul_ref(yi, yj), ring.mul_ref(xi, yj), ring.mul_ref(xj, yi) ]
}

fn crossFp2dim1_half<'a, R: RingStore, I>(ring: &'a R, coeff: &mut I) -> [El<R>; 2]
    where I: Iterator<Item = &'a El<R>>
{
    let xi = coeff.next().unwrap();
    let _yi = coeff.next().unwrap();
    let xj = coeff.next().unwrap();
    let yj = coeff.next().unwrap();
    [ ring.mul_ref(xi, xj), ring.mul_ref(xi, yj) ]
}


pub fn construct_r1cs_Fp2_dim1<'a, F>(field: &'a F, v: &[El<F>]) -> (Vec<El<F>>, R1CS<'a, F>)
    where F: RingStore<Type: Field> + Clone
{
    let vlen = v.len()/2 as usize; // number of fp2 elements in v
    let DIM = 1;
    let Dact = 1 << DIM;
    let D = 2*Dact;
    debug_assert!(2*vlen % D == 0);

    let inthom = field.int_hom();

    let actrows = 2*vlen + vlen + 2*vlen-D;
    let numrows = actrows.next_power_of_two();
    let actcols = 5*vlen;
    let numcols = actcols.next_power_of_two();

    let mut z = Vec::with_capacity(numcols);
    let mut z2 = Vec::with_capacity(2*vlen);
    let mut zx = Vec::with_capacity(2*vlen);

    let HFp2 = HadamardMatrixMul::new(&field, DIM);
    let H = SparseMatrixMul::emulFp2lin(SparseMatrixMul::from(&HFp2));

    let d = field.neg_one();
    // (d+1)/2
    let dtmp = field.div(&field.add_ref_fst(&d, field.one()), &inthom.map(2));
    let dtmpneg = field.negate(field.clone_el(&dtmp));

    (0..(2*vlen/D - 1)).for_each(|i| {

        let vcur = &v[i*D..(i+1)*D];
        let mut vcur2 = vcur.chunks_exact(2).flat_map(|fp2|
            squareFp2(field, fp2, &d, &inthom)).collect_vec();
        let rhs = H.mul(&vcur2);

        z.extend(vcur.iter().map(|el| field.clone_el(el)));
        z2.append(&mut vcur2);
        // TODO: first crossterms not needed
        zx.extend(crossFp2dim1_half(field, &mut vcur.iter()));

        // NOTE: vcur2 is not exactly Re,Im zipped vector of squares of vcur but
        // NOTE: in the case of d = -1 then it is
        if cfg!(debug_assertions) {
            let vnext = &v[(i+1)*D..(i+2)*D];
            let vnexth = H.mul(&vnext);
            let lhs = vnexth.chunks_exact(2).flat_map(|fp2|
                squareFp2(field, fp2, &d, &inthom)).collect_vec();

            test_rot(&field, &lhs, &rhs, 0);
        }
    });

    let vlast = &v[(2*vlen - D)..];
    z.extend(vlast.iter().map(|el| field.clone_el(el)));
    // TODO: last squares not needed?
    z2.extend(vlast.chunks_exact(2).flat_map(|fp2| squareFp2(field, fp2, &d, &inthom)));
    zx.extend(crossFp2dim1_half(field, &mut vlast.iter()));

    z.append(&mut z2);
    z.append(&mut zx);
    assert!(z.len() == actcols);
    z.extend((0..(numcols-actcols)).map(|_| field.zero()));

    let mut Adata = Vec::with_capacity(numrows);
    Adata.extend((0..vlen).flat_map(|i| [
        vec![(2*i, field.one()), (2*i+1, field.one())],
        vec![(2*i, field.one())]
    ]));
    Adata.extend((0..vlen/2).flat_map(|i| [
        vec![(4*i, field.one())],
        vec![(4*i, field.one())],
    ]));
    Adata.extend((0..(vlen/2-1)).flat_map(|i| [
        vec![ (4*(i+1) + 1, field.mul_ref_fst(&d, inthom.map(2))) ],
        vec![ (4*(i+1) + 1, field.mul_ref_fst(&d, inthom.map(-2))) ],
        vec![ (4*(i+1) + 2, inthom.map(2)) ],
        vec![ (4*(i+1) + 2, inthom.map(-2)) ],
    ]));
    Adata.extend((0..(numrows-actrows)).map(|_| vec![]));

    let mut Bdata = Vec::with_capacity(numrows);
    Bdata.extend((0..vlen).flat_map(|i| [
        vec![(2*i, field.one()), (2*i+1, field.clone_el(&d))],
        vec![(2*i+1, inthom.map(2))]
    ]));
    Bdata.extend((0..vlen/2).flat_map(|i| [
        vec![(4*i+2, field.one())],
        vec![(4*i+3, field.one())],
    ]));
    Bdata.extend((0..(vlen/2-1)).flat_map(|i| [
        vec![ (4*(i+1) + 3, field.one()) ],
        vec![ (4*(i+1) + 3, field.one()) ],
        vec![ (4*(i+1) + 1, field.one()) ],
        vec![ (4*(i+1) + 1, field.one()) ],
    ]));
    Bdata.extend((0..(numrows-actrows)).map(|_| vec![]));

    let mut Cdata = Vec::with_capacity(numrows);
    Cdata.extend((0..2*vlen).map(|i| vec![(2*vlen + i, field.one())]));
    Cdata.extend((0..vlen).map(|i| vec![(4*vlen + i, field.one())]));
    Cdata.extend((0..(vlen/2-1)).flat_map(|i| [
        vec![
            (2*vlen + 4*i, field.one()),
            (2*vlen + 4*i+1, field.clone_el(&dtmpneg)),
            (2*vlen + 4*i+2, field.one()),
            (2*vlen + 4*i+3, field.clone_el(&dtmpneg)),
            (2*vlen + 4*i+4, field.neg_one()),
            (2*vlen + 4*i+5, field.clone_el(&dtmp)),
            (2*vlen + 4*i+6, field.neg_one()),
            (2*vlen + 4*i+7, field.clone_el(&dtmp)),
            (4*vlen + 2*(i+1), inthom.map(-2)),
        ],
        vec![
            (2*vlen + 4*i, field.one()),
            (2*vlen + 4*i+1, field.clone_el(&dtmpneg)),
            (2*vlen + 4*i+2, field.neg_one()),
            (2*vlen + 4*i+3, field.clone_el(&dtmp)),
            (2*vlen + 4*i+4, field.neg_one()),
            (2*vlen + 4*i+5, field.clone_el(&dtmp)),
            (2*vlen + 4*i+6, field.neg_one()),
            (2*vlen + 4*i+7, field.clone_el(&dtmp)),
            (4*vlen + 2*(i+1), inthom.map(2)),
        ],
        vec![
            (2*vlen + 4*i+1, field.one()),
            (2*vlen + 4*i+3, field.one()),
            (2*vlen + 4*i+5, field.neg_one()),
            (2*vlen + 4*i+7, field.neg_one()),
            (4*vlen + 2*(i+1)+1, inthom.map(-2)),
        ],
        vec![
            (2*vlen + 4*i+1, field.one()),
            (2*vlen + 4*i+3, field.neg_one()),
            (2*vlen + 4*i+5, field.neg_one()),
            (2*vlen + 4*i+7, field.neg_one()),
            (4*vlen + 2*(i+1)+1, inthom.map(2)),
        ],
    ]));
    Cdata.extend((0..(numrows-actrows)).map(|_| vec![]));

    let A = SparseMatrixMul::new(field, numcols, Adata, format!("iso{}D_A", D).as_str());
    let B = SparseMatrixMul::new(field, numcols, Bdata, format!("iso{}D_B", D).as_str());
    let C = SparseMatrixMul::new(field, numcols, Cdata, format!("iso{}D_C", D).as_str());

    println!("m: {actrows}");
    println!("n: {actcols}");
    println!("nz: {}", A.nonzero_entries() + B.nonzero_entries() + C.nonzero_entries());

    (z, R1CS::new(A, B, C))
}


fn crossFp2dim2<'a, R: RingStore>(ring: &'a R, coeff: &[El<R>]) -> Vec<El<R>>
{
    crossFp2dim1_half(ring, &mut coeff[0..2].iter().chain(coeff[2..4].iter())).into_iter()
    .chain(crossFp2dim1(ring, &mut coeff[0..2].iter().chain(coeff[4..6].iter())).into_iter())
    .chain(crossFp2dim1(ring, &mut coeff[0..2].iter().chain(coeff[6..8].iter())).into_iter())
    .chain(crossFp2dim1(ring, &mut coeff[2..4].iter().chain(coeff[4..6].iter())).into_iter())
    .chain(crossFp2dim1(ring, &mut coeff[2..4].iter().chain(coeff[6..8].iter())).into_iter())
    .chain(crossFp2dim1(ring, &mut coeff[4..6].iter().chain(coeff[6..8].iter())).into_iter())
    .collect_vec()
}


pub fn construct_r1cs_Fp2_dim2<'a, F>(field: &'a F, v: &[El<F>]) -> (Vec<El<F>>, R1CS<'a, F>)
    where F: RingStore<Type: Field> + Clone
{
    let vlen = v.len()/2 as usize; // number of fp2 elements in v
    let DIM = 2;
    let Dact = 1 << DIM;
    let D = 2*Dact;
    debug_assert!(2*vlen % D == 0);

    let inthom = field.int_hom();

    let actrows = 2*vlen + 11*(vlen/2) + 2*vlen-D;
    let numrows = actrows.next_power_of_two();
    let actcols = 4*vlen + 11*(vlen/2);
    let numcols = actcols.next_power_of_two();

    let mut z = Vec::with_capacity(numcols);
    let mut z2 = Vec::with_capacity(2*vlen);
    let mut zx = Vec::with_capacity(6*vlen);

    let HFp2 = HadamardMatrixMul::new(&field, Dact.ilog2() as usize);
    let HFp2sparse = SparseMatrixMul::from(&HFp2);
    let H = SparseMatrixMul::emulFp2lin(HFp2sparse);

    let d = field.neg_one();
    // (d+1)/2
    let dtmp = field.div(&field.add_ref_fst(&d, field.one()), &inthom.map(2));
    let dtmpneg = field.negate(field.clone_el(&dtmp));

    (0..(2*vlen/D - 1)).for_each(|i| {
        
        let vcur = &v[i*D..(i+1)*D];
        let mut vcur2 = vcur.chunks_exact(2).flat_map(|fp2|
            squareFp2(field, fp2, &d, &inthom)).collect_vec();
        let rhs = H.mul(&vcur2);

        z.extend(vcur.into_iter().map(|el| field.clone_el(el)));
        z2.append(&mut vcur2);
        // TODO: first crossterms not needed
        zx.extend(crossFp2dim2(field, vcur));

        if cfg!(debug_assertions) {
            let vnext = &v[(i+1)*D..(i+2)*D];
            let vnexth = H.mul(&vnext);
            let lhs = vnexth.chunks_exact(2).flat_map(|fp2|
                squareFp2(field, fp2, &d, &inthom)).collect_vec();

            test_rot(&field, &lhs, &rhs, 0);
        }
    });

    let vlast = &v[(2*vlen - D)..];
    z.extend(vlast.iter().map(|el| field.clone_el(el)));
    // TODO: last squares not needed?
    z2.extend(vlast.chunks_exact(2).flat_map(|fp2| squareFp2(field, fp2, &d, &inthom)));
    zx.extend(crossFp2dim2(field, vlast));

    z.append(&mut z2);
    z.append(&mut zx);
    assert!(z.len() == actcols);
    z.extend((0..(numcols-actcols)).map(|_| field.zero()));

    let mut Adata = Vec::with_capacity(numrows);
    Adata.extend((0..vlen).flat_map(|i| [
        vec![(2*i, field.one()), (2*i+1, field.one())],
        vec![(2*i, field.one())]
    ]));
    Adata.extend((0..vlen/4).flat_map(|i| [
        vec![(D*i, field.one())], vec![(D*i, field.one())],
        vec![(D*i, field.one())], vec![(D*i+1, field.one())], vec![(D*i, field.one())], vec![(D*i+4, field.one())],
        vec![(D*i, field.one())], vec![(D*i+1, field.one())], vec![(D*i, field.one())], vec![(D*i+6, field.one())],
        vec![(D*i+2, field.one())], vec![(D*i+3, field.one())], vec![(D*i+2, field.one())], vec![(D*i+4, field.one())],
        vec![(D*i+2, field.one())], vec![(D*i+3, field.one())], vec![(D*i+2, field.one())], vec![(D*i+6, field.one())],
        vec![(D*i+4, field.one())], vec![(D*i+5, field.one())], vec![(D*i+4, field.one())], vec![(D*i+6, field.one())],
    ]));
    Adata.extend((0..(vlen/4-1)).flat_map(|i| [
        vec![ (D*(i+1) + 1, field.mul_ref_fst(&d, inthom.map(-2))) ],
        vec![ (D*(i+1) + 2, inthom.map(-2)) ],
        vec![ (D*(i+1) + 1, field.mul_ref_fst(&d, inthom.map(2))) ],
        vec![ (D*(i+1) + 2, inthom.map(2)) ],
        vec![ (D*(i+1) + 1, field.mul_ref_fst(&d, inthom.map(-2))) ],
        vec![ (D*(i+1) + 2, inthom.map(-2)) ],
        vec![ (D*(i+1) + 1, field.mul_ref_fst(&d, inthom.map(2))) ],
        vec![ (D*(i+1) + 2, inthom.map(2)) ],
    ]));
    Adata.extend((0..(numrows-actrows)).map(|_| vec![]));

    let mut Bdata = Vec::with_capacity(numrows);
    Bdata.extend((0..vlen).flat_map(|i| [
        vec![(2*i, field.one()), (2*i+1, field.clone_el(&d))],
        vec![(2*i+1, inthom.map(2))]
    ]));
    Bdata.extend((0..vlen/4).flat_map(|i| [
        vec![(D*i+2, field.one())], vec![(D*i+3, field.one())],
        vec![(D*i+4, field.one())], vec![(D*i+5, field.one())], vec![(D*i+5, field.one())], vec![(D*i+1, field.one())],
        vec![(D*i+6, field.one())], vec![(D*i+7, field.one())], vec![(D*i+7, field.one())], vec![(D*i+1, field.one())],
        vec![(D*i+4, field.one())], vec![(D*i+5, field.one())], vec![(D*i+5, field.one())], vec![(D*i+3, field.one())],
        vec![(D*i+6, field.one())], vec![(D*i+7, field.one())], vec![(D*i+7, field.one())], vec![(D*i+3, field.one())],
        vec![(D*i+6, field.one())], vec![(D*i+7, field.one())], vec![(D*i+7, field.one())], vec![(D*i+5, field.one())],
    ]));
    Bdata.extend((0..(vlen/4-1)).flat_map(|i| [
        vec![ (D*(i+1) + 3, field.one()) ],
        vec![ (D*(i+1) + 1, field.one()) ],
        vec![ (D*(i+1) + 3, field.one()) ],
        vec![ (D*(i+1) + 1, field.one()) ],
        vec![ (D*(i+1) + 3, field.one()) ],
        vec![ (D*(i+1) + 1, field.one()) ],
        vec![ (D*(i+1) + 3, field.one()) ],
        vec![ (D*(i+1) + 1, field.one()) ],
    ]));
    Bdata.extend((0..(numrows-actrows)).map(|_| vec![]));

    let mut Cdata = Vec::with_capacity(numrows);
    Cdata.extend((0..2*vlen).map(|i| vec![(2*vlen + i, field.one())]));
    Cdata.extend((0..11*(vlen/2)).map(|i| vec![(4*vlen + i, field.one())]));
    // TODO: clean this
    Cdata.extend((0..(vlen/4-1)).flat_map(|i| [
        vec![ // 1
            (2*vlen + D*i + 0, field.neg_one()),
            (2*vlen + D*i + 1, field.clone_el(&dtmp)),
            (2*vlen + D*i + 2, field.neg_one()),
            (2*vlen + D*i + 3, field.clone_el(&dtmp)),
            (2*vlen + D*i + 4, field.neg_one()),
            (2*vlen + D*i + 5, field.clone_el(&dtmp)),
            (2*vlen + D*i + 6, field.neg_one()),
            (2*vlen + D*i + 7, field.clone_el(&dtmp)),
            (2*vlen + D*i + 8, field.one()),
            (2*vlen + D*i + 9, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 10, field.one()),
            (2*vlen + D*i + 11, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 12, field.one()),
            (2*vlen + D*i + 13, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 14, field.one()),
            (2*vlen + D*i + 15, field.clone_el(&dtmpneg)),
            (4*vlen + 22*(i+1) + 0, inthom.map(2)), // 12
            (4*vlen + 22*(i+1) + 2, inthom.map(2)), // 13
            (4*vlen + 22*(i+1) + 3, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 6, inthom.map(2)), // 14
            (4*vlen + 22*(i+1) + 7, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 10, inthom.map(2)), // 23
            (4*vlen + 22*(i+1) + 11, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 14, inthom.map(2)), // 24
            (4*vlen + 22*(i+1) + 15, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 18, inthom.map(2)), // 34
            (4*vlen + 22*(i+1) + 19, field.mul_ref_fst(&d, inthom.map(2))),
        ],
        vec![ // 2
            (2*vlen + D*i + 1, field.neg_one()),
            (2*vlen + D*i + 3, field.neg_one()),
            (2*vlen + D*i + 5, field.neg_one()),
            (2*vlen + D*i + 7, field.neg_one()),
            (2*vlen + D*i + 9, field.one()),
            (2*vlen + D*i + 11, field.one()),
            (2*vlen + D*i + 13, field.one()),
            (2*vlen + D*i + 15, field.one()),
            (4*vlen + 22*(i+1) + 1, inthom.map(2)), // 12
            (4*vlen + 22*(i+1) + 4, inthom.map(2)), // 13
            (4*vlen + 22*(i+1) + 5, inthom.map(2)),
            (4*vlen + 22*(i+1) + 8, inthom.map(2)), // 14
            (4*vlen + 22*(i+1) + 9, inthom.map(2)),
            (4*vlen + 22*(i+1) + 12, inthom.map(2)), // 23
            (4*vlen + 22*(i+1) + 13, inthom.map(2)),
            (4*vlen + 22*(i+1) + 16, inthom.map(2)), // 24
            (4*vlen + 22*(i+1) + 17, inthom.map(2)),
            (4*vlen + 22*(i+1) + 20, inthom.map(2)), // 34
            (4*vlen + 22*(i+1) + 21, inthom.map(2)),
        ],
        vec![ // 3
            (2*vlen + D*i + 0, field.neg_one()),
            (2*vlen + D*i + 1, field.clone_el(&dtmp)),
            (2*vlen + D*i + 2, field.one()),
            (2*vlen + D*i + 3, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 4, field.neg_one()),
            (2*vlen + D*i + 5, field.clone_el(&dtmp)),
            (2*vlen + D*i + 6, field.one()),
            (2*vlen + D*i + 7, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 8, field.one()),
            (2*vlen + D*i + 9, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 10, field.one()),
            (2*vlen + D*i + 11, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 12, field.one()),
            (2*vlen + D*i + 13, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 14, field.one()),
            (2*vlen + D*i + 15, field.clone_el(&dtmpneg)),
            (4*vlen + 22*(i+1) + 0, inthom.map(-2)), // 12
            (4*vlen + 22*(i+1) + 2, inthom.map(2)), // 13
            (4*vlen + 22*(i+1) + 3, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 6, inthom.map(-2)), // 14
            (4*vlen + 22*(i+1) + 7, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 10, inthom.map(-2)), // 23
            (4*vlen + 22*(i+1) + 11, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 14, inthom.map(2)), // 24
            (4*vlen + 22*(i+1) + 15, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 18, inthom.map(-2)), // 34
            (4*vlen + 22*(i+1) + 19, field.mul_ref_fst(&d, inthom.map(-2))),
        ],
        vec![ // 4
            (2*vlen + D*i + 1, field.neg_one()),
            (2*vlen + D*i + 3, field.one()),
            (2*vlen + D*i + 5, field.neg_one()),
            (2*vlen + D*i + 7, field.one()),
            (2*vlen + D*i + 9, field.one()),
            (2*vlen + D*i + 11, field.one()),
            (2*vlen + D*i + 13, field.one()),
            (2*vlen + D*i + 15, field.one()),
            (4*vlen + 22*(i+1) + 1, inthom.map(-2)), // 12
            (4*vlen + 22*(i+1) + 4, inthom.map(2)), // 13
            (4*vlen + 22*(i+1) + 5, inthom.map(2)),
            (4*vlen + 22*(i+1) + 8, inthom.map(-2)), // 14
            (4*vlen + 22*(i+1) + 9, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 12, inthom.map(-2)), // 23
            (4*vlen + 22*(i+1) + 13, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 16, inthom.map(2)), // 24
            (4*vlen + 22*(i+1) + 17, inthom.map(2)),
            (4*vlen + 22*(i+1) + 20, inthom.map(-2)), // 34
            (4*vlen + 22*(i+1) + 21, inthom.map(-2)),
        ],
        vec![ // 5
            (2*vlen + D*i + 0, field.neg_one()),
            (2*vlen + D*i + 1, field.clone_el(&dtmp)),
            (2*vlen + D*i + 2, field.neg_one()),
            (2*vlen + D*i + 3, field.clone_el(&dtmp)),
            (2*vlen + D*i + 4, field.one()),
            (2*vlen + D*i + 5, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 6, field.one()),
            (2*vlen + D*i + 7, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 8, field.one()),
            (2*vlen + D*i + 9, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 10, field.one()),
            (2*vlen + D*i + 11, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 12, field.one()),
            (2*vlen + D*i + 13, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 14, field.one()),
            (2*vlen + D*i + 15, field.clone_el(&dtmpneg)),
            (4*vlen + 22*(i+1) + 0, inthom.map(2)), // 12
            (4*vlen + 22*(i+1) + 2, inthom.map(-2)), // 13
            (4*vlen + 22*(i+1) + 3, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 6, inthom.map(-2)), // 14
            (4*vlen + 22*(i+1) + 7, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 10, inthom.map(-2)), // 23
            (4*vlen + 22*(i+1) + 11, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 14, inthom.map(-2)), // 24
            (4*vlen + 22*(i+1) + 15, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 18, inthom.map(2)), // 34
            (4*vlen + 22*(i+1) + 19, field.mul_ref_fst(&d, inthom.map(2))),
        ],
        vec![ // 6
            (2*vlen + D*i + 1, field.neg_one()),
            (2*vlen + D*i + 3, field.neg_one()),
            (2*vlen + D*i + 5, field.one()),
            (2*vlen + D*i + 7, field.one()),
            (2*vlen + D*i + 9, field.one()),
            (2*vlen + D*i + 11, field.one()),
            (2*vlen + D*i + 13, field.one()),
            (2*vlen + D*i + 15, field.one()),
            (4*vlen + 22*(i+1) + 1, inthom.map(2)), // 12
            (4*vlen + 22*(i+1) + 4, inthom.map(-2)), // 13
            (4*vlen + 22*(i+1) + 5, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 8, inthom.map(-2)), // 14
            (4*vlen + 22*(i+1) + 9, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 12, inthom.map(-2)), // 23
            (4*vlen + 22*(i+1) + 13, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 16, inthom.map(-2)), // 24
            (4*vlen + 22*(i+1) + 17, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 20, inthom.map(2)), // 34
            (4*vlen + 22*(i+1) + 21, inthom.map(2)),
        ],
        vec![ // 7
            (2*vlen + D*i + 0, field.neg_one()),
            (2*vlen + D*i + 1, field.clone_el(&dtmp)),
            (2*vlen + D*i + 2, field.one()),
            (2*vlen + D*i + 3, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 4, field.one()),
            (2*vlen + D*i + 5, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 6, field.neg_one()),
            (2*vlen + D*i + 7, field.clone_el(&dtmp)),
            (2*vlen + D*i + 8, field.one()),
            (2*vlen + D*i + 9, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 10, field.one()),
            (2*vlen + D*i + 11, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 12, field.one()),
            (2*vlen + D*i + 13, field.clone_el(&dtmpneg)),
            (2*vlen + D*i + 14, field.one()),
            (2*vlen + D*i + 15, field.clone_el(&dtmpneg)),
            (4*vlen + 22*(i+1) + 0, inthom.map(-2)), // 12
            (4*vlen + 22*(i+1) + 2, inthom.map(-2)), // 13
            (4*vlen + 22*(i+1) + 3, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 6, inthom.map(2)), // 14
            (4*vlen + 22*(i+1) + 7, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 10, inthom.map(2)), // 23
            (4*vlen + 22*(i+1) + 11, field.mul_ref_fst(&d, inthom.map(2))),
            (4*vlen + 22*(i+1) + 14, inthom.map(-2)), // 24
            (4*vlen + 22*(i+1) + 15, field.mul_ref_fst(&d, inthom.map(-2))),
            (4*vlen + 22*(i+1) + 18, inthom.map(-2)), // 34
            (4*vlen + 22*(i+1) + 19, field.mul_ref_fst(&d, inthom.map(-2))),
        ],
        vec![ // 8
            (2*vlen + D*i + 1, field.neg_one()),
            (2*vlen + D*i + 3, field.one()),
            (2*vlen + D*i + 5, field.one()),
            (2*vlen + D*i + 7, field.neg_one()),
            (2*vlen + D*i + 9, field.one()),
            (2*vlen + D*i + 11, field.one()),
            (2*vlen + D*i + 13, field.one()),
            (2*vlen + D*i + 15, field.one()),
            (4*vlen + 22*(i+1) + 1, inthom.map(-2)), // 12
            (4*vlen + 22*(i+1) + 4, inthom.map(-2)), // 13
            (4*vlen + 22*(i+1) + 5, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 8, inthom.map(2)), // 14
            (4*vlen + 22*(i+1) + 9, inthom.map(2)),
            (4*vlen + 22*(i+1) + 12, inthom.map(2)), // 23
            (4*vlen + 22*(i+1) + 13, inthom.map(2)),
            (4*vlen + 22*(i+1) + 16, inthom.map(-2)), // 24
            (4*vlen + 22*(i+1) + 17, inthom.map(-2)),
            (4*vlen + 22*(i+1) + 20, inthom.map(-2)), // 34
            (4*vlen + 22*(i+1) + 21, inthom.map(-2)),
        ],
    ]));
    Cdata.extend((0..(numrows-actrows)).map(|_| vec![]));

    let A = SparseMatrixMul::new(field, numcols, Adata, format!("iso{}D_A", D).as_str());
    let B = SparseMatrixMul::new(field, numcols, Bdata, format!("iso{}D_B", D).as_str());
    let C = SparseMatrixMul::new(field, numcols, Cdata, format!("iso{}D_C", D).as_str());

    println!("m: {actrows}");
    println!("n: {actcols}");
    println!("nz: {}", A.nonzero_entries() + B.nonzero_entries() + C.nonzero_entries());

    (z, R1CS::new(A, B, C))
}


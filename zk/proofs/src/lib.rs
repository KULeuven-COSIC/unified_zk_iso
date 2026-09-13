#![feature(allocator_api)]

#![feature(generic_const_exprs)]

#![feature(vec_into_chunks)]

#![feature(trusted_len)]

#![allow(incomplete_features)]

#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

pub mod util;

pub mod multilinear;

pub mod codes;

pub mod commit;

pub mod r1cs;

pub mod lattice;


pub type FSRng = rand::rngs::StdRng;
// pub type FSRng = rand::rngs::ThreadRng;


# Proof of knowledge of isogenies

Code accompanying the paper "A Simple and Unified Approach for Proving
Knowledge of Isogenies between Abelian Varieties". We refer to the paper for a
more detailed explanation of of the functionalities of the code.

The code is split into two main chunks.

## Transcript generation

The `transcript/` folder contains code for generating the isogeny relations in
different dimensions. The code is structured as follows:

- `dim1/`: contains an adaptation of the dimension 1 code from
  [two-isogenies](https://github.com/ThetaIsogenies/two-isogenies);
- `dim2/`: contains an adaptation of the dimension 2 code from
  [ThetaCGL](https://github.com/GiacomoPope/ThetaCGL);
- `dim4/`: contains an adaptation of the dimension 4 code from
  [qt-Pegasis](https://github.com/KULeuven-COSIC/qt-pegasis).

In all three cases, running `sage main.py` generates a `zk_radical.txt` file
that constitutes the input for the zero knowledge protocols. The folders also
contain a file `check_eq.py`. Running `sage check_eq.py` checks that
`zk_radical.txt` satisfies the hadamard - square relations.

The folder `transcript/cryptanalysis` contains the experiments and the
statistics concerning Problem 2.

## ZK Proof

The `zk/` folder contains the proof system for proving the relations generated
above.

The underlying math library
[feanor-math](https://github.com/FeanorTheElf/feanor-math) relies on
[mpir](https://github.com/wbhart/mpir) for fast arbitrary precision integer
arithmetic. It is recommended to install mpir before running benchmarks.

The code loads the corresponding transcript directly from the `transcript`
folder. It must thus be generated in advance with `sage main.py` in the
corresponding folder.

The different tests can be run with:
- dimension 1: `cargo test -r test_iso_pcs -- --no-capture`
- dimension 2: `cargo test -r test_cgl_pcs -- --no-capture`
- dimension 4: `cargo test -r test_iso4_pcs -- --no-capture`
- dimension 4 (lattice): `cargo test -r test_iso4D_sigma -- --no-capture`

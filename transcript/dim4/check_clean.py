from sage.all import *

from qt_pegasis import qtPegasis
import params

def Hadamard(P):
    H = hadamard_matrix(16)
    return list(H*vector(P))

if __name__ == "__main__":
    # Parameters setup

    lvl = '500'
    EGA = qtPegasis(lvl) # adding P for PEGASIS parameter set

    Fp2, i = GF(EGA.p**2, name="i", modulus=[1, 0, 1]).objgen()
    Fp = GF(EGA.p)

    V = VectorSpace(GF(2), 4)

    # Read transcript
    with open('zk_radical.txt', 'r') as fh:
        zk_radical = fh.read().strip()

    for idx, row in enumerate(zk_radical.split('\n')):
        exec(row)

        # Parse
        A = [
                a0, a1, a2, a3, a4, a5, a6, a7,
                a8, a9, a10, a11, a12, a13, a14, a15
        ]
        A = [Fp(c) for c in A]

        # First step
        if idx == 0:
            A_prev = A
            continue

        H_A = Hadamard(A)
        HS_A_prev = Hadamard([c**2 for c in A_prev])

        for y_i, x_i_prev in zip(H_A, HS_A_prev):
            assert y_i**2 == x_i_prev

        A_prev = A

    print('Ok')


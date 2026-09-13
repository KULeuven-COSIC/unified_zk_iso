from sage.all import *

from qt_pegasis import qtPegasis
from theta_lib.pkg.basis_change.base_change_dim4 import (
        base_change_theta_dim4, is_symplectic_matrix_dim4)
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
        P = [
                p0, p1, p2, p3, p4, p5, p6, p7,
                p8, p9, p10, p11, p12, p13, p14, p15
        ]
        P = [Fp(c) for c in P]

        # First step
        if idx == 0:
            A_prev = A
            P_prev = P
            continue

        H_A = Hadamard(A)
        HS_A_prev = Hadamard([c**2 for c in A_prev])
        H_P = Hadamard(P)
        HS_P_prev = Hadamard([c**2 for c in P_prev])

        for y_i, x_i_prev in zip(H_A, HS_A_prev):
            assert y_i**2 == x_i_prev

        for p_i, a_i, p_i_prev in zip(H_P, H_A, HS_P_prev):
            assert p_i*a_i == p_i_prev

        A_prev = A
        P_prev = P

    # Public splitting data. The theta-coordinate matrix N is reconstructed
    # from the underlying symplectic basis change.
    M_split = Matrix(Integers(4), 8, 8, [
            m0, m1, m2, m3, m4, m5, m6, m7,
            m8, m9, m10, m11, m12, m13, m14, m15,
            m16, m17, m18, m19, m20, m21, m22, m23,
            m24, m25, m26, m27, m28, m29, m30, m31,
            m32, m33, m34, m35, m36, m37, m38, m39,
            m40, m41, m42, m43, m44, m45, m46, m47,
            m48, m49, m50, m51, m52, m53, m54, m55,
            m56, m57, m58, m59, m60, m61, m62, m63
    ])
    assert is_symplectic_matrix_dim4(M_split) #Necessary for verifier to CHECK, but not in zero-knowledge, since M_split is public

    e4 = Fp2(e4)
    # assert e4**2 == -1
    N = base_change_theta_dim4(M_split, e4)

    product_null = [
            s0, s1, s2, s3, s4, s5, s6, s7,
            s8, s9, s10, s11, s12, s13, s14, s15
    ]
    product_null = vector(Fp2, product_null)

    #This MUST be checked in zero-knowledge (product_null is public, but A is of course not)
    assert N*vector(Fp2, A) == product_null

    factor = ZZ(factor)
    zidx = ZZ(zidx)
    qidx = ZZ(qidx)
    #assert factor in (0, 1)
    mask = 2**factor
    #assert 0 <= zidx < 16 and zidx & mask == 0
    #assert 0 <= qidx < 16 and qidx & mask == 0

    # Only the two public rows selecting the claimed elliptic factor are
    # needed to prove that q is the projection of the terminal point onto it.
    terminal_point = vector(Fp2, P)
    projected_point = [
            sum(N[row, j]*terminal_point[j] for j in range(16))
            for row in (qidx, qidx + mask)
    ]
    null_factor = [Fp2(z0), Fp2(z1)]
    point_factor = projected_point

    #Unsure if this must be checked in zero knowledge, or if the previous check is sufficient?
    assert null_factor == [product_null[zidx], product_null[zidx + mask]]

    #This must be checked in zero knowledge (recall: here both nz and point_factor is secret)
    determinant = (point_factor[0]*null_factor[1] - point_factor[1]*null_factor[0])
    assert Fp2(nz)*determinant == 1

    print("Success!")

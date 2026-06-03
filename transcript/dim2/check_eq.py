from sage.all import *

if __name__ == "__main__":
    # Parameters setup
    p = 2**127 - 1
    Fp2, i = GF(p**2, name="i", modulus=[1, 0, 1]).objgen()

    # Read transcript
    with open('zk_radical.txt', 'r') as fh:
        zk_radical = fh.read().strip()

    for idx, row in enumerate(zk_radical.split('\n')):
        exec(row)
        if idx == 0:
            a0_prev, a1_prev, a2_prev, a3_prev = a0, a1, a2, a3
            continue

        # Define the checks as (LHS, RHS, description)
        old1 = a0_prev**2 + a1_prev**2 + a2_prev**2 + a3_prev**2
        old2 = a0_prev**2 - a1_prev**2 + a2_prev**2 - a3_prev**2
        old3 = a0_prev**2 + a1_prev**2 - a2_prev**2 - a3_prev**2
        old4 = a0_prev**2 - a1_prev**2 - a2_prev**2 + a3_prev**2

        new1 = (a0 + a1 + a2 + a3)**2
        new2 = (a0 - a1 + a2 - a3)**2
        new3 = (a0 + a1 - a2 - a3)**2
        new4 = (a0 - a1 - a2 + a3)**2

        assert old1 == new1
        assert old2 == new2
        assert old3 == new3
        assert old4 == new4

        a0_prev, a1_prev, a2_prev, a3_prev = a0, a1, a2, a3

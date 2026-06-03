from sage.all import *

import params

if __name__ == "__main__":
    # Parameters setup
    p = params.set_params(0)
    Fp2, i = GF(p**2, name="i", modulus=[1, 0, 1]).objgen()

    # Read transcript
    with open('zk_radical.txt', 'r') as fh:
        zk_radical = fh.read().strip()

    exec(zk_radical)

    for idx, A_i in enumerate(A_is):
        if idx == 0:
            A_i_prev = A_i
            continue
        a0, a1 = A_i
        a0_prev, a1_prev = A_i_prev

        assert (a0 + a1)**2 == a0_prev**2 + a1_prev**2
        assert (a0 - a1)**2 == a0_prev**2 - a1_prev**2

        A_i_prev = A_i

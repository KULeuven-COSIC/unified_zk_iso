from time import time

from sage.all import *
proof.all(False)

from sos import sum_of_squares

def _find_st(N, max_k, r, two_lam_inv, e, stats = False):
    """
    Find valid solutions (s, t) to s + ct = v(2*lambda)^-1 mod N.
    Input:
    - N: norm of frak_a
    - max_c: starting value (upper bound) for c
    - r: n(alpha)/N, where frak_a = (N, alpha)
    - two_lam_inv: (2*lambda)^-1 mod N, where alpha = lambda + pi/2
    - e: exponent of 2 in the norm equation
    - stats: if True, return the number of total tries

    Output:
    - c, (s, t) such that s + ct = (2^e - (1+c^2)r)(2*lambda)^-1 mod N
    """

    M = 2**e
    k = max_k
    ksq = k**2
    bound = floor(max_k*sqrt(M/N - ksq/4))

    num_tries = 0
    v = (M - (1 + ksq)*r) % N
    v = -two_lam_inv*v

    r_two_lam_inv = r*two_lam_inv
    t1 = -((2*k - 1)*r_two_lam_inv) % N
    two_r_two_lam_inv = 2*r_two_lam_inv

    N_even = (N % 2 == 0)

    for _ in range(10000000):
        num_tries += 1
        k -= 1
        #V = [-k, 1] is one short vector
        #W = [N-kx, x] is the other one

        #Compute v, should be small
        v = (v + t1) % N
        t1 = (t1 + two_r_two_lam_inv) % N
        #assert T == -two_lam_inv*(M - (1 + d*d)*r) % N #Sick
        if N_even and k % 2 == 0:
            continue

        if v < bound:
            ksq = k**2
            xV = ZZ(round((-k*v)/(ksq + 1)))
            s, t = (-xV*k - v, xV)

            if stats:
                yield k, (-xV*k - v, xV), v, num_tries
            else:
                yield k, (-xV*k - v, xV), v

    raise RuntimeError('Find alpha failed :(')

def fix_coeff(delta_1, delta_2, N, z):
    """
    Pre check on the coefficients to avoid singular cases before cornacchia
    """
    # s1 -> B1 + D1 = 2 mod 4
    # s2 -> B1 + B2 + D1 + D2 = 2 mod 4
    # s3 -> C1 - E1 = 2 mod 4
    # s4 -> C1 + C2 - E1 - E2 = 2 mod 4

    _D1, _D2 = delta_1 * delta_2.conjugate() / N # c1bar_c2
    D1, D2 = _D1 - _D2, 2*_D2
    _C1, _C2 = delta_2.conjugate() # c2_b1bar (multiply later with b1)
    C1, C2 = _C1 - _C2, 2*_C2
    _E1, _E2 = delta_1.conjugate() # b2bar_c1 (multiply later with b2)
    E1, E2 = _E1 - _E2, 2*_E2

    if N % 2 == 0:
        # TODO figure out if we have some requirements in this case
        return True, (1, C1, C2, D1, D2, E1, E2)

    if z % 8 == 1:
        # b2 == 0 mod 4
        if D1 % 4 == 2:
            return False, 1
        if (D1 + D2) % 4 == 2:
            return False, 2
        # if C1 % 4 == 2:
        #   return False, 3
        # if (C1 + C2) % 4 == 2:
        #   return False, 4

    elif z % 8 == 5:
        # b2 == 2 mod 4
        if D1 % 4 == 0:
            return False, 1
        if (D1 + D2) % 4 == 0:
            return False, 2
        # if (C1 - 2*E1) % 4 == 2:
        #    return False, 3
        # if (C1 + C2 - 2*(E1 + E2)) % 4 == 2:
        #    return False, 4
    else:
        # z%8 == 2 -> b2 odd
        # Two possibilities for (b1, b2) % 4
        # Case 1: (1, 1)
        if not 2 in [
            (N + D1) % 4, (N + D1 + D2) % 4,
            (C1 - E1) % 4, (C1 + C2 - E1 - E2) % 4]:
            return True, (1, C1, C2, D1, D2, E1, E2)
        # Case 2: (1, -1)
        if not 2 in [
            (-N + D1) % 4, (-N + D1 + D2) % 4,
            (C1 + E1) % 4, (C1 + C2 + E1 + E2) % 4]:
            return True, (2, C1, C2, D1, D2, E1, E2)
        return False, 3
    return True, (0, C1, C2, D1, D2, E1, E2)

def qlapoti(frak_a, e, stats=False):
    """
    Algorithm for solving the norm equation N1 + N2 = 2^e.

    Input:
    - frak_a = (ell, omega - lambda) an ideal represented as two elements
      in Z[omega]; we assume ell to be smaller than sqrt(p), so that the
      ideal is (close) to reduced and we can use it directly
    - e: target exponent of 2 for the norm equation
    - stats: if True, compute and return statistics instead of the actual
      solution

    Output:
    - A1, A2 generating frak_c1_bar * frak_b1
    - B1, B2 generating frak_b2_bar * frak_b1
    - C1, C2 generating frak_c2 * frak_c1_bar
    - D1, D2 generating frak_c1_bar * frak_c2
    - E1, E2 generating frak_b2_bar * frak_c1
    - N1 = frak_b1.norm() + frak_c1.norm()
    - N2 = frak_b2.norm() + frak_c2.norm()
    - Nb1 = frak_b1.norm()
    """
    num_tries = 0
    data = {
        'alpha_tries':0, # Tries of _find_alpha
        'z':0, # Number of times z<0
        '3m4':0, # z is 3 mod 4
        'even':0, # Retry to avoid even norms
        'prod':0, # Retry to avoid products
        'er_1_1':0, # Singular case, z = 1 mod 8, case 1
        'er_1_2':0, # case 2
        'er_5_1':0, # z = 5 mod 8
        'er_5_2':0,
        'er_2_3':0,
        'sos':0, # Failed sum of squares
    }

    N, alpha = frak_a
    p = -(alpha.parent().discriminant())

    assert N % 4 != 2, "N is 2 mod 4, so you must act with a single 2-isogeny first"

    tr_alpha, pi_coeff = list(alpha)

    # Choose sign of trace positive
    if tr_alpha < 0:
        alpha = -alpha
        tr_alpha = -tr_alpha
        #pi_coeff = -pi_coeff
    # assert abs(pi_coeff) == 1/2, f"k_coeff was {pi_coeff}" this is not a problem
    tr_alpha = 2*tr_alpha

    assert tr_alpha % 2 == 1

    n_alpha = alpha.norm()
    tr_alpha_inv = ZZ(inverse_mod(ZZ(tr_alpha), N))
    r = ZZ(n_alpha/N)
    two_e = 2**e

    # Try to find a good lattice
    max_k = floor(isqrt(N * 2**(e-2) / p))

    for output in _find_st(N, max_k, r, tr_alpha_inv, e, stats):
        if stats:
            k, (s, t), v, tries = output
            data["alpha_tries"] = tries
        else:
            k, (s, t), v = output
        
        if N % 2 == 0:
            if k % 2 == 0 or s % 2 == r % 2 or t % 2 == r % 2:
                continue
        #Compared with the paper, v has a sign flip, hence the + tr_alpha*v
        _z = two_e - (1+k**2)*r + tr_alpha*v
        z = (_z // N) - s**2 - t**2

        if z < 0:
            data["z"] += 1
            continue
        if z % 4 == 3 or z % 8 == 6:
            data["3m4"] += 1
            continue

        # Skip frak_b1.norm() + frak_c1.norm() even for 4D
        delta_1 = s*N + alpha
        d1 = delta_1.norm()/N
        if N % 2 == 1:
            assert d1 % 2 == 0 # alpha = (pi - lambda)/2
        else:
            assert d1 % 2 == 1

        if z % 4 == 0:
            # b1 even + d1 even
            data['even'] += 1
            continue

        delta_2 = t*N + k*alpha

        if N % 2 == 0:
            assert delta_2.norm()/N % 2 == 1

        if z % 4 == 2:
            # Check to avoid products
            tt1, tt2 = delta_1 + delta_2
            if (tt1 + tt2) % 2 == 0:
                data['prod'] += 1
                continue
        
        out, state = fix_coeff(delta_1, delta_2, N, z)
        if not out:
            data[f'er_{z % 8}_{state}'] += 1
            continue

        b12 = sum_of_squares(z)

        if not b12:
            data['sos'] += 1
            continue

        #print("passed cornacchia!")

        # Solution found
        state, xC1, xC2, D1, D2, xE1, xE2 = state

        b1, b2 = b12
        if z % 4 == 1 and b1 % 2 == 0:
            b2, b1 = b1, b2

        if z % 8 == 2:
            # Impose conditions for later
            # b1 = 1 mod 4
            if b1 % 4 == 3:
                b1 = -b1
            # b2 = 1 mod 4 for (1) / 3 mod 4 for (2)
            if (state == 1 and b2 % 4 == 3) or \
                (state == 2 and b2 % 4 == 1):
                b2 = -b2

        d2 = delta_2.norm()/N

        # beta_1 = b1*N
        # beta_2 = b2*N
        # This line takes a lot the first time to call PARI
        # assert all([beta in frak_a for beta in [beta_1, beta_2, delta_1, delta_2]])
        # assert beta_1**2 + beta_2**2 + delta_1.norm() + delta_2.norm() == 2**e*N

        Nb1 = b1**2 * N # n(frak_b1)
        N1 = d1 + b1**2 * N # n(frak_b1) + n(frak_c1)
        N2 = d2 + b2**2 * N # n(frak_b2) + n(frak_c2)

        _A1, _A2 = delta_1 * b1 # c1bar_b1
        A1, A2 = _A1 - _A2, 2*_A2

        B1, B2 = b1 * b2 * N, 0 # b2bar_b1

        C1, C2 = b1*xC1, b1*xC2 # c2_b1bar
        E1, E2 = b2*xE1, b2*xE2 # b2bar_c1

        if N % 2 == 0:
            #Need to swap all the variables
            #For simplicity, we swap bfraki with cfraki_bar
            #Thus, we need to take the twist later!!
            Nb1 = d1
            E1, C1 = C1, E1
            E2, C2 = C2, E2

            B1, D1 = D1, B1
            B2, D2 = D2, B2

        assert 2 not in [
            (B1 + D1) % 4, (B1 + B2 + D1 + D2) % 4,
            (C1 - E1) % 4, (C1 + C2 - E1 - E2) % 4], "should never happen"

        break

    if stats:
        return data

    return A1, A2, B1, B2, C1, C2, D1, D2, E1, E2, N1, N2, Nb1

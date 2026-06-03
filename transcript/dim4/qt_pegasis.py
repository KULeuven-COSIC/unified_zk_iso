from time import time
import logging

from sage.all import *
proof.all(False)

from xonly import xPoint, random_xPoint, MontgomeryA, isWeierstrass, translate_by_T
from params import *
from norm_eq import qlapoti

from hd_helpers import ChainHelper
from theta_lib.pkg.basis_change.canonical_basis_dim1 import make_canonical
from theta_lib.pkg.theta_structures.Tuple_point import TuplePoint

logger = logging.getLogger(__name__)
logger.setLevel(logging.WARNING)
logger_sh = logging.StreamHandler()
formatter = logging.Formatter('%(name)s [%(levelname)s] %(message)s')
logger_sh.setFormatter(formatter)
logger.addHandler(logger_sh)

class qtPegasis:
    def __init__(self, level):
        r"""
        Main qt-Pegasis class. Takes as input the security level:
        - 500|1000|15000|2000|4000: qt-Pegasis parameters
        - 500P|1000P|1500P|2000P|4000P: PEGASIS parameters
        """
        logger.info('Initialization')
        _t0 = time()
        params = qt_params(level)
        self.f = params['f']
        self.e = params['e']
        self.p = self.f * 2**self.e - 1
        self.A = params['A']

        self.Fp = GF(self.p)
        self.Fp2 = GF((self.p, 2), name='i', modulus=var('x')**2 + 1)
        self.K = NumberField(name="pi", polynomial = var('x')**2 + self.p)
        self.pi = self.K.gens()[0]

        E_start = EllipticCurve(self.Fp, [0, self.A, 0, 1, 0])
        self.E_start = E_start

        self.e_sol = self.e - 3

        _t1 = time()
        logger.info(f' - Done in {_t1-_t0:.3f}s')
        logger.info('Precomputations')
        EE = E_start.change_ring(self.Fp2)

        # Loading basis from params (generated with pgen.py)
        self.P = EE([params['Px'], params['Py']])
        self.Q = EE([params['Qx'], self.Fp2([0, params['Qy']])])
        self.TP = EE([params['TPx'], 0])
        self.TQ = EE([params['TQx'], 0])
        self.P16 = EE([params['P16x'], params['P16y']])
        self.Q16 = EE([params['Q16x'], self.Fp2([0, params['Q16y']])])
        self.P16 = EE([params['P16x'], params['P16y']])
        self.Q16 = EE([params['Q16x'], self.Fp2([0, params['Q16y']])])
        self.S = EE([params['Sx'], self.Fp2([params['Sy'], params['Syi']])])
        self.R = EE([params['Rx'], self.Fp2([params['Ry'], params['Ryi']])])
        self.ePQ4 = self.Fp2([0, params['ePQ4']])
        _x, _y, _z, _w = params['_xyzw']

        M0 = Matrix(Integers(4),[
            [_x, 0, 0, 0, _y, 0, 0, 0], # (P, 0, 0, 0)
            [0, _x, 0, 0, 0, _y, 0, 0], # (0, P, 0, 0)
            [0, 0, _x, 0, 0, 0, _y, 0],
            [0, 0, 0, _x, 0, 0, 0, _y],
            [_z, 0, 0, 0, _w, 0, 0, 0], # (S, 0, 0, 0)
            [0, _z, 0, 0, 0, _w, 0, 0],
            [0, 0, _z, 0, 0, 0, _w, 0],
            [0, 0, 0, _z, 0, 0, 0, _w]
        ]).transpose()
        self.M0 = M0
        _t2 = time()
        logger.info(f' - Done in {_t2-_t1:.3f}s')

    def sage_action(self, frak_a, E=None, timings=False, ret_twist=False):
        """
        Compute the action of frak_a from E using qt-Pegasis.
        Wrapper that calls qt_action (which assumes the ideal is
        of a certain form, and reduced).
        Warning: sage structures may cause a significant slowdown especially at
        higher levels.

        Input:
        - frak_a = an instance of Sage's fractional_ideal class
        - E: an elliptic curve; if None, self.E_start is used instead
        - timings, ret_twist: qt_action flags

        Output:
        - `Ea`, the montgomery coefficient of the codomain curve
        """
        #print('Inside the sage part')
        if E:
            E_0 = E
        else:
            E_0 = self.E_start

        frak_a_reduced = frak_a.reduce_equiv()
        frak_a_red_gens = frak_a_reduced.gens()
        if len(frak_a_red_gens) == 1:
            return E_0

        N, alpha = frak_a_red_gens
        assert N == frak_a_reduced.norm()

        # 2-isogeny step
        tt0 = time()
        if ZZ(N) % 4 == 2:
            E_0 = self.two_isogeny(E_0, alpha)
            N //= 2
        tt1 = time()

        out = self.qt_action([ZZ(N), alpha], E=E_0, timings=timings,
                             ret_twist=ret_twist)

        if timings:
            E_a = EllipticCurve(self.Fp, [0, out[0], 0, 1, 0])
            return E_a, out[1]

        if ret_twist:
            return [EllipticCurve(self.Fp, [0, A, 0, 1, 0]) for A in out]

        return EllipticCurve(self.Fp, [0, out, 0, 1, 0])

    def qt_action(self, frak_a, E=None, timings=False, ret_twist=False):
        """
        Compute the action of frak_a from E using qt-Pegasis.

        Input:
        - frak_a = (ell, omega - lambda) an ideal represented as two elements
          in Z[omega]; we assume ell to be smaller than sqrt(p), so that the
          ideal is (close) to reduced and we can use it directly
        - E: an elliptic curve; if None, self.E_start is used instead
        - timings: if True, return an additional tuple (t1, t2, t3) with the
          timings of the corresponding steps
        - `ret_twist`: if True, return also Eabar

        Output:
        - `Ea`, the montgomery coefficient of the codomain curve
        """
        logger.info(f'Starting qt-Pegasis action')
        # Step 1: solve norm equation
        _t1 = time()

        A1, A2, B1, B2, C1, C2, D1, D2, E1, E2, N1, N2, Nb1 = qlapoti(
                frak_a, self.e_sol)

        # Step 2: compute basis
        # Step 2.1: Curve basis generation
        _t2 = time()
        logger.info(f'Step 1: {_t2-_t1:.3f}s')
        e_sol = self.e_sol

        if not E:
            E = self.E_start

        if E == self.E_start:
            P, Q = self.P, self.Q
            TP, TQ = self.TP, self.TQ
            P16, Q16 = self.P16, self.Q16
            ePQ4 = self.ePQ4
            R, S = self.R, self.S
            M0 = self.M0

        else:
            P, Q, TP, TQ = self.TwoTorsBasis(E, e_sol+2)

            # 4-torsion
            dt_two = 2**(e_sol-2)
            P16, Q16 = dt_two*P, dt_two*Q
            P4, Q4 = 4*P16, 4*Q16
            ePQ4 = P4.weil_pairing(Q4, 4)

            # Change of basis
            _, _, R, S, M0 = make_canonical(P4, Q4, 4, preserve_pairing=True)
            (_x, _y), (_z, _w) = M0
            # assert _x*R + _y*S == P4 and _z*R + _w*S == Q4
            M0 = Matrix(Integers(4),[
                [_x, 0, 0, 0, _y, 0, 0, 0], # (P, 0, 0, 0)
                [0, _x, 0, 0, 0, _y, 0, 0], # (0, P, 0, 0)
                [0, 0, _x, 0, 0, 0, _y, 0],
                [0, 0, 0, _x, 0, 0, 0, _y],
                [_z, 0, 0, 0, _w, 0, 0, 0], # (S, 0, 0, 0)
                [0, _z, 0, 0, 0, _w, 0, 0],
                [0, 0, _z, 0, 0, 0, _w, 0],
                [0, 0, 0, _z, 0, 0, 0, _w]
            ])
            M0 = M0.transpose()
        _t21 = time()
        logger.info(f'Step 2.1: {_t21 - _t2:.3f}s')

        # Step 2.2: 4D basis generation
        alpha = inverse_mod(N1, 2**(e_sol + 2))
        beta = inverse_mod(N2, 2**(e_sol + 2))
        q_cff = (1 - alpha*2**e_sol) % 2**(e_sol+2)
        s1 = (C1 - E1) % 2**(e_sol+2)
        s2 = (C1 + C2 - E1 - E2) % 2**(e_sol+2)
        s3 = (B1 + B2 + D1 + D2) % 2**(e_sol+2)
        s4 = (B1 + D1) % 2**(e_sol+2)
        s5 = (C2 - E2) % 2
        s6 = (B2 + D2) % 2

        M = Matrix(Integers(4), [
            [0,0,0,0,-alpha,0,0,0],
            [0,0,0,0,0,-alpha,0,0],
            [0,0,beta*s3,-beta*s1,0,0,0,0],
            [0,0,beta*s2, beta*s4,0,0,0,0],
            [N1,0,s3,-s1,0,0,0,0],
            [0,N1,s2,s4,0,0,0,0],
            [0,0,0,0,q_cff,0,alpha*s4,-alpha*s2],
            [0,0,0,0,0,q_cff,alpha*s1,alpha*s3]]).transpose()

        # Compute the compatible basis from [qt-Pegasis, Eq. (x), Section 4.y]
        OE = P.curve()(0)

        N1P = N1*P
        s5TP = s5*TP
        s6TP = s6*TP

        alphas1 = (alpha*s1) % 2**(e_sol+2)
        alphas2 = (alpha*s2) % 2**(e_sol+2)
        alphas3 = (alpha*s3) % 2**(e_sol+2)
        alphas4 = (alpha*s4) % 2**(e_sol+2)
        q_cffQ=q_cff*Q
        alphas5TQ = s5*TQ # alpha = 1 mod 2
        alphas6TQ = s6*TQ # alpha = 1 mod 2

        T1 = TuplePoint(N1P,OE,s3*P+s6TP,-s1*P+s5TP)
        T2 = TuplePoint(OE, N1P, s2*P+s5TP,s4*P-s6TP)
        T3 = TuplePoint(q_cffQ,OE,alphas4*Q+alphas6TQ,-alphas2*Q+alphas5TQ)
        T4 = TuplePoint(OE,q_cffQ,alphas1*Q+alphas5TQ,alphas3*Q-alphas6TQ)

        # Basis mod 16
        N1P_16 = N1*P16

        alphas1_16 = (alpha*s1) % 16
        alphas2_16 = (alpha*s2) % 16
        alphas3_16 = (alpha*s3) % 16
        alphas4_16 = (alpha*s4) % 16
        q_cffQ_16=(q_cff % 16)*Q16

        T1_16 = TuplePoint(N1P_16,OE,(s3%16)*P16,-(s1%16)*P16)
        T2_16 = TuplePoint(OE, N1P_16, (s2%16)*P16,(s4%16)*P16)
        T3_16 = TuplePoint(q_cffQ_16,OE,alphas4_16*Q16,-alphas2_16*Q16)
        T4_16 = TuplePoint(OE,q_cffQ_16,alphas1_16*Q16,alphas3_16*Q16)

        # Splitting change of basis
        A3 = (A1 + A2) % 4
        t = inverse_mod(Nb1,4)
        mu = inverse_mod(Nb1**2+A1*A3,4)
        nu = inverse_mod(1+t**2*A1*A3,4)

        M2 = Matrix(Integers(4), [[0,0,0,0,-Nb1*N1*mu,A3*N1*mu,0,0],
            [0,0,0,0,-A1*N1*mu,-Nb1*N1*mu,0,0],
            [0,0,alpha*N2,0,0,0,0,0],
            [0,0,0,alpha*N2,0,0,0,0],
            [nu,-t*A1*nu,-alpha*N2,0,0,0,0,0],
            [t*A3*nu,nu,0,-alpha*N2,0,0,0,0],
            [0,0,0,0,Nb1*N1*mu,-A3*N1*mu,beta*N1,0],
            [0,0,0,0,A1*N1*mu,Nb1*N1*mu,0,beta*N1]])

        # Step 3: 4D isogeny
        _t3 = time()
        logger.info(f'Step 2.2: {_t3-_t21:.3f}s')

        Phi = ChainHelper(e_sol,
                (T1, T2, T3, T4), (T1_16, T2_16, T3_16, T4_16), (R, S),
                M0 * M, (P, Q), ePQ4, M2)

        _t4 = time()
        logger.info(f'Step 3: {_t4-_t3:.3f}s')
        logger.info(f'qt-Pegasis action: {_t4 - _t1:.3f}s')

        # If N is even, we have acted with the conjugate
        if frak_a[0] % 2 == 0:
            Phi.Ea, Phi.Eabar = Phi.Eabar, Phi.Ea

        if timings:
            return Phi.Ea, (_t2-_t1, _t21-_t2, _t3-_t21, _t4-_t3)

        if ret_twist:
            return Phi.Ea, Phi.Eabar
        return Phi.Ea

    def sample_ideal(self):
        r"""
        Samples a random ideal frak_ell = (ell, omega + lambda) with ell a
        random prime slightly smaller than sqrt(p), so that the sampled ideal
        is (close to) reduced
        """
        ub = isqrt(self.p)//2

        ell = next_prime(randint(0, ub))
        while kronecker(-self.p, ell) != 1:
            ell = next_prime(ell)

        Fl = GF(ell)
        x = Fl.polynomial_ring().gens()[0]
        lam = (x**2 + x + Fl(self.p+1)/4).any_root()
        b2 = (1 - self.pi)/2 + ZZ(lam)
        if (b2-ell).norm() < b2.norm():
            b2 -= ell

        frak_ell = (ell, b2)
        # frak_ell = self.max_order*ell + self.max_order*b2
        return frak_ell

    def sample_sage_ideal(self):
        r"""
        Samples a random ideal, as an instance of Sage's 
        fractional ideal class
        """
        X = polygen(QQ)
        O_K = self.K.maximal_order()
        ell = next_prime(randint(0, self.p))
        while kronecker(-self.p, ell) != 1:
            ell = next_prime(ell)
        frak_a = factor(O_K.fractional_ideal(ell))[0][0]

        assert frak_a.norm() == ell
        return frak_a

    def TwoTorsBasis(self, E, e):
        r"""
        Fast sampling of a basis P, Q of E[2**e], such that x(P) and x(Q) are both defined over Fp
        Input:
            - E: Elliptic curve over Fp
            - e: Exponent
        Output:
            - P, Q: Basis of E[2**e] so that P is in E(Fp), and Q is in E^t(Fp) for an Fp-twist of E.
            - TP, TQ: 2-torsion points output of `eval_omega_and_lift`
        """
        _t0 = time()

        T0, Tm1, T1 = self.find_Ts(E)

        A = MontgomeryA(E)
        F =  E.base_field()
        R = F["X"]
        X = R.gens()[0]
        f = X**2 + A*X + 1

        _t1 = time()
        logger.debug(f'\t- Finding two torsion basis: {_t1 - _t0:.3f}s')

        xT0 = T0.x()
        xP = xT0 + F.random_element()**2
        while not (f(xP)*xP).is_square() or (xP-Tm1.x()).is_square():
            xP = xT0 + F.random_element()**2

        xQ = xT0 - F.random_element()**2
        while (f(xQ)*xQ).is_square() or not ((xQ-T1.x()).is_square()):
            xQ = xT0 - F.random_element()**2

        _t2 = time()
        logger.debug(f'\t- Sample xP and xQ: {_t2 - _t1:.3f}s')

        P = xPoint(xP, E)
        Q = xPoint(xQ, E)

        assert (self.p+1) % 2**(e+1) == 0
        cofac = (self.p+1)/2**(e+1)
        P = P.xMUL(cofac)
        Q = Q.xMUL(cofac)

        assert P.xMUL(2**(e-1))
        assert not P.xMUL(2**e)
        assert Q.xMUL(2**(e-1))
        assert not Q.xMUL(2**e)
        assert Q.xMUL(2**(e-1)) != P.xMUL(2**(e-1))

        P, Q, TP, TQ = self.eval_omega_and_lift(E, P, Q, T0, Tm1, T1)
        _t3 = time()
        logger.debug(f'\t- Lift: {_t3 - _t2:.3f}s')
        return P, Q, TP, TQ

    def eval_omega_and_lift(self,E, P, Q, T0, Tm1, T1):
        r"""
        [Pegasis, Algorithm 4] Finds T_P, T_Q\in E[2] such that 
        omega(P)=P+T_P and omega(Q)=T_Q.
        Input:
        - E: Elliptic curve over Fp.
        - P, Q: basis of E[2**(e-1)] (defined in x-only arithmetic over Fp).
        - T0, Tm1, T1: points of E[2] obtained from find_Ts (full Fp-points).
        [Pegasis, Lemma D.1]. 
        Output:
        - Plift, Qlift: full lifts of P, Q over Fp2.
        - TP, TQ: such that omega(P)=P+T_P and omega(Q)=T_Q.
        """

        Plift = E.lift_x(P.X)

        mu1 = Tm1.tate_pairing(Plift,2,1)
        mu2 = T1.tate_pairing(Plift,2,1)

        if mu1 == 1 and mu2 == 1:
            TP = E(0)
        elif mu1 == -1 and mu2 == 1:
            TP = T1
        elif mu1 == 1 and mu2 == -1:
            TP = Tm1
        elif mu1 == -1 and mu2 == -1:
            TP = T0
        else:
            raise ValueError("Wrong Tate pairing P.")

        A = MontgomeryA(E)
        F =  E.base_field()
        Et = EllipticCurve(F,[0,-A,0,1,0])

        #T0t = Et(-T0.x(),0)
        Tm1t = Et(-T1.x(),0)
        T1t = Et(-Tm1.x(),0)

        Qliftt = Et.lift_x(-Q.X)

        mu1 = Tm1t.tate_pairing(Qliftt,2,1)
        mu2 = T1t.tate_pairing(Qliftt,2,1)

        if mu1 == 1 and mu2 == 1:
            TQ = E(0)
        elif mu1 == -1 and mu2 == 1:
            TQ = Tm1
        elif mu1 == 1 and mu2 == -1:
            TQ = T1
        elif mu1 == -1 and mu2 == -1:
            TQ = T0
        else:
            raise ValueError("Wrong Tate pairing Q.")

        EE = E.change_ring(self.Fp2)
        ii = self.Fp2.gen()
        Qlift = EE(-Qliftt.x(),-ii*Qliftt.y())
        Plift = EE(Plift)
        TP = EE(TP)
        TQ = EE(TQ)

        return Plift, Qlift, TP, TQ

    def find_Ts(self, E, only_T0 = False):
        r"""
        Given a curve E, finds and marks the non-trivial
        2-torsion points according to Lemma D.1
        """
        A = MontgomeryA(E)
        F =  E.base_field()
        R = F["X"]
        X = R.gens()[0]
        f = X**2 + A*X + 1
        lam1, lam2 = f.roots(multiplicities=False)

        R1 = E(lam1, 0)
        R2 = E(lam2, 0)
        R3 = E(0, 0)

        #Find T0
        Rs = [R1, R2]
        for T in Rs:
            if T.tate_pairing(T, 2, 1) != 1:
                T0 = T
                Rs.remove(T)
                break

        assert T0
        if only_T0:
            return T0

        assert T0.tate_pairing(T0, 2, 1) == -1
        Rs.append(R3)
        for T in Rs:
            if T.tate_pairing(T0, 2, 1) == 1:
                Tm1 = T
                Rs.remove(T)
                break

        assert Tm1
        T1 = Rs[0]
        assert T1.tate_pairing(T0, 2, 1) != 1

        return T0, Tm1, T1

    def two_isogeny(self, E, alpha):
        r""" Helper for annoying special case
        Given E, and alpha, computes a * E,
        where a = (2, alpha)"""

        T0, Tm1, T1 = self.find_Ts(E)
        a, b = list(alpha)
        # See appendix D, PEGASIS
        if (a + b) % 2 == 1:
            #print("m1")
            K = Tm1
        else:
            #print("p1")
            K = T1
        return E.isogeny(K).codomain().montgomery_model()



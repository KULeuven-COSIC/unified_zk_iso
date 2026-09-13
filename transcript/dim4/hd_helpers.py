from time import time
import itertools as itt
import logging

from sage.all import *

from theta_lib.pkg.theta_structures.theta_helpers_dim4 import hadamard
from theta_lib.pkg.theta_structures.Tuple_point import TuplePoint
from theta_lib.pkg.theta_structures.montgomery_theta import null_point_to_montgomery_coeff
from theta_lib.pkg.theta_structures.Theta_dim1 import (
        ThetaPointDim1, ThetaStructureDim1)
from theta_lib.pkg.theta_structures.Theta_dim2 import (
        ThetaPointDim2, ProductThetaStructureDim2)
from theta_lib.pkg.theta_structures.Theta_dim4 import ProductThetaStructureDim2To4
from theta_lib.pkg.basis_change.base_change_dim4 import base_change_theta_dim4
from theta_lib.pkg.isogenies.isogeny_chain_dim4 import IsogenyChainDim4
from theta_lib.pkg.isogenies.gluing_isogeny_dim4 import GluingIsogenyDim4

logger = logging.getLogger(__name__)
logger.setLevel(logging.WARNING)
logger_sh = logging.StreamHandler()
formatter = logging.Formatter('%(name)s [%(levelname)s] %(message)s')
logger_sh.setFormatter(formatter)
logger.addHandler(logger_sh)

class ChainHelper:
    """
    General 4D isogeny wrapper for `theta_lib`
    """

    def __init__(self, e, T, T16, B, M, BPQ, ePQ4, M2):
        """
        Input:
        - e: the total number of (2*)-steps
        - T: 4 TuplePoints representing the T_i
        - T16: TuplePoints for the T_i mod 16
        - B: Canonical basis (R, S) on E[4]
        - M: Change of coordinates from B^4 to (S, T)
        - BPQ: basis (P, Q) of E[4*2^e]
        - ePQ4: 4-Weil Pairing between P4 and Q4 (4-torsion of P,Q)
        - M2: splitting change of basis matrix
        """
        # Gluing
        tt0 = time()
        glue_4d = GlueHelper(e, T16, B, M, BPQ, ePQ4)
        tt1 = time()
        logger.info(f'\t- Gluing: {tt1-tt0:.3f}s')

        # Chain
        Phi = IsogenyChainDim4(
                T, glue_4d, e, 1,
                splitting=True, strategy=None)

        self.isogeny = Phi

        tt2 = time()
        logger.info(f'\t- Chain: {tt2-tt1:.3f}s for {e = }')
        cod = Phi._isogenies[-1]._codomain

        #dom = Phi._isogenies[0]._domain
        #print(dom)

        # Splitting
        P, Q = BPQ

        # assert ePQ4 == P.weil_pairing(Q, 2**(e+2))**(2**e)
        N = base_change_theta_dim4(M2, ePQ4)
        codom_prod = cod.base_change_struct(N)

        self.N_split = N
        self.M_split = M2
        self.e4 = ePQ4
        self.codomain_product = codom_prod

        thetaA, thetaB = find_product_4(codom_prod.null_point())
        a1, b1 = thetaA[0], thetaA[2]
        a2, b2 = thetaA[0], thetaA[1]

        A1 = null_point_to_montgomery_coeff(a1, b1)
        A2 = null_point_to_montgomery_coeff(a2, b2)

        Fp = A1.parent().base()
        if Fp(A2 + 2).is_square():
            A2 = -A2
        if Fp(A1 + 2).is_square():
            A1 = -A1
        self.Ea = A2
        self.Eabar = A1
        tt3 = time()
        logger.info(f'\t- Splitting: {tt3-tt2:.3f}s')

    def _normalize_auxiliary(self, P, P_prev, null_point):
        """
        Scale P so that the point evaluation formula holds affinely.
        """
        H_P = hadamard(P.coords())
        H_null = hadamard(null_point.coords())
        HS_P_prev = hadamard([c**2 for c in P_prev.coords()])

        scale = None
        for h_p, h_null, hs_p_prev in zip(H_P, H_null, HS_P_prev):
            if h_p*h_null != 0:
                scale = hs_p_prev/(h_p*h_null)
                break
        assert scale is not None

        P = P.scale(scale)
        H_P = hadamard(P.coords())
        for h_p, h_null, hs_p_prev in zip(H_P, H_null, HS_P_prev):
            assert h_p*h_null == hs_p_prev

        return P

    def evaluate_auxiliary(self, P):
        """
        Evaluate P and return one theta point for every null point in the
        transcript.
        """
        first_isogenies = self.isogeny._isogenies[0]

        P, Q = first_isogenies.eval_gluing(P, return_domain=True)
        points = [P]

        null_point = first_isogenies.glue_4d._codomain.null_point()
        Q = self._normalize_auxiliary(Q, P, null_point)
        points.append(Q)

        P = Q
        Q = first_isogenies.second_isogeny(P)
        null_point = first_isogenies.second_isogeny._codomain.null_point()
        Q = self._normalize_auxiliary(Q, P, null_point)
        points.append(Q)

        for phi in self.isogeny._isogenies[1:]:
            P = Q
            Q = phi(P)
            null_point = phi._codomain.null_point()
            Q = self._normalize_auxiliary(Q, P, null_point)
            points.append(Q)

        return points

    def write_auxiliary_transcript(self, points, factor=0):
        """
        Add the auxiliary theta coordinates to the null-point transcript and
        prove that the selected embedded isogeny does not map the auxiliary
        point to zero.
        """
        assert factor in (0, 1)

        with open('zk_radical.txt', 'r') as fh:
            transcript = fh.read().strip().split('\n')

        assert len(transcript) == len(points)
        for idx, P in enumerate(points):
            coords = P.coords()
            transcript[idx] += ';'.join(
                    f'p{j}={coords[j]}' for j in range(len(coords))) + ';'

        null_point = self.codomain_product.null_point().coords()
        P = self.codomain_product.base_change_coords(
                self.N_split, points[-1])

        null_index, null_factor = product_factor_slice(null_point, factor)
        point_index, point_factor = product_factor_slice(P.coords(), factor)

        Fp = self.isogeny._isogenies[0].Fp
        null_factor = [Fp(c) for c in null_factor]
        point_factor = [Fp(c) for c in point_factor]
        # Two theta points of dimension one are equal precisely when this
        # projective determinant vanishes.
        determinant = (point_factor[0]*null_factor[1]
                - point_factor[1]*null_factor[0])
        nonzero_witness = 1/determinant

        transcript[-1] += ';'.join(
                f'z{j}={null_factor[j]}' for j in range(2)) + ';'
        transcript[-1] += f'nz={nonzero_witness};'
        transcript[-1] += f'factor={factor};'
        transcript[-1] += f'zidx={null_index};qidx={point_index};'
        # Public product null-point and splitting data.
        transcript[-1] += ';'.join(
                f's{j}={null_point[j]}' for j in range(16)) + ';'
        M_split = self.M_split.list()
        transcript[-1] += ';'.join(
                f'm{j}={M_split[j]}' for j in range(64)) + ';'
        transcript[-1] += f'e4={self.e4};'

        with open('zk_radical.txt', 'w') as fh:
            fh.write('\n'.join(transcript) + '\n')


class GlueHelper:
    def __init__(self, e, T16, B, M, BPQ, ePQ4):
        """
        Input:
        - T16: 4 TuplePoints representing the T_i
        - B: Canonical basis (R, S) on E[4]
        - M: Change of coordinates from B^4 to (S, T)
        - BPQ: basis (P, Q) of E[4*2^e]
        - ePQ4: e4(P4, Q4)
        """
        logger.debug('\t- Starting Gluing')
        _t0 = time()
        # Init
        self.E = B[0].curve() # Over Fp2
        self.Fp2 = self.E.base_ring()
        self.Fp = self.Fp2.base_ring()

        R, S = B
        P, Q = BPQ

        # Make dim 1 and 2 theta structures
        Theta1 = ThetaStructureDim1(self.E, R, S)
        Theta2 = ProductThetaStructureDim2(Theta1, Theta1)

        # Turn dimension 1 theta structure into dim 4
        dom_prod = ProductThetaStructureDim2To4(Theta2, Theta2)

        # Change of coordinate to the "good" basis
        self.e4 = ePQ4 # e4(P4, Q4) == e4(R, S)
        N_dim4 = base_change_theta_dim4(M, self.e4)
        dom_base_change = dom_prod.base_change_struct(N_dim4)

        self.N_dim4 = N_dim4
        self.dom_base_change = dom_base_change
        self.dom_prod = dom_prod
        self.Theta1 = Theta1
        _t1 = time()
        logger.debug(f'\t- Change of basis: {_t1 - _t0:.3f}s')

        # Prepare kernel
        L_K = list([2*_T for _T in T16])
        L_K_indexes = [
            (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)
        ]

        L_K = [[
            TuplePoint(L_K[k][0], L_K[k][1]),
            TuplePoint(L_K[k][2], L_K[k][3])
            ] for k in range(len(L_K))]

        # Translates for evaluation of the first gluing
        self.L_trans = [[2*(L_K[1][0]+L_K[2][0]),2*(L_K[1][1]+L_K[2][1])],
        [2*(L_K[0][0]+L_K[3][0]),2*(L_K[0][1]+L_K[3][1])]] # T2+T3, T1+T4
        self.L_ind = [6,9] # (0,1,1,0), (1,0,0,1)

        # Turn the theta dim 1 structure into dim 2
        L_K_theta = []
        for k in range(len(L_K)):
            _P1 = mont_to_theta(L_K[k][0][0], Theta1)
            _P2 = mont_to_theta(L_K[k][0][1], Theta1)
            thetaQ1 = theta_pt_prod_1to2(_P1, _P2)

            _P1 = mont_to_theta(L_K[k][1][0], Theta1)
            _P2 = mont_to_theta(L_K[k][1][1], Theta1)
            thetaQ2 = theta_pt_prod_1to2(_P1, _P2)
            L_K_theta.append((thetaQ1, thetaQ2))

        L_K = L_K_theta
        L_K = [dom_prod.product_theta_point(_R, _S) for _R, _S in L_K]
        L_K = [dom_base_change.base_change_coords(N_dim4, _RS) for _RS in L_K]
        _t2 = time()
        logger.debug(f'\t- Prepare kernel: {_t2 - _t1:.3f}s')

        # Gluing
        self.glue_4d = GluingIsogenyDim4(
                dom_base_change,
                L_K,
                L_K_indexes,
                coerce=self.Fp
        )
        self._domain = self.glue_4d._domain
        self._codomain = self.glue_4d._codomain

        # Second isogeny
        L_K_2 = list(T16)
        L_K_2.append(L_K_2[0]+L_K_2[1])

        L_K_2_indexes = [
                (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0),
                (0, 0, 0, 1), (1, 1, 0, 0)]

        L_K_2 = [self.eval_gluing(_T) for _T in L_K_2]

        self.second_isogeny = GluingIsogenyDim4(
                self.glue_4d._codomain,
                L_K_2,
                L_K_2_indexes,
                coerce=self.Fp
                )
        self._codomain = self.second_isogeny._codomain
        _t3 = time()
        logger.debug(f'\t- Isogeny: {_t3 - _t2:.3f}s')

    def codomain(self):
        return self._codomain

    def eval_gluing(self, P, return_domain=False):
        """
        We need to pass, together with P, translates P+T by points of 4-torsion
        T above the kernel. The index is turn into a number, so (1, 0, 1, 0) is
        T1 + T3 and corresponds to the index 2^0 + 2^2 = 5.
        All inputs to that are in theta coordinates, while P is a TuplePoint.
        """
        # Add translates to the points
        P = [TuplePoint(P[0], P[1]), TuplePoint(P[2], P[3])]

        P_trans = [
            [P[0] + Ti[0], P[1] + Ti[1]] for Ti in self.L_trans
        ]

        # Turn the theta dim 1 structure into dim 2
        # TODO: write more unified classes
        _P1 = mont_to_theta(P[0][0], self.Theta1)
        _P2 = mont_to_theta(P[0][1], self.Theta1)
        thetaQ1 = theta_pt_prod_1to2(_P1, _P2)

        _P1 = mont_to_theta(P[1][0], self.Theta1)
        _P2 = mont_to_theta(P[1][1], self.Theta1)
        thetaQ2 = theta_pt_prod_1to2(_P1, _P2)
        P_theta = (thetaQ1, thetaQ2)

        # Turning the translates into theta
        P_trans_theta = []
        for Q_tr in P_trans:
            _P1 = mont_to_theta(Q_tr[0][0], self.Theta1)
            _P2 = mont_to_theta(Q_tr[0][1], self.Theta1)
            thetaQ1 = theta_pt_prod_1to2(_P1, _P2)

            _P1 = mont_to_theta(Q_tr[1][0], self.Theta1)
            _P2 = mont_to_theta(Q_tr[1][1], self.Theta1)
            thetaQ2 = theta_pt_prod_1to2(_P1, _P2)
            P_trans_theta.append((thetaQ1, thetaQ2))

        P = P_theta
        P = self.dom_prod.product_theta_point(P_theta[0], P[1])
        P = self.dom_base_change.base_change_coords(self.N_dim4, P)

        P_trans = P_trans_theta
        P_trans = [self.dom_prod.product_theta_point(_R, _S) for _R, _S in P_trans]
        P_trans = [
            self.dom_base_change.base_change_coords(self.N_dim4, _RS)
            for _RS in P_trans
        ]

        Q = self.glue_4d.special_image(P, P_trans, self.L_ind)
        if return_domain:
            return P, Q
        return Q

    def __call__(self,P):
        Q = self.second_isogeny(self.eval_gluing(P))
        return Q

def theta_pt_prod_1to2(P1, P2):
    """
    Given two ThetaPointDim1 P1 and P2 on the same curve return the
    ThetaPointDim2 corresponding to (P1, P2) on E^2.
    """
    a1, b1 = P1.coords()
    a2, b2 = P2.coords()

    theta1 = P1._parent
    theta2 = ProductThetaStructureDim2(theta1, theta1)

    coords = [a1*a2, b1*a2, a1*b2, b1*b2]
    thetaP12 = ThetaPointDim2(theta2, coords)
    return thetaP12

def mont_to_theta(P, T):
    """
    Given a point P on E and a ThetaStructureDim1 for E return theta
    coordinates for P.
    From [Pegasis, Appendix A.1]
    Input:
    - a point P on E
    - a ThetaStrucureDim1 for E
    Output:
    - a ThetaPointDim1 representing P
    """
    R = T.P
    assert R*2 != R.curve()(0, 0)
    r = R.x()
    a, b = r+1, r-1

    if P != 0:
        xP, zP = P[0], P[2]
    else:
        xP, zP = 1, 0
    t1 = a*(xP-zP)
    t2 = b*(xP+zP)
    assert any([t1, t2]), "Invalid point"

    thetaP = ThetaPointDim1(T, (t1, t2))
    return thetaP

def product_factor_slice(P, factor):
    """
    Extract a projective factor from a product theta point, together with a
    public non-zero slice index.
    """
    mask = 2**factor
    for idx in range(16):
        if idx & mask:
            continue
        point = (P[idx], P[idx + mask])
        if point != (0, 0):
            return idx, point
    raise ValueError("Invalid product theta point")

def find_product_4(theta_null):
    """
    [Dartois Phd, Alg. 6.9] We have theta_ij = (theta_i)(theta_j) where the
    two components are on the two surfaces. Fix an index i0j0 to start such
    that theta_i0j0 != 0, and then set thetaA_i = theta_ij0 and thetaB_j =
    theta_i0j. Can be generalized to split anything in half dimension.
    """
    sA = []
    sB = []
    for i0, j0 in itt.product(range(4), repeat=2):
        idx = (j0 << 2) + i0 # Theta_i0j0
        if theta_null[idx] == 0:
            continue
        thetaA = [theta_null[(j0<<2) + i] for i in range(4)]
        thetaB = [theta_null[(j<<2) + i0] for j in range(4)]
        return thetaA, thetaB

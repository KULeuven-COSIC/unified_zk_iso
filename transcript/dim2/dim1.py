from collections import namedtuple
from sage.all import EllipticCurve
from sage.schemes.elliptic_curves.ell_generic import EllipticCurve_generic

from cgl import CGL
from utilities import montgomery_coefficient

ThetaNullPoint = namedtuple("ThetaNullPoint_dim_1", "a b")
ThetaPoint = namedtuple("ThetaNullPoint_dim_1", "x z")


class ThetaCGL(CGL):
    def __init__(self, domain, **kwds):
        super().__init__(domain, **kwds)
        if isinstance(self.domain, EllipticCurve_generic):
            self.domain = self.montgomery_curve_to_theta_null_point(domain)
        elif isinstance(domain, tuple):
            self.domain = ThetaNullPoint(*domain)

    def montgomery_curve_to_theta_null_point(self, E):
        """
        From an elliptic curve in Montgomery form, compute a theta null point
        (a:b). Let T1=(1:1) the canonical point of 4-torsion in Montgomery
        coordinates and T2 such that (T1,T2) forms a symplectic basis of E[4].
        There are 4 choices of T2, giving 4 different theta null points.
        """
        # Extract A from curve equation
        A = montgomery_coefficient(E)

        # alpha is a root of
        # x^2 + Ax + 1
        disc = A * A - 4
        assert disc.is_square()

        d = self.sqrt(disc)
        alpha = (-A + d) / 2

        # The theta coordinates a^2 and b^2
        # are related to alpha
        aa = alpha + 1
        bb = alpha - 1

        aabb = aa * bb
        ab = self.sqrt(aabb)

        # We aren't given (a,b) rational, but
        # (a/b) is rational so we use
        # (ab : b^2) as the theta null point
        O0 = ThetaNullPoint(ab, bb)
        return O0

    def to_montgomery_curve(self):
        """
        Given a level 2 theta null point (a:b), compute a Montgomery curve
        equation. We use the model where the 4-torsion point (1:0) above (a:-b)
        is sent to (1:1) in Montgomery coordinates.
        """

        a, b = self.domain

        aa = a**2
        bb = b**2

        T1 = aa + bb
        T2 = aa - bb

        # Montgomery coefficient
        A = -(T1**2 + T2**2) / (T1 * T2)

        # Construct curve
        F = b.parent()
        E = EllipticCurve(F, [0, A, 0, 1, 0])
        return E

    def j_invariant(self):
        """
        Give the j-invariant of our current theta null point
        """
        return self.to_montgomery_curve().j_invariant()

    def cardinality(self):
        return self.to_montgomery_curve().cardinality()

    @staticmethod
    def hadamard(x, z):
        return (x + z, x - z)

    def radical_2isogeny(self, bits=[0]):
        """
        Given a level 2-theta null point, compute a 2-isogeneous theta null
        point
        """
        a0, a1 = self.domain
        x0, x1 = ThetaCGL.hadamard(a0 * a0, a1 * a1)
        x01 = x0 * x1
        y1 = self.sqrt(x01)
        if bits[0] == 1:
            y1 = -y1
        b0, b1 = ThetaCGL.hadamard(x0, y1)
        O1 = ThetaNullPoint(b0, b1)
        return O1

    def advance(self, bits=[0]):
        O1 = self.radical_2isogeny(bits=bits)
        return ThetaCGL(O1)

    def to_hash(self):
        a0, a1 = self.domain
        return a1 / a0


# Experimental formula for 4-radical isogeny
class ThetaCGLRadical4(ThetaCGL):
    def __init__(self, domain, zeta4=None, chunk=2, **kwds):
        super().__init__(domain, chunk=chunk, **kwds)

        if zeta4 is None:
            a, _ = self.domain
            zeta4 = a.parent().gen()
        assert zeta4 * zeta4 == -1
        self.zeta4 = zeta4

    def radical_4isogeny(self, bits=[0, 0]):
        """
        Given a level 2-theta null point, compute a 4-isogeneous theta null
        point
        """
        a0, a1 = self.domain

        x0, x1 = ThetaCGL.hadamard(a0 * a0, a1 * a1)
        x01 = x0 * x1
        factor = self.fourth_root(x01)  # fourth root

        if bits[0] == 1:
            factor = -factor

        if bits[1] == 1:
            factor = self.zeta4 * factor

        b0 = a0 + factor
        b1 = a0 - factor
        b0, b1 = ThetaCGL.hadamard(b0, b1)

        return ThetaNullPoint(b0, b1)

    def advance(self, bits=[0, 0]):
        O1 = self.radical_4isogeny(bits=bits)
        return ThetaCGLRadical4(
            O1,
            zeta4=self.zeta4,
        )


# Experimental formula for 8-radical isogeny
class ThetaCGLRadical8(ThetaCGLRadical4):
    def __init__(
        self,
        domain,
        torsion=None,
        chunk=3,
        zeta8=None,
        zeta4=None,
        sqrt2=None,
        **kwds,
    ):
        super().__init__(domain, chunk=chunk, **kwds)

        self.zeta8 = zeta8
        assert self.zeta8**4 == -1

        self.zeta4 = zeta4
        assert self.zeta4**2 == -1

        self.sqrt2 = sqrt2
        assert self.sqrt2**2 == 2

        if torsion is None:
            a2, b2 = self.radical_2isogeny()
            r = self.sqrt(a2*b2)
            s = self.sqrt(b2**2)
            torsion = ThetaPoint(r, s)
        self.torsion = torsion

    def radical_8isogeny(self, bits=[0, 0, 0]):
        """
        Given a level 2-theta null point, compute a 4-isogeneous theta null
        point
        """
        a0, a1 = self.domain
        u0, u1 = self.torsion

        a00 = a0 * a0
        a01 = a0 * a1
        a11 = a1 * a1

        u00 = u0 * u0
        u01 = u0 * u1
        u11 = u1 * u1

        u0_4 = u00 * u00
        u1_4 = u11 * u11
        lam = self.eighth_root((u0_4 - u1_4)*(u0_4 + u1_4))

        if bits[0] == 1:
            lam = -lam

        if bits[1] == 1:
            lam = self.zeta4 * lam

        if bits[2] == 1:
            lam = self.zeta8 * lam

        assert lam**8 == u0**8 - u1**8

        lam_2 = lam * lam
        lam_4 = lam_2 * lam_2

        # Compute the codomain
        b0, b1 = ThetaCGL.hadamard(u00, lam_2)
        O1 = ThetaNullPoint(b0, b1)

        # Recover the 8-torsion above
        t = 2 * u01 * a01
        v0 = t * b1
        v1 = (
            2 * a00 * u01**2 
            + lam_4 * a11 
            - self.sqrt2 * lam * t * u0
        )
        P1 = ThetaPoint(v0, v1)
        
        return O1, P1

    def advance(self, bits=[0, 0, 0]):
        O1, P1 = self.radical_8isogeny(bits=bits)
        return ThetaCGLRadical8(
            O1,
            torsion=P1,
            zeta8=self.zeta8,
            zeta4=self.zeta4,
            sqrt2=self.sqrt2,
        )

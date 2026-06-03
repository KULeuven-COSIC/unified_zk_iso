from collections import namedtuple
from cgl import CGL
from dim1 import ThetaCGL

ThetaNullPointDim2 = namedtuple("ThetaNullPoint_dim_2", "a0 a1 a2 a3")


class ThetaCGLDim2(CGL):
    def __init__(self, domain, chunk=3, **kwds):
        super().__init__(domain, chunk=chunk, **kwds)

    @classmethod
    def from_null_coords(cls, coords):
        assert len(coords) == 4
        OO = ThetaNullPointDim2(*coords)
        return cls(OO)

    @classmethod
    def from_elliptic_curves(cls, E1, E2):
        O1 = ThetaCGL(E1)
        O2 = ThetaCGL(E2)
        a0, a1 = O1.domain
        b0, b1 = O2.domain
        OO = ThetaNullPointDim2(a0 * b0, a0 * b1, a1 * b0, a1 * b1)
        return cls(OO)

    @staticmethod
    def hadamard(x, y, z, t):
        return (x + y + z + t, x - y + z - t, x + y - z - t, x - y - z + t)

    def radical_2isogeny(self, bits=[0, 0, 0]):
        """
        Given a level 2-theta null point, compute a 2-isogeneous theta null
        point
        """
        a0, a1, a2, a3 = self.domain
        # Write to the transcript
        with open('zk_radical.txt', 'a') as fh:
            fh.write(f'{a0 = };{a1 = };{a2 = };{a3 = };\n')
        x0, x1, x2, x3 = ThetaCGLDim2.hadamard(a0 * a0, a1 * a1, a2 * a2, a3 * a3)

        # Ensure that the zero coordinate is not x0
        zero_index = 3
        xi_list = [x0, x1, x2, x3]
        for i, xi in enumerate(xi_list):
            if xi.is_zero():
                print("We will have a redundant bit...")
                zero_index = i
                break
        xi_list[zero_index], xi_list[3] = xi_list[3], xi_list[zero_index]
        x0, x1, x2, x3 = xi_list

        y0 = x0
        y1 = self.sqrt(x0 * x1)
        y2 = self.sqrt(x0 * x2)
        y3 = self.sqrt(x0 * x3)

        if bits[0] == 1:
            y1 = -y1
        if bits[1] == 1:
            y2 = -y2
        if bits[2] == 1:
            y3 = -y3

        # If we swapped coordinates, swap them back
        yi_list = [y0, y1, y2, y3]
        yi_list[zero_index], yi_list[3] = yi_list[3], yi_list[zero_index]
        y0, y1, y2, y3 = yi_list

        b0, b1, b2, b3 = ThetaCGLDim2.hadamard(y0, y1, y2, y3)

        rhs = a0**2 + a1**2 + a2**2 + a3**2
        lhs = (b0 + b1 + b2 + b3)**2
        rad_scale = (lhs / rhs).sqrt()
        b0 /= rad_scale
        b1 /= rad_scale
        b2 /= rad_scale
        b3 /= rad_scale

        old1 = a0**2 + a1**2 + a2**2 + a3**2
        old2 = a0**2 - a1**2 + a2**2 - a3**2
        old3 = a0**2 + a1**2 - a2**2 - a3**2
        old4 = a0**2 - a1**2 - a2**2 + a3**2

        new1 = (b0 + b1 + b2 + b3)**2
        new2 = (b0 - b1 + b2 - b3)**2
        new3 = (b0 + b1 - b2 - b3)**2
        new4 = (b0 - b1 - b2 + b3)**2

        # print(f'{old1 = } {new1 = }')
        # print(f'{old2 = } {new2 = }')
        # print(f'{old3 = } {new3 = }')
        # print(f'{old4 = } {new4 = }')
        # assert old1 == new1
        # assert old2 == new2
        # assert old3 == new3
        # assert old4 == new4

        return ThetaNullPointDim2(b0, b1, b2, b3)

    def advance(self, bits=[0, 0, 0]):
        O1 = self.radical_2isogeny(bits)
        return ThetaCGLDim2(O1)

    def to_hash(self):
        a0, a1, a2, a3 = self.domain
        a0_inv = 1 / a0
        return (a1 * a0_inv, a2 * a0_inv, a3 * a0_inv)


class ThetaCGLDim2Radical4(ThetaCGLDim2):
    def __init__(
        self,
        domain,
        zeta4=None,
        chunk=6,
        **kwds,
    ):
        super().__init__(domain, chunk=chunk, **kwds)

        if zeta4 is None:
            a = self.domain[0]
            zeta4 = a.parent().gen()
        assert zeta4 * zeta4 == -1
        self.zeta4 = zeta4

    def radical_4isogeny(self, bits=[0, 0, 0, 0, 0, 0]):
        """
        Given a level 2-theta null point, compute a 4-isogeneous theta null
        point
        """
        a0, a1, a2, a3 = self.domain
        x0, x1, x2, x3 = ThetaCGLDim2.hadamard(a0 * a0, a1 * a1, a2 * a2, a3 * a3)

        x01 = x0 * x1
        x02 = x0 * x2
        x13 = x1 * x3
        x23 = x2 * x3

        # First sqrt
        y = self.sqrt(x01 * x23)

        # Consume one bit on the sign
        if bits[0] == 1:
            y = -y

        # Two fourth roots
        alpha1_4 = 4 * (2 * y + x01 + x23)
        alpha2_4 = 4 * (2 * y + x02 + x13)
        alpha1 = self.fourth_root(alpha1_4)
        alpha2 = self.fourth_root(alpha2_4)

        # Consume four bits, sign and zeta
        if bits[1] == 1:
            alpha1 = -alpha1
        if bits[2] == 1:
            alpha1 *= self.zeta4

        if bits[3] == 1:
            alpha2 = -alpha2
        if bits[4] == 1:
            alpha2 *= self.zeta4

        # Last sqrt
        alpha3_2 = 8 * (x23 + y)
        alpha3_2 *= (x02 + y) * x23 * x3 + (x13 + y) * x23 * x2
        alpha3 = self.sqrt(alpha3_2)

        # Consume the last bit
        if bits[5] == 1:
            alpha3 = -alpha3

        projective_factor = x23 * alpha1 * alpha2
        b0, b1, b2, b3 = ThetaCGLDim2.hadamard(
            2 * a0 * projective_factor,
            alpha1 * projective_factor,
            alpha2 * projective_factor,
            alpha3,
        )

        return ThetaNullPointDim2(b0, b1, b2, b3)

    def advance(self, bits=[0, 0, 0, 0, 0, 0]):
        O1 = self.radical_4isogeny(bits=bits)
        return ThetaCGLDim2Radical4(
            O1,
            zeta4=self.zeta4,
        )

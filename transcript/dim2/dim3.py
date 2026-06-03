from collections import namedtuple
from dim1 import CGL, ThetaCGL
from sage.all import vector

ThetaNullPointDim3 = namedtuple("ThetaNullPoint_dim_3", "a0 a1 a2 a3 a4 a5 a6 a7")


class ThetaCGLDim3(CGL):
    def __init__(self, domain, **kwds):
        super().__init__(domain, chunk=6, **kwds)

    @classmethod
    def from_null_coords(cls, coords):
        assert len(coords) == 8
        OO = ThetaNullPointDim3(*coords)
        return cls(OO)

    @classmethod
    def from_elliptic_curves(cls, E1, E2, E3):
        O1 = ThetaCGL(E1)
        O2 = ThetaCGL(E2)
        O3 = ThetaCGL(E3)
        a0, a1 = O1.domain
        b0, b1 = O2.domain
        c0, c1 = O3.domain
        # We changed the ordering to be compatible with our notes.
        OO = ThetaNullPointDim3(
            a0 * b0 * c0,
            a1 * b0 * c0,
            a0 * b1 * c0,
            a1 * b1 * c0,
            a0 * b0 * c1,
            a1 * b0 * c1,
            a0 * b1 * c1,
            a1 * b1 * c1,
        )
        return cls(OO)

    @staticmethod
    def hadamard(x0, x1, x2, x3, x4, x5, x6, x7):
        y0 = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7
        y1 = x0 - x1 + x2 - x3 + x4 - x5 + x6 - x7
        y2 = x0 + x1 - x2 - x3 + x4 + x5 - x6 - x7
        y3 = x0 - x1 - x2 + x3 + x4 - x5 - x6 + x7
        y4 = x0 + x1 + x2 + x3 - x4 - x5 - x6 - x7
        y5 = x0 - x1 + x2 - x3 - x4 + x5 - x6 + x7
        y6 = x0 + x1 - x2 - x3 - x4 - x5 + x6 + x7
        y7 = x0 - x1 - x2 + x3 - x4 + x5 + x6 - x7
        return (y0, y1, y2, y3, y4, y5, y6, y7)


    def last_sqrt(self, x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6):
        #b0, b1, b2, b3, b4, b5, b6, b7 = self.hadamard(x0, x1, x2, x3, x4, x5, x6, x7)
        
        a0, a1, a2, a3, a4, a5, a6, a7 = self.domain

        a0123 = 16 * a0 * a1 * a2 * a3 # 3 M + 1 m
        a4567 =  16 * a4 * a5 * a6 * a7 # 3 M + 1 m
        r1 =  a0123 * a0123  # 1 S
        r3 =  a4567 * a4567  # 1 S

        x04 = x0 * x4
        x15 = x1 * x5
        x26 = x2 * x6
        x37 = x3 * x7
        x0246 = x04 * x26
        x1357 = x15 * x37   # 6 M

        t0 = (x04 - x15 + x26 - x37) ** 2 - 4 * (x0246 + x1357)     # 1 S + 1 m + 5 a
        t = r1 + r3 - t0 #  2 a

        y = y1 * y2 * y3 * y4 * y5 * y6 # 5 M 

        if t != 0:
            t1 = t * t + 64 * x0246 * x1357 - 4 * r1 * r3 # 2 M + 1 S + 2 m + 2 a
            t2 = 16 * t * y # 1 M + 1 m
        else:
            t1 = - a0123 * a4567 # 1 M
            t2 = 4 * y # 1 m

        y0, y1, y2, y3, y4, y5, y6 = [t2 * y for y in [y0, y1, y2, y3, y4, y5, y6]]     # 7 M 
        y7 = t1 * x0**3  # 2 M + 1 S

        return y0, y1, y2, y3, y4, y5, y6, y7

    def squared_thetas(self):
        converter = {
            0: vector([0, 0, 0]),
            1: vector([1, 0, 0]),
            2: vector([0, 1, 0]),
            3: vector([1, 1, 0]),
            4: vector([0, 0, 1]),
            5: vector([1, 0, 1]),
            6: vector([0, 1, 1]),
            7: vector([1, 1, 1]),
        }

        a0, a1, a2, a3, a4, a5, a6, a7 = self.domain
        theta_list = [a0, a1, a2, a3, a4, a5, a6, a7]
        squared_theta_list = []

        for chi in range(0, 8):
            for i in range(0, 8):
                if (converter[chi] * converter[i]) % 2 == 0:
                    U_chi_i = 0
                    for t in range(0, 8):
                        chi_t = (-1) ** (converter[chi] * converter[t])
                        vec = (converter[i] + converter[t]) % 2
                        index = vec[0] + 2 * vec[1] + 4 * vec[2]
                        U_chi_i += chi_t * theta_list[index] * theta_list[t]
                    squared_theta_list.append(U_chi_i)
        return squared_theta_list

    def label(self):
        """
        Type1: plane quartic
        Type2: hyperelliptic
        Type3: product of dimension 1 and 2
        Type4: product of elliptic curves
        """
        squared_thetas_list = self.squared_thetas()
        zeros = 0
        for el in squared_thetas_list:
            if el == 0:
                zeros += 1
        if zeros == 0:
            return "Plane quartic"
        elif zeros == 1:
            return "Hyperelliptic curve"
        elif zeros == 6:
            return "Product of a hyperelliptic curve and an elliptic curve"
        elif zeros == 9:
            return "Product of three elliptic curves"
        else:
            print("unexpected case: number of zeros is", zeros)
            return None

    def radical_2isogeny(self, bits=[0, 0, 0, 0, 0, 0]):
        """
        Given a level 2-theta null point, compute a 2-isogeneous theta null
        point
        """
        a0, a1, a2, a3, a4, a5, a6, a7 = self.domain
        x0, x1, x2, x3, x4, x5, x6, x7 = self.hadamard(
            a0 * a0, a1 * a1, a2 * a2, a3 * a3, a4 * a4, a5 * a5, a6 * a6, a7 *a7
        )

        # Ensure that if a value is zero, it is x7
        # TODO: we need to handle the case where x0 = 0 and x7 = 0
        #       which would currently break the hash...
        xi_list = [x0, x1, x2, x3, x4, x5, x6, x7]
        zero_index = 7
        for i, xi in enumerate(xi_list):
            if xi.is_zero():
                zero_index = i
                break
        xi_list[zero_index], xi_list[7] = xi_list[7], xi_list[zero_index]
        x0, x1, x2, x3, x4, x5, x6, x7 = xi_list

        # Compute yi from square roots
        y0 = x0
        y1 = self.sqrt(x0 * x1)
        y2 = self.sqrt(x0 * x2)
        y3 = self.sqrt(x0 * x3)
        y4 = self.sqrt(x0 * x4)
        y5 = self.sqrt(x0 * x5)
        y6 = self.sqrt(x0 * x6)

        # Conditionally negate values
        if bits[0] == 1:
            y1 = -y1
        if bits[1] == 1:
            y2 = -y2
        if bits[2] == 1:
            y3 = -y3
        if bits[3] == 1:
            y4 = -y4
        if bits[4] == 1:
            y5 = -y5
        if bits[5] == 1:
            y6 = -y6

        # If any of x1, ..., x6 are zero we're on a degenerate case with a redundant bit
        zero_indices = [
            i for i, x in enumerate([x1, x2, x3, x4, x5, x6]) if x.is_zero()
        ]
        if zero_indices:
            print("we have redundant bits")
            y7 = self.sqrt(x0 * x7)
            if bits[zero_indices[0]] == 1:
                y7 = -y7
        else:
            y0, y1, y2, y3, y4, y5, y6, y7 = self.last_sqrt(
                x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6
            )

        # If we swapped a value above, then we should swap the corresponding yi
        yi_list = [y0, y1, y2, y3, y4, y5, y6, y7]
        yi_list[zero_index], yi_list[7] = yi_list[7], yi_list[zero_index]
        y0, y1, y2, y3, y4, y5, y6, y7 = yi_list

        # Compute the codomain with a last Hadamard
        b0, b1, b2, b3, b4, b5, b6, b7 = self.hadamard(y0, y1, y2, y3, y4, y5, y6, -y7)
        _theta = (b0, b1, b2, b3, b4, b5, b6, b7)
        print(f'{self.check_riemann(_theta) = }')
        b0, b1, b2, b3, b4, b5, b6, b7 = self.hadamard(y0, y1, y2, y3, y4, y5, y6, y7)
        _theta = (b0, b1, b2, b3, b4, b5, b6, b7)
        print(f'{self.check_riemann(_theta) = }')
        breakpoint()


        O1 = ThetaNullPointDim3(b0, b1, b2, b3, b4, b5, b6, b7)
        return O1

    def check_riemann(self, theta):
        a0, a1, a2, a3, a4, a5, a6, a7 = theta
        b00, b01, b10, b11, d00, d01, d10, d11 = self.hadamard(
            a0 * a0, a1 * a1, a2 * a2, a3 * a3, a4 * a4, a5 * a5, a6 * a6, a7 *a7
        )

        # b00, b01, b10, b11, d00, d01, d10, d11 = hadamard(*square(*theta))
        c00 = 2*(a0*a4 + a1*a5 + a2*a6 + a3*a7)
        c01 = 2*(a0*a4 - a1*a5 + a2*a6 - a3*a7)
        c10 = 2*(a0*a4 + a1*a5 - a2*a6 - a3*a7)
        c11 = 2*(a0*a4 - a1*a5 - a2*a6 + a3*a7)

        R1 = b00 * b01 * b10 * b11
        R2 = c00 * c01 * c10 * c11
        R3 = d00 * d01 * d10 * d11
        print(f'{R1 = } {R2 = } {R3 = }')

        return R1**2 + R2**2 + R3**2 - 2*(R1*R2 + R1*R3 + R2*R3) == 0

    def advance(self, bits=[0, 0, 0, 0, 0, 0]):
        O1 = self.radical_2isogeny(bits)
        O1 = ThetaCGLDim3(O1)
        return O1

    def bit_string(self, message):
        r = self
        for x in range(0, len(message), self.chunk):
            bits = message[x : x + self.chunk]
            try:
                r = r.advance(bits)
            except Exception as e:
                raise ValueError(f"Something went wrong: {e = }")
        return r

    def to_hash(self):
        a0, a1, a2, a3, a4, a5, a6, a7 = self.domain
        a0_inv = 1 / a0
        return (
            a1 * a0_inv,
            a2 * a0_inv,
            a3 * a0_inv,
            a4 * a0_inv,
            a5 * a0_inv,
            a6 * a0_inv,
            a7 * a0_inv,
        )

# def hadamard(x0, x1, x2, x3, x4, x5, x6, x7):
#     y0 = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7
#     y1 = x0 - x1 + x2 - x3 + x4 - x5 + x6 - x7
#     y2 = x0 + x1 - x2 - x3 + x4 + x5 - x6 - x7
#     y3 = x0 - x1 - x2 + x3 + x4 - x5 - x6 + x7
#     y4 = x0 + x1 + x2 + x3 - x4 - x5 - x6 - x7
#     y5 = x0 - x1 + x2 - x3 - x4 + x5 - x6 + x7
#     y6 = x0 + x1 - x2 - x3 - x4 - x5 + x6 + x7
#     y7 = x0 - x1 - x2 + x3 - x4 + x5 + x6 - x7
#     return (y0, y1, y2, y3, y4, y5, y6, y7)

# def square(x0, x1, x2, x3, x4, x5, x6, x7):
#     return x0**2, x1**2, x2**2, x3**2, x4**2, x5**2, x6**2, x7**2

# def check_riemann(theta):
#     """
#     Given a theta null point check the riemann relation from [Theta, prop 7]
#     """

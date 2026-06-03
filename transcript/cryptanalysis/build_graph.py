
from sage.all import *
import itertools as itt


def sqrt_Fp(x):
    p = x.parent().characteristic()
    exp = (p + 1) // 4

    r = x**exp
    if r * r != x:
        return 0
    if int(r) % 2 != 0:
        return -r
    return r


def sqrt_Fp2(x):
    assert x.is_square(), "Trying to take a square-root of a non-square..."
    F = x.parent()
    x0, x1 = x.list()

    if x1 == 0:
        lx0 = x0.is_square()
        if lx0:
            y0 = sqrt_Fp(x0)
            return F([y0, 0])
        else:
            y1 = sqrt_Fp(-x0)
            return F([0, y1])

    delta = x0**2 + x1**2
    sqrt_delta = sqrt_Fp(delta)

    y02 = (x0 + sqrt_delta) / 2
    if not y02.is_square():
        y02 -= sqrt_delta

    y0 = sqrt_Fp(y02)
    y1 = x1 / (y0 + y0)

    return F([y0, y1])

def montgomery_coefficient(E):
    a_inv = E.a_invariants()
    A = a_inv[1]
    if a_inv != (0, A, 0, 1, 0):
        raise ValueError("The elliptic curve E is not in the Montgomery model.")
    return A

def curve_to_theta_1(E):
    A = montgomery_coefficient(E)
    disc = A * A - 4
    assert disc.is_square()
    d = sqrt_Fp2(disc)
    alpha = (-A + d) / 2
    aa = alpha + 1
    bb = alpha - 1
    aabb = aa * bb
    ab = sqrt_Fp2(aabb)
    return (ab, bb)

def curve_to_theta_3(E1, E2, E3):
    a0, a1 = curve_to_theta_1(E1)
    b0, b1 = curve_to_theta_1(E2)
    c0, c1 = curve_to_theta_1(E3)
    return (
        a0 * b0 * c0,
        a1 * b0 * c0,
        a0 * b1 * c0,
        a1 * b1 * c0,
        a0 * b0 * c1,
        a1 * b0 * c1,
        a0 * b1 * c1,
        a1 * b1 * c1,
    )

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

def square(x0, x1, x2, x3, x4, x5, x6, x7):
    return x0**2, x1**2, x2**2, x3**2, x4**2, x5**2, x6**2, x7**2

def last_sqrt(theta, x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6):
    #b0, b1, b2, b3, b4, b5, b6, b7 = self.hadamard(x0, x1, x2, x3, x4, x5, x6, x7)
    
    a0, a1, a2, a3, a4, a5, a6, a7 = theta

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

def radical_step(theta, only_isogs = False):
    """
    Given a theta-null point theta, compute all the possible 2^g-1=7 sign
    choices (so 2^7 outgoing isogenies) and check that 2^6 satisfy the riemann
    relations
    """
    a0, a1, a2, a3, a4, a5, a6, a7 = theta
    xi_list = list(hadamard(*square(*theta)))
    # print(f'{xi_list = }')

    # Should look for non-zero index instead
    zero_index = 7
    for i, xi in enumerate(xi_list):
        if xi.is_zero():
            zero_index = i
            break
    xi_list[zero_index], xi_list[7] = xi_list[7], xi_list[zero_index]
    x0, x1, x2, x3, x4, x5, x6, x7 = xi_list

    # Compute yi from square roots
    #if not check_riemann(theta):
    #    print([(x0 * xi).is_square() for xi in xi_list])
    yi_list = [sqrt_Fp2(x0 * xi) for xi in xi_list]
    yi_list[0] = xi_list[0]

    sols = set()
    if only_isogs:
        # If any of x1, ..., x6 are zero we're on a degenerate case with a redundant bit
        zero_indices = [
            i for i, x in enumerate([x1, x2, x3, x4, x5, x6]) if x.is_zero()
        ]

        for signs in itt.product([1, -1], repeat=6):
            yi_temp = [yi_list[0]] + [signs[j] * yi_list[j+1] for j in range(6)]
            if zero_indices:
                y7 = sqrt_Fp2(x0 * x7)
                ss = yi_temp + [y7]
            else:
                ss = last_sqrt(theta, *xi_list, *yi_temp)
            sols.add(tuple(ss))
    else:
        for signs in itt.product([1, -1], repeat=7):
            ss = [yi_list[0]] + [signs[j] * yi_list[j+1] for j in range(7)]
            sols.add(tuple(ss))

    # print(f'{len(sols) = }')



    out = set()
    for sol in sols:
        yi_list = list(sol)
        yi_list[zero_index], yi_list[7] = yi_list[7], yi_list[zero_index]
        bi_list = hadamard(*yi_list)
        out.add(bi_list)

    return out

def check_riemann(theta):
    """
    Given a theta null point check the riemann relation from [Theta, prop 7]
    """
    a0, a1, a2, a3, a4, a5, a6, a7 = theta
    b00, b01, b10, b11, d00, d01, d10, d11 = hadamard(*square(*theta))
    c00 = 2*(a0*a4 + a1*a5 + a2*a6 + a3*a7)
    c01 = 2*(a0*a4 - a1*a5 + a2*a6 - a3*a7)
    c10 = 2*(a0*a4 + a1*a5 - a2*a6 - a3*a7)
    c11 = 2*(a0*a4 - a1*a5 - a2*a6 + a3*a7)

    R1 = b00 * b01 * b10 * b11
    R2 = c00 * c01 * c10 * c11
    R3 = d00 * d01 * d10 * d11

    return R1**2 + R2**2 + R3**2 - 2*(R1*R2 + R1*R3 + R2*R3) == 0

def normalize_projective(P):
    assert not all([c == 0 for c in P])
    non_zero_idx = 0
    while P[non_zero_idx] == 0:
        non_zero_idx += 1
    lam = P[non_zero_idx]
    P = [c/lam for c in P]
    return P

from collections import deque, defaultdict

def normalize_tuple(P):
    """
    Normalize a projective point and return an immutable tuple.
    Returns None if the point is the zero vector.
    """
    if all(c == 0 for c in P):
        return None

    return tuple(normalize_projective(list(P)))


def radical_step_normalized(theta, only_isogs = False):
    """
    Apply radical_step(theta), normalize all outputs projectively,
    discard zero vectors, and deduplicate.

    Returns:
        set of normalized tuples
    """
    out = []

    try:
        raw = radical_step(theta, only_isogs = only_isogs)
    except Exception:
        #print("THIS EXEPTION WAS HIT?")
        return out

    for P in raw:
        Q = normalize_tuple(P)
        if Q is not None:
            out.append(Q)

    return out


def build_graph(start_theta, max_depth=None):
    """
    Traverse the graph generated by radical_step.

    Parameters
    ----------
    start_theta:
        Initial theta point

    max_depth:
        Optional BFS depth cutoff

    Returns
    -------
    vertices:
        set of normalized vertices

    edges:
        dict mapping vertex -> set(neighbors)

    riemann_pts:
        set of vertices satisfying check_riemann
    """

    start = normalize_tuple(start_theta)

    vertices = {start}
    edges = defaultdict(set)

    q = deque([(start, 0)])
    visited = {start}

    while q:
        theta, depth = q.popleft()

        if max_depth is not None and depth >= max_depth:
            continue

        nbrs = radical_step_normalized(theta)

        # Dead end allowed naturally if nbrs == empty set
        for tt in nbrs:

            # Add edge theta -> tt
            edges[theta].add(tt)

            if tt not in vertices:
                vertices.add(tt)

            if tt not in visited:
                visited.add(tt)
                q.append((tt, depth + 1))

    return vertices, edges

if __name__=="__main__":
    #p = 2**64 - 257
    #p = 2**10 * 5 - 1
    p = 3
    Fp2 = GF(p**2, name="i", modulus=[1, 0, 1])
    E0 = EllipticCurve(Fp2, [1, 0])
    assert E0.is_supersingular()

    theta0 = curve_to_theta_3(E0, E0, E0)
    print(theta0)

    V, E = build_graph(theta0, 1)

    G = DiGraph(multiedges=True, loops=True)
    for v in V:
        G.add_vertex(v)
    for u, nbrs in E.items():
        for v in nbrs:
            G.add_edge(u, v)

    P = G.plot(
        layout="spring",
        vertex_size=30,
        vertex_labels=False,
    )

    P.save("pseudo_isogeny_graph.png")
    

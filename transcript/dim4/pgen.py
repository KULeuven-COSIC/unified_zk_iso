from sage.all import *
proof.all(False)
from theta_lib.pkg.basis_change.canonical_basis_dim1 import make_canonical
from xonly import xPoint, random_xPoint, MontgomeryA, isWeierstrass, translate_by_T

from pathlib import Path
import json

def gen_params(p, A):
    """
    Given p and the montgomery coefficient of the starting curve A, generate
    and print all the precomputation for the starting curve.
    """
    e = valuation(p+1, 2)
    f = (p+1)//(2**e)

    Fp = GF(p)
    Fp2 = GF((p, 2), name='i', modulus=var('x')**2 + 1)

    E_start = EllipticCurve(Fp, [0, A, 0, 1, 0])
    print('Setup done')

    e_sol = e - 3

    EE = E_start.change_ring(Fp2)

    P, Q, TP, TQ = TwoTorsBasis(E_start, e_sol+2)

    dt_two = 2**(e_sol-2)
    P16, Q16 = dt_two*P, dt_two*Q
    P4, Q4 = 4*P16, 4*Q16
    ePQ4 = P4.weil_pairing(Q4, 4)

    assert TP.y() == 0 and TP.x() in Fp
    assert TQ.y() == 0 and TQ.x() in Fp

    # Change of basis
    _, _, R, S, M0 = make_canonical(P4, Q4, 4, preserve_pairing=True)
    (_x, _y), (_z, _w) = M0
    assert _x*R + _y*S == P4 and _z*R + _w*S == Q4
    data = {
        'f': int(f),
        'e': int(e),
        'A': int(A),
        'Px': int(P.x()),
        'Py': int(P.y()),
        'Qx': int(Q.x()),
        'Qy': int(Q.y()[1]),
        'TPx': int(TP.x()),
        'TQx': int(TQ.x()),
        'P16x': int(P16.x()),
        'P16y': int(P16.y()),
        'Q16x': int(Q16.x()),
        'Q16y': int(Q16.y()[1]),
        'Rx': int(R.x()),
        'Ry': int(R.y()[0]),
        'Ryi': int(R.y()[1]),
        'Sx': int(S.x()),
        'Sy': int(S.y()[0]),
        'Syi': int(S.y()[1]),
        'ePQ4': int(ePQ4[1]),
        '_xyzw': [int(_x), int(_y), int(_z), int(_w)]
    }
    return data

    # Print all stuff in hex
    # print(f"'f':{f},")
    # print(f"'e':{e},")
    # print(f"'A':{hex(ZZ(A))},")
    # ...

# Basis generation from PEGASIS
def TwoTorsBasis(E, e):
    T0, Tm1, T1 = find_Ts(E)

    A = MontgomeryA(E)
    F = E.base_field()
    p = F.characteristic()

    R = F["X"]
    X = R.gens()[0]
    f = X**2 + A*X + 1

    xT0 = T0.x()
    xP = xT0 + F.random_element()**2
    while not (f(xP)*xP).is_square() or (xP-Tm1.x()).is_square():
        xP = xT0 + F.random_element()**2

    xQ = xT0 - F.random_element()**2
    while (f(xQ)*xQ).is_square() or not ((xQ-T1.x()).is_square()):
        xQ = xT0 - F.random_element()**2

    P = xPoint(xP, E)
    Q = xPoint(xQ, E)

    assert (p+1) % 2**(e+1) == 0
    cofac = (p+1)/2**(e+1)
    P = P.xMUL(cofac)
    Q = Q.xMUL(cofac)

    assert P.xMUL(2**(e-1))
    assert not P.xMUL(2**e)
    assert Q.xMUL(2**(e-1))
    assert not Q.xMUL(2**e)
    assert Q.xMUL(2**(e-1)) != P.xMUL(2**(e-1))

    return eval_omega_and_lift(E, P, Q, T0, Tm1, T1)

def eval_omega_and_lift(E, P, Q, T0, Tm1, T1):
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

    p = F.characteristic()
    Fp2 = GF((p, 2), name='i', modulus=var('x')**2 + 1)
    EE = E.change_ring(Fp2)
    ii = Fp2.gen()
    Qlift = EE(-Qliftt.x(),-ii*Qliftt.y())
    Plift = EE(Plift)
    TP = EE(TP)
    TQ = EE(TQ)

    return Plift, Qlift, TP, TQ

def find_Ts(E, only_T0 = False):
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

def starting_curve(p, E0=None):
    """
    Given a prime p, compute the montgomery coefficient of a valid starting
    curve A.
    """
    # Starting curve y^3 = x^3 - x
    if not E0:
        Fp = GF(p)
        # Fp2 = GF((p, 2), name='i', modulus=var('x')**2 + 1)
        E0 = EllipticCurve(Fp, [-1, 0])

    # Fid the cofactor
    val2 = valuation(p+1, 2)
    ell = (p+1)//(2**val2)
    assert ell != 1
    ell = factor(ell)[0][0]
    cof = (p+1)//ell
    print(f'{ell = }')

    # Act with some odd ideal
    n_act = ZZ(p).nbits()
    n_act += n_act // 10

    E = E0
    E._order = p+1
    from tqdm import tqdm
    # for i in range(n_act):
    for i in tqdm(range(n_act)):
        # print(f'Action {i+1}/{n_act} ({100*i/n_act:.1f}%)')
        while True:
            P = E.random_point() * cof
            if P != 0:
                assert P * ell == 0, "something is very wrong"
                break
        P._order = ell
        phi = E.isogeny(P)
        E = phi.codomain()
        E._order = p+1

    A = E.montgomery_model().a_invariants()[1]
    return A

# Parameter sets for PEGASIS
peg_primes = {
    '500':33*2**503-1,
    '1000':15*2**1004-1,
    '1500':9*2**1551-1,
    '2000':51*2**2026-1,
    '4000':63*2**4084-1
}

peg_curves = {
    '500':0x102bad9db56de678020d816f2c566b728c4cf1515fda7c3687a864824ea9a8c7a03b686a2d80253ad0b82d8923200c4b48c28e67bb66d4eb586cff837915a121,
    '1000':0xe474e3ef79088b1bbaccf7ae89f9f54915df70255a113272315c2cf8848e52c753403bec0cf386862b1cb4512510bc748ca96efa6158e543dfa151df2ddba05437796407a5a463b172da19daf51de831508e6f8af1b101559164aa023111c0b58fe9b2891d8335d6dde2f9c15dd8fa51a3a7387f120f038ae45d33b499ed,
    '1500':0x2fad1cba2a3569b406ee81b363feaa81df691ebe08245fb88ff478bac22523a60473d097cb184112c1a9d422f6dd5144544b9055ce27c094a938e73e724c4bc8ffe241d783d858e8f7dae86db910f9a6eee633fe7b86589cd7f1fbf4fd376a924cf8976afd202f2de3a58e851767542653724b832fdb637a5bb116f1adab4db7193f6c3bf90271bd231702dcdde158df61c34f1a0f7f40c3b2dd4c787677ec5f5d083d12429b8c922abd7bbfa860ffbdc97bf2c47ccdda765b8ad18c8b74aab821676,
    '2000':0x2a5264129fc329c574f17d7355b096d99dff8cd2f46b295ce5198f9278342bbe5810709c09dd2d8427eced058237c4b89bd102fe1c21eecfef5f203bf49127c887126051d51678f098c0e9a99fe85b9535df355596e5292e85d46451ad110e7955c650e592e2420a9d243ee3a4187eea1a88761b83db13e364ca9a32426072f59a684329e74f81a9504fb6359332a730ef51201182da362032ce0f10aaae693bfd7207730be75d29bbde01d3c2153abce23af50a535041c129a86c0de8c94dda5ea3b00caefb3ad0b73bd6113bfe2cfb5a9ea8aa6bba5a788c06b0f3963241b851ae65a2eafd933c076cee39c63657f8056efe9858c84a715e8f1985a3be,
    '4000':0xf24a99b4c09c41e66e81d92bbf7dc29ca187aec88c97dd176d1d33a517e0055c1462f209f9fd0292126c4a075f6bbc5a9deae336faa329abc903b0e578f3d07c0ee74531e654843e1d8580aa0ad4e7c2089e74b4032d3d98cd1717adbc328c266baaebd9800854ca5778821a1c2acc8bd9df86a4dc979e0a5deadfe6dfab34fe134b1645a0309692e6b4695ba7b9cecefebe43d16146a9b1b0c55753611857b6ccabeab15f2c18856dd1d47bc9c33dd0494fa97fa5e583ded4c31eefd949b1ba957c20e01c5c72a564a28fcf9f40368801a4f3c60ee2639636696a654ba98fb2adf486e3794355639c315c6f1349324443dec0f1c591947f3a4380fb0756fa65cb3e34e9111f5807b7a15cb6980b20cfbf446c8fa8c4d36259a6ef1a0aa543509112e7b56b9b8e04bf74b761deee6e0f51fec35f2f59d0f0474b2da20f752659780accbd930f50fbd049b20e4886f35cdae2cce8f06387be15b5a5e10a662293d1f71129a6547b741bd5f106d33e836bdcbb1a8fdd223aa8cfc204bb587fa60fb41f28fa2a01f26634699fcdce70c5b2ef93e6523e4daeeb5a79f044f4dbc545d3ecc20109514acdaa48f4bfb1901a408199742be8333901ac9f4b8dbbb2ec4b25e55a497bfd5e23c181dc167c022a5908183cb9f203176538a2ccc6b9c23cd20fe037bc4776ec4f561e9974abf7e84cdcea0fbc61bce901302b961966250b
}

# Parameter sets for qt-Pegasis
qtp_primes = {
    '500': 27 * 2**500 - 1,
    '1000': 15 * 2**1004 - 1, # same as in PEGASIS
    '1500': 5 * 2**1522 - 1,
    '2000': 5 * 2**2014 - 1,
    '4000': 45 * 2**4024 - 1
}

qtp_curves = {
    '500':0x1648774f73444336f54a856d88c81350d300274f4518a60a5446912fc6533d590f65c5a2dbba86bdd1ad80e7e7dfad4ce240052db3f10f48440f00d80735f34,
    '1000':0xe474e3ef79088b1bbaccf7ae89f9f54915df70255a113272315c2cf8848e52c753403bec0cf386862b1cb4512510bc748ca96efa6158e543dfa151df2ddba05437796407a5a463b172da19daf51de831508e6f8af1b101559164aa023111c0b58fe9b2891d8335d6dde2f9c15dd8fa51a3a7387f120f038ae45d33b499ed,
    '1500':0x1253a191007c7828135448acd08b424b1d35435105a3c3591a4f0999f36500e7f47aaefae38133f57aa7e4085fee410080818f993ae0e749c86fbfc1979797da273f6792fadb3c6bc9119410d1ad223d4795d8fa4796fe1ed6c8efdc9b291f2f6e7ab04bbdb42029b510a52fcb9d16a4ac984e28903b0db2ca83b549a050615aaaa2fc5bb8dfd9d7c2e76920bceb0d76f5d6d65ddba4ab99d1eaaf490a1a1cf2edec36db979f0b48d6f05c160572a67f18a3357140dd268e0fd6fb2a02816b,
    '2000':0x3fbf79c8f5abeada18852ffa04f54d5eb6ead47af23ca0cd0fb8126c372c8eb2e49c165292c3ccc5d9c22bdd347f1377d95595a56ee1ad60a829bd93e0a691d2885e403119d0cc6d78778a32fd428036f3e5a3a90c71c8c14018dec227c438e6171401a13eedee695a137f5158401091bce506b4598c2440b1ec32068b6845c7084965e396478221c9623dd780c9fe67d03ce7535e26a132651b0b3023ddf03201c814e3cfb4f93711135e9f54ee1119828fffd729dc74d986b1f316bf3084e8c166c4933820bf6b8b7cd390bd5393777831ca59f4481995fa35343698058dea248c89edeb07ebb999c7ab46456b8f2fd0f5176757bcd06132c3e98c,
    '4000':0x6fdba01cce885e9e7726b7c310e480d477e71caf59de0fcbf3f24f7291b591455d8263ae8f5834457b539ebdb78f67d5c20e288bd9003fd84d461728dc63fbe6cd5b3713db6512e79e98bb51c621bd690dfd441c67d5dd745a6e2f632c7d22de1145832545acccac0e32a5dfe13684aaa7a6ab27cc3bb587b627290669a846e149718f85ee57f49d6f07cf6123b99510911628006a536ab401336543d00581a6a445e58fe48fccf50ccbd0f4608299b464dbb13ccc8bf8bf8ca11e2358d7df800c4e1f81f57d773d85bb71de456671765217f1196566762033c2a75dd3172895284e682b3fbb86eb8e185edf264ec78dfa36de089651e1328e00f637408de1b64cd070ab0578c941f77d86040260852ae9d758d39eb90ceae4ee008618d9eb89e13b49efcdde72fa633ae1782699a73d494fe341514596ac1252d1e936441beb252af75be97a688b56442255d3e6d4c8fd5da2187573d1eeabef0c2fb7c8d38e8d0e59de7c55ab6d316c866f439cec675a6c43fdfd3ab173acff96c803745e0aecef4f3b95906ad3f277a9b137da6d70f374d44b374730f562a5d8179a1b8ed7206229815c5109c5dc58e89b7e63c63956102df1af5494b1547241cc8e57f0b85ffcb08b3aabb52f7e56ab306edcf2f182667fb73af6052ea652dea64a9daf71b2e8382b1a8e78b00d930ffba51b88aa6b12f0ea58ac62f
}


if __name__ == "__main__":
    set_random_seed(42) # Always get same curve

    # Choose security level and parameter set name
    lvl = '500'
    lvl = '1000'
    lvl = '1500'
    lvl = '2000'
    lvl = '4000'

    # PEGASIS setup
    name = lvl + 'P'
    p = peg_primes[lvl]
    A = peg_curves[lvl]

    # qt-P setup
    name = lvl
    p = qtp_primes[lvl]
    A = qtp_curves[lvl]

    print(f'Parameter set {name}')
    assert is_prime(p)

    # If needed, generate new starting curve
    # A = starting_curve(p)
    # print(f'{hex(A) = }')

    # Compute parameters
    data = gen_params(p, A)

    # Automatically generates `params/{name}.json` file that can be loaded with
    # PEGASIS(name)
    fname = Path(__file__).parent / 'params' / f'{name}.json'
    if fname.is_file():
        _x = input(f'Level {name} already existing; override? [y/N]')
        if _x.upper() != 'Y':
            exit()
    with open(fname, 'w') as fh:
        fh.write(json.dumps(data))







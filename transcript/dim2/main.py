import time

from sage.all import GF, EllipticCurve

from dim1 import ThetaCGL, ThetaCGLRadical4, ThetaCGLRadical8
from dim2 import ThetaCGLDim2, ThetaCGLDim2Radical4
from dim3 import ThetaCGLDim3

from utilities import print_info


def time_function_ns(f):
    t0 = time.process_time_ns()
    eval(f)
    return time.process_time_ns() - t0


def time_ms(f):
    v = time_function_ns(f)
    return v / 1_000_000


def to_hex_str(a):
    p = a.parent().characteristic()
    byte_len = (p.nbits() + 7) // 8
    a0, a1 = a.list()
    a0_bytes = int(a0).to_bytes(byte_len, byteorder="little")
    a1_bytes = int(a1).to_bytes(byte_len, byteorder="little")

    return (a0_bytes + a1_bytes).hex()

def fmt_list(ele):
    ele = str(ele)
    ele = ele.replace("[", "")
    ele = ele.replace("]", "")
    ele = ele.replace("'", "")
    return ele

def fmt_little_u64(res):
    out = []
    for r in res:
        num = r[2:]
        new_num = num.zfill(16)
        new_num = new_num.upper()
        new_num = "0x" + new_num
        out.append(new_num)
    return out

def to_little_u64(x):
    y = int(x)
    res = []
    while y:
        tmp = y % 2**64
        res.append(hex(tmp))
        y >>= 64
    if not res:
        res = ['0x0']
    ele = fmt_little_u64(res)
    return fmt_list(ele)

def print_fp2_to_little_u64(x):
    print(f"re = {to_little_u64(x[0])}")
    print(f"im = {to_little_u64(x[1])}")

def check(O0, O1, O2):
    print(
        f"Are the isogeneous curves isogeneous? {O0.cardinality() == O1.cardinality()}, {O0.cardinality() == O2.cardinality()}"
    )
    print(
        f"Are the isogeneous curves the same? {O1.j_invariant() == O2.j_invariant()}, {O0.j_invariant(), O1.j_invariant(), O2.j_invariant()}"
    )

# sha256("Bristol 2023")
MESSAGE = [
    1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0,
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1,
    0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0,
    0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1,
    1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1,
]


def dim_two_example():
    print_info("Example in dim 2 (Two radical)")

    import os
    try:
        os.remove('zk_radical.txt')
    except:
        pass

    p = 2**127 - 1
    F = GF(p**2, name="i", modulus=[1, 0, 1])
    E0 = EllipticCurve(F, [1, 0])

    O0 = ThetaCGLDim2.from_elliptic_curves(E0, E0)
    hash_1 = O0.hash(MESSAGE)
    print(f"Hashing test 1: {hash_1}")

if __name__ == "__main__":
    dim_two_example()

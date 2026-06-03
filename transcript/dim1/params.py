from sage.all import ZZ, is_pseudoprime

def set_params(lvl):
    if lvl == 0:
        p = ZZ(5)*ZZ(2)**248 - 1
    else:
        assert False, "not valid lvl"
    assert is_pseudoprime(p)
    return p

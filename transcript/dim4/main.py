import sys
from tqdm import tqdm
from time import time
import logging

from sage.all import *

from qt_pegasis import qtPegasis
import os

"""
This file requires the original pegasis repository to be imported as a
subdirectory to cross check results. It can be downloaded with
```
git clone --recurse-submodules git@github.com:pegasis4d/pegasis.git .old_pegasis
```
"""

# Setup logging
logging.getLogger('qt_pegasis').setLevel(logging.INFO)

try:
    os.remove('zk_radical.txt')
except:
    pass
rr = randint(1, 2**16)
print(f'{rr = }\n====================')
set_random_seed(rr)

# Benchmark parameters
lvl = '500'

EGA = qtPegasis(lvl) # adding P for PEGASIS parameter set
order = EGA.K.order_of_conductor(2)


while True:
    ell = random_prime(2**100)
    ids = [I[0] for I in factor(order.fractional_ideal(ell))]
    if len(ids) == 2:
        break

a = None
for I in ids:
    check = I.gens()[1][0]
    if check < 0:
        a = I
        break
assert a

ell, alpha = a.gens_two()

aux_P = EGA.E_start.random_point()
Ea, Eabar = EGA.qt_action((ZZ(ell), alpha), ret_twist=True, aux_point = aux_P)



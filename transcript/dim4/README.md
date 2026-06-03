# qt-PEGASIS

## Code structure

- Main functions:
    - `qt_pegasis.py`: main algorithm class
    - `norm_eq.py`: solving the norm equation
- Subroutines:
    - `sos.py` and `const_precomp.py`: solving sums of squares
    - `ideals.py`: ideal helpers
    - `xonly.py`: x-only arithmetic
    - `hd_helpers`: wrapper for 4D theta isogenies
    - `theta_lib/`: theta isogenies
- Parameters:
    - `params.py`: parameters loading
    - `params/`: parameter sets for different security levels
    - `pgen.py`: generate new parameters given p and A
- Benchmarking and testing
    - `benchmarks/`

## Example usage

To run an action, just type in sage:
```
from qt_pegasis import qtPegasis

lvl = '500P'
EGA = qtPegasis(lvl)
frak_a = EGA.sample_ideal()
EGA.qt_action(frak_a)
```

The level correspond to the bitsize of the base prime; the `P` at the end
denotes PEGASIS primes, while a number without `P` denotes qtPegasis primes.
Available levels are 500, 1000, 1500, 2000, 4000. New parameters can be
generated as described below.

The function `qt_action` assumes the ideal to be a pair `[ell, omega-lambda]`.
To act with a `sage` ideal the wrapper `sage_action` can be used as follows:

```
from qt_pegasis import qtPegasis

lvl = '500P'
EGA = qtPegasis(lvl)
frak_a = EGA.sample_sage_ideal()
EGA.sage_action(frak_a)
```

Warning: `sage` structures may cause a significant slowdown especially at
higher levels.

## Parameters and parameter generation

Parameter sets for different security levels are stored in the `params/` folder
in `json` format. For security level `lvl` the file `params/{lvl}.json`
contains the qt-Pegasis parameter set, while `params/{lvl}P.json` contains the
PEGASIS parameter set. To create a new parameter set, follow the instructions
in `pgen.py`. This generates a new file `params/name.json` that can be later
loaded with `qtPegasis(name)`.

## Logging

Additional information is available at runtime by activating logging. Loggers
for `qt_pegasis` and `hd_helpers` can be made verbose with
```
logging.getLogger('qt_pegasis').setLevel(logging.INFO)
logging.getLogger('norm_eq').setLevel(logging.INFO)
```
The default level is `logging.WARNING` (no printing), while `logging.INFO`
prints timings for the main steps and `logging.DEBUG` adds times for
subroutines.

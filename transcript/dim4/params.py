from sage.all import *
import json
from pathlib import Path

def qt_params(level):
    """
    Load parameters for qt-Pegasis. Avaliable parameter sets:
    - 500|1000|15000|2000|4000: qt-Pegasis parameters
    - 500P|1000P|1500P|2000P|4000P: PEGASIS parameters
    To add new ones, use `pgen.py`
    """
    fh_path = Path(__file__).absolute()
    main_dir = fh_path.parent
    fname = main_dir / 'params' / f'{level}.json'
    if not fname.is_file():
        raise ValueError(f'Unknown security level {level}')

    with open(fname, 'r') as fh:
        data = json.loads(fh.read())
    return data


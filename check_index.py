
import os, re
from pathlib import Path

ROOT = Path(".")
for area in ['Analysis', 'Probability', 'Dynamics', 'MeasureTheory']:
    assembly = (ROOT / 'CKMA' / (area + '.lean')).read_text()
    expected = {'.'.join(p.relative_to(ROOT).with_suffix('').parts)
                for p in (ROOT / 'CKMA' / area).rglob('*.lean')}
    actual = set(re.findall(r'^public import (\S+)', assembly, re.M))
    
    missing = expected - actual
    extra = actual - expected
    if missing or extra:
        print(f"Mismatch in {area}:")
        print(f"  Missing (should be in {area}.lean): {missing}")
        print(f"  Extra (should be removed from {area}.lean): {extra}")

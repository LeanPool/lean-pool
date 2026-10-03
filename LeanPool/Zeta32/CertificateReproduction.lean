/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module
public import LeanPool.Zeta32.FstarDefs

/-!
# Reproducing the finite point certificates

The upstream comments cite `choose_params.py`, `gen_points.py`, and `b2_numerics.py`,
but those scripts are absent from the pinned upstream tree. This replacement procedure
reproduces the rational witnesses used by the fifteen weight and density point proofs.
It uses Python's standard library only and exact rational arithmetic throughout.
Run the following block from the repository root with Python 3.13 or later.
The target lower bounds and support endpoint are read from `FstarDefs.lean`.

For weight bounds, the arctangent modes and log scaling/Taylor lengths below are the
explicit inputs of `FstarPointsW/Points.lean`. `FstarPointsW/Bounds.lean` proves each
atom enclosure. A mode or Taylor length can be changed and searched in a finite range;
accept it only if the exact `weight_bound` exceeds the chosen target.

For density bounds, bracket each square root on the grid with denominator 100000.
Round the rational product bound down to five significant decimal digits to obtain `P`.
Normalize `P` by its largest power of two and use the four-term positive logarithm series
from `FstarPointsRho/Basic.lean`. The output gives the `sl`, `sh`, `U1`, `U5`, `P`, and
log exponent witnesses used by `rho_ge_of` in `FstarPointsRho/Points.lean`.
For example, point one yields `sl = 186297/100000`, `sh = 93149/50000`,
`P = 29440000`, and exponent 24. The target bounds are deliberate input margins;
they are not inferred from floating-point estimates.

Changing the support endpoint requires fresh mass/support and energy bounds as well as
these point witnesses. For a new weight target, search the direct or shifted arctangent
modes, nonnegative log scales, and positive Taylor lengths until the exact assertion holds.
For a new density target, refine the square-root grid and the logarithm series if needed.
Update the corresponding Lean proof inputs and run
`lake build LeanPool.Zeta32.FstarPointsW LeanPool.Zeta32.FstarPointsRho LeanPool.Zeta32`.
The Lean proofs, including their rational side conditions, certify every accepted result.

```python
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json
import re

root = Path("LeanPool/Zeta32")
source = (root / "FstarDefs.lean").read_text()
a = F(re.search(r"def aMinus : ℝ := ([0-9/]+)", source)[1])

def table(name):
    body = source.split("def " + name + " : Fin 15 → ℚ := ![", 1)[1].split("]", 1)[0]
    values = [F(x) for x in re.findall(r"([0-9]+/[0-9]+)\s*:\s*ℚ", body)]
    assert len(values) == 15
    return values

weight, density = table("Wlow"), table("Rlow")
pi_low, pi_high = F(3141592, 1000000), F(31416, 10000)
log_two_low, log_two_high = F(6931471803, 10**10), F(6931471808, 10**10)
log_scale = [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]
log_terms = [1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 2, 1, 1, 1]
small_log_terms = [1] * 12 + [2, 1, 1]

def square_root_floor(value, denominator=100000):
    scaled = value * denominator**2
    return F(isqrt(scaled.numerator // scaled.denominator), denominator)

def arctan_three(t):
    return t - t**3 / 3 + t**5 / 5

def arctan_four(t):
    return arctan_three(t) - t**7 / 7

u1 = square_root_floor(1 + a*a) + F(1, 100000)
u5 = square_root_floor(25 + a*a)
rows = []
for index in range(15):
    x = a * (index + 1) / 16
    if index < 6:
        mode, arctan_lower = "direct", arctan_four(x)
    elif index < 8:
        mode = "shift_neg"
        arctan_lower = pi_low / 4 - arctan_three((1-x) / (1+x))
    else:
        mode = "shift_pos"
        arctan_lower = pi_low / 4 + arctan_four((x-1) / (x+1))
    scale, length = log_scale[index], log_terms[index]
    u = 1 - (1+x*x) / 2**scale
    assert abs(u) < 1
    log_upper = scale * log_two_high - sum(u**j / j for j in range(1, length+1))
    log_upper += abs(u)**(length+1) / (1-abs(u))
    t, length_small = x*x / 25, small_log_terms[index]
    assert 0 <= t < 1
    log_lower = -sum((-t)**j / j for j in range(1, length_small+1))
    log_lower -= t**(length_small+1) / (1-t)
    weight_bound = F(2, 3) * (2*x*arctan_lower - log_upper + pi_low*x/4
                            - x*arctan_three(x/5)/2 + 5*log_lower/4)
    assert weight[index] <= weight_bound
    lower = square_root_floor(a*a - x*x)
    upper = lower + F(1, 100000)
    assert lower**2 <= a*a - x*x <= upper**2
    assert 1+a*a <= u1**2 and u5**2 <= 25+a*a and upper < u5
    cap = (a+lower)/(a-lower) * ((u1+lower)/(u1-lower))**4
    cap /= (u5+upper)/(u5-upper)
    unit = F(1, 10000)
    while cap / unit >= 100000:
        unit *= 10
    p = (cap // unit) * unit
    exponent = 0
    while 2**(exponent+1) <= p:
        exponent += 1
    z = p / 2**exponent
    t = (z-1)/(z+1)
    log_bound = exponent * log_two_low + 2 * sum(t**j/j for j in [1, 3, 5, 7])
    assert 12 * pi_high * density[index] <= log_bound
    rows.append(dict(point=index+1, x=str(x), weight=str(weight[index]),
                     arctan=mode, log_scale=scale, log_terms=length,
                     small_log_terms=length_small, lower=str(lower), upper=str(upper),
                     u1=str(u1), u5=str(u5), p=str(p), exponent=exponent,
                     density=str(density[index])))
print(json.dumps(rows, indent=2))
```
-/

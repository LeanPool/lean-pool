/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext200000210000
import Mathlib.Tactic.FinCases

/-!
# Sext 200000 210000 6

Kernel-checked forced assignments and closed-interval exclusions.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

-- Generated checkpoints are proposals; all acceptance proofs are checked by the kernel.

namespace ConwaySoifer.Simplified.Certificates
open ConwaySoifer.Certificates
namespace Sext200000210000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner3Part0 : FanWitness := (.next ([-525000000000], [2925000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-1125000000000], [4875000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-600000000000], [1950000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-2025000000000], [5625000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-2100000000000,
    9000000000000], [5400000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-2925000000000],
    [7050000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1800000000000], [4125000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3450000000000, 9000000000000], [7200000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1650000000000], [3225000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-2850000000000, 9000000000000], [5250000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-2700000000000], [4500000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-3300000000000], [5400000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-3300000000000], [5250000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3900000000000],
    [5400000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5250000000000], [7200000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5250000000000, 0], [7050000000000, 9000000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-1350000000000], [1800000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-600000000000], [750000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    (.next ([-1650000000000], [2025000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next
    ([-1050000000000], [1275000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-5400000000000,
    0], [6450000000000, 9000000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-4650000000000],
    [5250000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3075000000000], [3300000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-3750000000000], [3900000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.terminal (some (0, 8, 6)) (some (0, 8, 6)) (some (0, 8,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner3Part1 : FanWitness := (.next ([2325000000000], [1800000000000]) (some (7, 0, 5))
    (some (7, 0, 5)) (.next ([3750000000000, 9000000000000], [3450000000000, -9000000000000]) (some
    (7, 0, 5)) (some (7, 0, 5)) (.next ([1575000000000], [1650000000000]) (some (7, 0, 5)) (some (7,
    0, 5)) (.next ([2400000000000, 9000000000000], [2850000000000, -9000000000000]) (some (7, 0, 5))
    (some (7, 0, 5)) (.next ([1800000000000], [2700000000000]) (some (7, 0, 5)) (some (7, 0, 5))
    (.next ([2100000000000], [3300000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next
    ([1950000000000], [3300000000000]) (some (7, 0, 5)) (some (7, 0, 5)) (.next ([1500000000000],
    [3900000000000]) (some (7, 0, 5)) (some (7, 8, 5)) (.next ([1950000000000], [5250000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1800000000000, 9000000000000], [5250000000000]) (some
    (7, 8, 5)) (some (7, 8, 5)) (.next ([450000000000], [1350000000000]) (some (7, 8, 5)) (some (7,
    8, 5)) (.next ([150000000000], [600000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next
    ([375000000000], [1650000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([225000000000],
    [1050000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([1050000000000, 9000000000000],
    [5400000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([600000000000], [4650000000000])
    (some (7, 8, 5)) (some (7, 8, 5)) (.next ([225000000000], [3075000000000]) (some (7, 8, 5))
    (some (7, 8, 5)) (.next ([150000000000], [3750000000000]) (some (7, 8, 5)) (some (7, 8, 5))
    (.next ([0], [4650000000000]) (some (7, 8, 5)) (some (7, 8, 5)) (.next ([-225000000000,
    9000000000000], [5625000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-225000000000],
    [2100000000000]) (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-375000000000], [3000000000000])
    (some (0, 8, 6)) (some (0, 8, 6)) (.next ([-750000000000], [5400000000000]) (some (0, 8, 6))
    (some (0, 8, 6)) (.next ([-150000000000], [900000000000]) (some (0, 8, 6)) (some (0, 8, 6))
    fan49Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner0Part0 : FanWitness := (.next ([-3225000000000], [5475000000000]) (some (10, 4, 10))
    (some (10, 4, 10)) (.next ([-1860000000000], [3135000000000]) (some (10, 4, 10)) (some (10, 4,
    10)) (.next ([-600000000000], [975000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next
    ([-3615000000000], [5475000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next
    ([-1875000000000], [2775000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next
    ([-3975000000000], [5850000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next
    ([-2286000000000, 2370000000000], [3234000000000, 2370000000000]) (some (10, 4, 10)) (some (10,
    4, 10)) (.next ([-4200000000000], [5850000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-1785000000000], [2385000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-225000000000],
    [300000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-1785000000000], [2160000000000])
    (some (1, 4, 10)) (some (1, 5, 10)) (.next ([-6000000000000], [7260000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-4215000000000], [5100000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    (.next ([-6360000000000], [7635000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-4575000000000], [5475000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-4215000000000], [4875000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-4575000000000], [5250000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-5925000000000], [6600000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next ([-3714000000000,
    -2370000000000], [4026000000000, -2370000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-4074000000000, -2370000000000], [4401000000000, -2370000000000]) (some (1, 5, 10)) (some (2,
    5, 10)) (.next ([-6000000000000], [6375000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next
    ([-6675000000000], [6975000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next ([-360000000000],
    [375000000000]) (some (2, 5, 10)) (some (2, 5, 10)) (.next ([-6900000000000], [6975000000000])
    (some (2, 5, 10)) (some (3, 5, 10)) (.terminal (some (3, 5, 10)) (some (3, 5, 10)) (some (3, 5,
    10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner0Part1 : FanWitness := (.next ([15000000000], [360000000000]) (some (10, 4, 6)) (some
    (10, 4, 6)) (.next ([75000000000], [6900000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next
    ([0], [225000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-225000000000],
    [6975000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-300000000000], [9060000000000])
    (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-600000000000], [9135000000000]) (some (10, 4, 6))
    (some (10, 4, 6)) (.next ([-126000000000, 2370000000000], [1449000000000, 2370000000000]) (some
    (10, 4, 6)) (some (10, 4, 6)) (.next ([-675000000000], [7275000000000]) (some (10, 4, 6)) (some
    (10, 4, 6)) (.next ([-900000000000], [7275000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next
    ([-975000000000], [7350000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-225000000000],
    [1575000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-1200000000000], [7350000000000])
    (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-375000000000], [2160000000000]) (some (10, 4, 6))
    (some (10, 4, 6)) (.next ([-1248000000000, -4740000000000], [6774000000000, 2370000000000])
    (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-1548000000000, -4740000000000], [6849000000000,
    2370000000000]) (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-600000000000], [2385000000000])
    (some (10, 4, 6)) (some (10, 4, 6)) (.next ([-975000000000], [3135000000000]) (some (10, 4, 6))
    (some (10, 4, 6)) (.next ([-375000000000], [975000000000]) (some (10, 4, 6)) (some (10, 4, 10))
    (.next ([-501000000000, 2370000000000], [1074000000000, 2370000000000]) (some (10, 4, 10)) (some
    (10, 4, 10)) (.next ([-600000000000], [1200000000000]) (some (10, 4, 10)) (some (10, 4, 10))
    (.next ([-1560000000000], [3060000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next
    ([-1074000000000, -2370000000000], [1923000000000, 4740000000000]) (some (10, 4, 10)) (some (10,
    4, 10)) (.next ([-2865000000000], [5100000000000]) (some (10, 4, 10)) (some (10, 4, 10)) (.next
    ([-1575000000000], [2700000000000]) (some (10, 4, 10)) (some (10, 4, 10))
    fan50Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner0Part2 : FanWitness := (.next ([2235000000000], [2865000000000]) (some (10, 3, 5))
    (some (10, 3, 5)) (.next ([1125000000000], [1575000000000]) (some (10, 3, 5)) (some (10, 3, 5))
    (.next ([2250000000000], [3225000000000]) (some (10, 3, 5)) (some (10, 4, 5)) (.next
    ([1275000000000], [1860000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next ([375000000000],
    [600000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next ([1860000000000], [3615000000000])
    (some (10, 4, 5)) (some (10, 4, 5)) (.next ([900000000000], [1875000000000]) (some (10, 4, 5))
    (some (10, 4, 5)) (.next ([1875000000000], [3975000000000]) (some (10, 4, 5)) (some (10, 4, 5))
    (.next ([948000000000, 4740000000000], [2286000000000, -2370000000000]) (some (10, 4, 5)) (some
    (10, 4, 5)) (.next ([1650000000000], [4200000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next
    ([600000000000], [1785000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next ([75000000000],
    [225000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next ([375000000000], [1785000000000])
    (some (10, 4, 5)) (some (10, 4, 5)) (.next ([1260000000000], [6000000000000]) (some (10, 4, 5))
    (some (10, 4, 5)) (.next ([885000000000], [4215000000000]) (some (10, 4, 5)) (some (10, 4, 5))
    (.next ([1275000000000], [6360000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next
    ([900000000000], [4575000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next ([660000000000],
    [4215000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next ([675000000000], [4575000000000])
    (some (10, 4, 5)) (some (10, 4, 5)) (.next ([675000000000], [5925000000000]) (some (10, 4, 5))
    (some (10, 4, 5)) (.next ([312000000000, -4740000000000], [3714000000000, 2370000000000]) (some
    (10, 4, 5)) (some (10, 4, 5)) (.next ([327000000000, -4740000000000], [4074000000000,
    2370000000000]) (some (10, 4, 5)) (some (10, 4, 5)) (.next ([375000000000], [6000000000000])
    (some (10, 4, 5)) (some (10, 4, 5)) (.next ([300000000000], [6675000000000]) (some (10, 4, 5))
    (some (10, 4, 6)) fan50Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan50Owner4Part0 : FanWitness := (.next ([1425000000000], [375000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([5250000000000], [1800000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([6240000000000], [2760000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([990000000000],
    [960000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1800000000000, 9000000000000],
    [3825000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1800000000000,
    9000000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1125000000000],
    [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1740000000000], [7260000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([615000000000], [2760000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([750000000000], [6300000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0, 9000000000000], [5250000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([0], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-960000000000,
    9000000000000], [7200000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-375000000000], [1800000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1800000000000],
    [7050000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2760000000000], [9000000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-960000000000], [1950000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-3825000000000, 9000000000000], [5625000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4500000000000], [6300000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-4500000000000], [5625000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-7260000000000], [9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-2760000000000], [3375000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6300000000000],
    [7050000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-5250000000000, 9000000000000],
    [5250000000000]) (some (0, 5, 5)) (some (0, 5, 5)) (.terminal (some (0, 5, 5)) (some (0, 5, 5))
    (some (0, 5, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan51Owner3Part0 : FanWitness := (.next ([-750000000000], [5400000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-1425000000000], [8625000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-1575000000000], [8025000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-1800000000000], [6975000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-1575000000000,
    9000000000000], [5400000000000, -9000000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-2025000000000], [5625000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-2925000000000],
    [7050000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-1800000000000], [4125000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3375000000000], [7200000000000]) (some (0, 3, 5))
    (some (0, 3, 5)) (.next ([-3075000000000], [6450000000000]) (some (0, 3, 5)) (some (0, 3, 5))
    (.next ([-1575000000000], [3075000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
    ([-2115000000000], [3915000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-3300000000000],
    [5400000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-4440000000000, 9000000000000],
    [6240000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-2415000000000], [3375000000000])
    (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-5250000000000, 0], [7050000000000, 9000000000000])
    (some (0, 3, 5)) (some (0, 7, 5)) (.next ([-600000000000], [750000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-1650000000000], [2025000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1050000000000], [1275000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-5400000000000, 0], [6450000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-5250000000000], [6240000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4650000000000],
    [5490000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3600000000000], [4215000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2325000000000, 9000000000000], [2325000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.terminal (some (0, 7, 5)) (some (0, 7, 5)) (some (0, 7,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan51Owner3Part1 : FanWitness := (.next ([6450000000000], [1575000000000]) (some (6, 0, 7))
    (some (6, 0, 7)) (.next ([5175000000000], [1800000000000]) (some (6, 0, 7)) (some (6, 0, 7))
    (.next ([3825000000000, 0], [1575000000000, -9000000000000]) (some (6, 0, 7)) (some (6, 0, 7))
    (.next ([3600000000000], [2025000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
    ([4125000000000], [2925000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([2325000000000],
    [1800000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([3825000000000], [3375000000000])
    (some (6, 0, 7)) (some (6, 0, 7)) (.next ([3375000000000], [3075000000000]) (some (6, 0, 7))
    (some (6, 0, 7)) (.next ([1500000000000], [1575000000000]) (some (6, 0, 7)) (some (6, 0, 7))
    (.next ([1800000000000], [2115000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
    ([2100000000000], [3300000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([1800000000000,
    9000000000000], [4440000000000, -9000000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
    ([960000000000], [2415000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([1800000000000,
    9000000000000], [5250000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([150000000000],
    [600000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([375000000000], [1650000000000]) (some
    (6, 0, 7)) (some (6, 1, 7)) (.next ([225000000000], [1050000000000]) (some (6, 1, 7)) (some (6,
    1, 7)) (.next ([1050000000000, 9000000000000], [5400000000000]) (some (6, 1, 7)) (some (6, 2,
    7)) (.next ([990000000000], [5250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([840000000000], [4650000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([615000000000],
    [3600000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([0, 9000000000000], [2325000000000,
    -9000000000000]) (some (6, 2, 7)) (some (6, 3, 7)) (.next ([0], [5250000000000]) (some (6, 3,
    7)) (some (6, 3, 7)) (.next ([-225000000000, 9000000000000], [5625000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) fan51Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner3Part0 : FanWitness := (.next ([0], [5250000000000]) (some (6, 7, 4)) (some (6, 7, 5))
    (.next ([-225000000000, 9000000000000], [5625000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-750000000000], [5400000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-2025000000000], [5625000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2925000000000],
    [7050000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1800000000000], [4125000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3075000000000], [6450000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3000000000000], [5625000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-2115000000000], [3915000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-4050000000000], [6900000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3525000000000],
    [5925000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4650000000000], [7650000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3300000000000], [5400000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-1410000000000], [2010000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-5250000000000, 0], [7050000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-600000000000], [750000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-1650000000000], [2025000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1050000000000],
    [1275000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5400000000000, 0], [6450000000000,
    9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5250000000000], [6240000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4650000000000], [5490000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-3600000000000], [4215000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-7650000000000], [8250000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-2325000000000, 9000000000000], [2325000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.terminal
    (some (0, 7, 5)) (some (0, 7, 5)) (some (0, 7, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner4Part0 : FanWitness := (.next ([1425000000000], [375000000000]) (some (4, 1, 5)) (some
    (4, 1, 5)) (.next ([5250000000000], [1800000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([2025000000000], [750000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1050000000000],
    [1350000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3150000000000], [5250000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1800000000000, 9000000000000], [3825000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1800000000000, 9000000000000],
    [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1125000000000], [4500000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1050000000000, 9000000000000], [6600000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([750000000000], [6300000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [5250000000000, -9000000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [4500000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([-750000000000], [8400000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-375000000000], [1800000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1800000000000],
    [7050000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-750000000000], [2775000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1350000000000], [2400000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([-5250000000000], [8400000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-3825000000000, 9000000000000], [5625000000000]) (some (0, 1, 3)) (some (0, 5, 3))
    (.next ([-4500000000000], [6300000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-4500000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-6600000000000, 9000000000000], [7650000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-6300000000000], [7050000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5250000000000,
    9000000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan55Owner3Part0 : FanWitness := (.next ([0], [5250000000000]) (some (6, 7, 4)) (some (6, 7, 5))
    (.next ([-225000000000, 9000000000000], [5625000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-750000000000], [5400000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-1800000000000], [5175000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2025000000000],
    [5625000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2925000000000], [7050000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-1800000000000], [4125000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-2850000000000], [6450000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-3075000000000], [6675000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-3075000000000], [6450000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3450000000000],
    [7200000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2115000000000], [3915000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5400000000000, 9000000000000], [9000000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3300000000000], [5400000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-4440000000000, 9000000000000], [6240000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-5250000000000, 0], [7050000000000, 9000000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-600000000000], [750000000000]) (some (0, 7, 5)) (some (0, 7, 5))
    (.next ([-1650000000000], [2025000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-1050000000000], [1275000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5400000000000,
    0], [6450000000000, 9000000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-5250000000000],
    [6240000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-4650000000000], [5490000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-3600000000000], [4215000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.next ([-2325000000000, 9000000000000], [2325000000000]) (some (0, 7, 5))
    (some (0, 7, 5)) (.terminal (some (0, 7, 5)) (some (0, 7, 5)) (some (0, 7,
    5)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6675000000000, 9000000000000], [525000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4650000000000], [375000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1575000000000], [750000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([4875000000000], [2325000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([2325000000000], [1950000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([2400000000000, 9000000000000], [2850000000000, -9000000000000]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([1800000000000, 9000000000000], [5625000000000, 0]) (some (0, 1, 2)) (some (0,
      1, 2)) (.next ([600000000000], [4650000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [5625000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-525000000000, 9000000000000],
      [7200000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([-375000000000],
      [5025000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-750000000000], [2325000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2325000000000], [7200000000000]) (some (0, 1, 3))
      (some (4, 1, 3)) (.next ([-1950000000000], [4275000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-2850000000000, 9000000000000], [5250000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-5625000000000, 0], [7425000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 2, 3))
      (.next ([-4650000000000], [5250000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some
      (4, 2, 3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact excluded48_2
    · exact (hj rfl).elim
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_0 : ExcludedOn (model49.B 0 ++ [step49.q]) 9000000000000 (model49.caps 0)
    (model49.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [225000000000,
      -9000000000000]) (some (6, 0, 8)) (some (7, 0, 8)) (.next ([1875000000000], [225000000000])
      (some (7, 0, 8)) (some (7, 0, 8)) (.next ([2625000000000], [375000000000]) (some (7, 0, 8))
      (some (7, 0, 8)) (.next ([4650000000000], [750000000000]) (some (7, 0, 8)) (some (7, 0, 8))
      (.next ([750000000000], [150000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next
      ([2400000000000], [525000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([3750000000000],
      [1125000000000]) (some (7, 0, 8)) (some (7, 0, 8)) (.next ([1350000000000], [600000000000])
      (some (7, 0, 5)) (some (7, 0, 5)) (.next ([3600000000000], [2025000000000]) (some (7, 0, 5))
      (some (7, 0, 5)) (.next ([3300000000000, 9000000000000], [2100000000000, -9000000000000])
      (some (7, 0, 5)) (some (7, 0, 5)) (.next ([4125000000000], [2925000000000]) (some (7, 0, 5))
      (some (7, 0, 5)) fan49Owner3Part1)))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded49_0
    · exact excluded49_1
    · exact excluded49_2
    · exact excluded49_3
    · exact (hj rfl).elim
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_0 : ExcludedOn (model50.B 0 ++ [step50.q]) 9000000000000 (model50.caps 0)
    (model50.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6750000000000], [225000000000]) (some (10, 3,
      5)) (some (10, 3, 5)) (.next ([8760000000000], [300000000000]) (some (10, 3, 5)) (some (10, 3,
      5)) (.next ([8535000000000], [600000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
      ([1323000000000, 4740000000000], [126000000000, -2370000000000]) (some (10, 3, 5)) (some (10,
      3, 5)) (.next ([6600000000000], [675000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
      ([6375000000000], [900000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([6375000000000],
      [975000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([1350000000000], [225000000000])
      (some (10, 3, 5)) (some (10, 3, 5)) (.next ([6150000000000], [1200000000000]) (some (10, 3,
      5)) (some (10, 3, 5)) (.next ([1785000000000], [375000000000]) (some (10, 3, 5)) (some (10, 3,
      5)) (.next ([5526000000000, -2370000000000], [1248000000000, 4740000000000]) (some (10, 3, 5))
      (some (10, 3, 5)) (.next ([5301000000000, -2370000000000], [1548000000000, 4740000000000])
      (some (10, 3, 5)) (some (10, 3, 5)) (.next ([1785000000000], [600000000000]) (some (10, 3, 5))
      (some (10, 3, 5)) (.next ([2160000000000], [975000000000]) (some (10, 3, 5)) (some (10, 3, 5))
      (.next ([600000000000], [375000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
      ([573000000000, 4740000000000], [501000000000, -2370000000000]) (some (10, 3, 5)) (some (10,
      3, 5)) (.next ([600000000000], [600000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next
      ([1500000000000], [1560000000000]) (some (10, 3, 5)) (some (10, 3, 5)) (.next ([849000000000,
      2370000000000], [1074000000000, 2370000000000]) (some (10, 3, 5)) (some (10, 3, 5))
      fan50Owner0Part2))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4650000000000], [375000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([2160000000000], [1590000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([3375000000000], [2865000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([4560000000000, 9000000000000], [4440000000000, -9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([2400000000000, 9000000000000], [2850000000000, -9000000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([2760000000000], [6240000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([1800000000000, 9000000000000], [5625000000000, 0]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([600000000000], [4650000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([0],
      [5625000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-375000000000], [5025000000000])
      (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-1590000000000], [3750000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-2865000000000], [6240000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-4440000000000, 9000000000000], [9000000000000, 0]) (some (0, 1, 3)) (some (4, 1, 3))
      (.next ([-2850000000000, 9000000000000], [5250000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-6240000000000], [9000000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next
      ([-5625000000000, 0], [7425000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-4650000000000], [5250000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6240000000000], [960000000000, -9000000000000])
      (some (5, 0, 5)) (some (5, 1, 5)) fan50Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_5 : ExcludedOn (model50.B 5 ++ [step50.q]) 9000000000000 (model50.caps 5)
    (model50.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded50_0
    · exact excluded50_1
    · exact excluded50_2
    · exact (hj rfl).elim
    · exact excluded50_4
    · exact excluded50_5
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [225000000000,
      -9000000000000]) (some (5, 0, 7)) (some (6, 0, 7)) (.next ([4650000000000], [750000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([7200000000000], [1425000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) fan51Owner3Part1)))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_7 : ExcludedOn (model51.B 7 ++ [step51.q]) 9000000000000 (model51.caps 7)
    (model51.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded51_0
    · exact excluded51_1
    · exact (hj rfl).elim
    · exact excluded51_3
    · exact excluded51_4
    · exact excluded51_5
    · exact excluded51_6
    · exact excluded51_7
    · exact excluded51_8
    · exact excluded51_9
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded52_1 : ExcludedOn (model52.B 1 ++ [step52.q]) 9000000000000 (model52.caps 1)
    (model52.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [225000000000,
      -9000000000000]) (some (5, 0, 7)) (some (6, 0, 7)) (.next ([4650000000000], [750000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([3600000000000], [2025000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([4125000000000], [2925000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([2325000000000], [1800000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next
      ([3375000000000], [3075000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([2625000000000],
      [3000000000000]) (some (6, 0, 7)) (some (6, 0, 7)) (.next ([1800000000000], [2115000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([2850000000000], [4050000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([2400000000000], [3525000000000]) (some (6, 0, 7)) (some (6, 0, 7))
      (.next ([3000000000000], [4650000000000]) (some (6, 0, 4)) (some (6, 0, 4)) (.next
      ([2100000000000], [3300000000000]) (some (6, 0, 4)) (some (6, 7, 4)) (.next ([600000000000],
      [1410000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1800000000000, 9000000000000],
      [5250000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([150000000000], [600000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([375000000000], [1650000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([225000000000], [1050000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([1050000000000, 9000000000000], [5400000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([990000000000], [5250000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([840000000000], [4650000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([615000000000],
      [3600000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([600000000000], [7650000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([0, 9000000000000], [2325000000000, -9000000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) fan52Owner3Part0)))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7650000000000], [750000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan52Owner4Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_8 : ExcludedOn (model52.B 8 ++ [step52.q]) 9000000000000 (model52.caps 8)
    (model52.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_9 : ExcludedOn (model52.B 9 ++ [step52.q]) 9000000000000 (model52.caps 9)
    (model52.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked52 : StepValid model52 9000000000000 step52 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded52_1
    · exact excluded52_2
    · exact excluded52_3
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact excluded52_8
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded53_0 : ExcludedOn (model53.B 0 ++ [step53.q]) 9000000000000 (model53.caps 0)
    (model53.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4200000000000], [300000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) (.next ([4650000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([825000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([3600000000000, 9000000000000], [2025000000000, -9000000000000]) (some (0, 1, 5)) (some (0,
      2, 5)) (.next ([4350000000000], [4875000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([1800000000000], [3825000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([750000000000,
      0], [1800000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([1800000000000,
      9000000000000], [5625000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([750000000000],
      [3600000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([600000000000], [4650000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([525000000000], [4875000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([0], [3825000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-300000000000], [4500000000000]) (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-375000000000],
      [5025000000000]) (some (0, 2, 4)) (some (0, 5, 4)) (.next ([-375000000000], [1200000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2025000000000, 9000000000000], [5625000000000, 0])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4875000000000], [9225000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-3825000000000], [5625000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-1800000000000, 9000000000000], [2550000000000, -9000000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-5625000000000, 0], [7425000000000, 9000000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-3600000000000], [4350000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-4650000000000], [5250000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4875000000000], [5400000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 0)) (some (0, 5, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_5 : ExcludedOn (model53.B 5 ++ [step53.q]) 9000000000000 (model53.caps 5)
    (model53.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_6 : ExcludedOn (model53.B 6 ++ [step53.q]) 9000000000000 (model53.caps 6)
    (model53.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_7 : ExcludedOn (model53.B 7 ++ [step53.q]) 9000000000000 (model53.caps 7)
    (model53.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000], [2550000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5400000000000], [4350000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1800000000000, 9000000000000], [3300000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([300000000000], [4350000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([0], [5100000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-2550000000000, 9000000000000], [7950000000000, -9000000000000]) (some (3, 3, 2)) (some (3,
      3, 2)) (.next ([-4350000000000], [9750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3300000000000, 9000000000000], [5100000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4350000000000], [4650000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_9 : ExcludedOn (model53.B 9 ++ [step53.q]) 9000000000000 (model53.caps 9)
    (model53.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked53 : StepValid model53 9000000000000 step53 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded53_0
    · exact (hj rfl).elim
    · exact excluded53_2
    · exact excluded53_3
    · exact excluded53_4
    · exact excluded53_5
    · exact excluded53_6
    · exact excluded53_7
    · exact excluded53_8
    · exact excluded53_9
theorem next53 : model53.insert step53 = model54 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded54_1 : ExcludedOn (model54.B 1 ++ [step54.q]) 9000000000000 (model54.caps 1)
    (model54.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4650000000000], [750000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([2850000000000, -9000000000000], [750000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([6450000000000], [3075000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1800000000000, 9000000000000], [1800000000000, 9000000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([2325000000000], [3075000000000, -9000000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([2325000000000], [4875000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1050000000000, 9000000000000], [5400000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([525000000000, -9000000000000], [6675000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([0], [1800000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-750000000000], [5400000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-750000000000,
      0], [3600000000000, -9000000000000]) (some (0, 4, 3)) none (.next ([-3075000000000],
      [9525000000000]) none none (.next ([-1800000000000, -9000000000000], [3600000000000,
      18000000000000]) none none (.next ([-3075000000000, 9000000000000], [5400000000000,
      -9000000000000]) (some (4, 4, 0)) (some (4, 4, 0)) (.next ([-4875000000000], [7200000000000])
      (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-5400000000000], [6450000000000, 9000000000000])
      (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-6675000000000, -9000000000000], [7200000000000,
      0]) (some (4, 1, 0)) (some (4, 1, 0)) (.terminal (some (4, 1, 0)) (some (4, 1, 0)) (some (4,
      1, 0))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded54_2 : ExcludedOn (model54.B 2 ++ [step54.q]) 9000000000000 (model54.caps 2)
    (model54.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_3 : ExcludedOn (model54.B 3 ++ [step54.q]) 9000000000000 (model54.caps 3)
    (model54.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_4 : ExcludedOn (model54.B 4 ++ [step54.q]) 9000000000000 (model54.caps 4)
    (model54.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_5 : ExcludedOn (model54.B 5 ++ [step54.q]) 9000000000000 (model54.caps 5)
    (model54.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_6 : ExcludedOn (model54.B 6 ++ [step54.q]) 9000000000000 (model54.caps 6)
    (model54.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3600000000000, 9000000000000], [525000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1800000000000], [2325000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1800000000000, 9000000000000], [7200000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1800000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-525000000000, 9000000000000],
      [4125000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2325000000000], [4125000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7200000000000, 9000000000000], [9000000000000, 0])
      (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1,
      2))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded54_7 : ExcludedOn (model54.B 7 ++ [step54.q]) 9000000000000 (model54.caps 7)
    (model54.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_8 : ExcludedOn (model54.B 8 ++ [step54.q]) 9000000000000 (model54.caps 8)
    (model54.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_9 : ExcludedOn (model54.B 9 ++ [step54.q]) 9000000000000 (model54.caps 9)
    (model54.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked54 : StepValid model54 9000000000000 step54 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded54_1
    · exact excluded54_2
    · exact excluded54_3
    · exact excluded54_4
    · exact excluded54_5
    · exact excluded54_6
    · exact excluded54_7
    · exact excluded54_8
    · exact excluded54_9
theorem next54 : model54.insert step54 = model55 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded55_1 : ExcludedOn (model55.B 1 ++ [step55.q]) 9000000000000 (model55.caps 1)
    (model55.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_2 : ExcludedOn (model55.B 2 ++ [step55.q]) 9000000000000 (model55.caps 2)
    (model55.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_3 : ExcludedOn (model55.B 3 ++ [step55.q]) 9000000000000 (model55.caps 3)
    (model55.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [225000000000,
      -9000000000000]) (some (5, 0, 7)) (some (6, 0, 7)) (.next ([4650000000000], [750000000000])
      (some (6, 0, 7)) (some (6, 0, 7)) (.next ([3375000000000], [1800000000000]) (some (6, 0, 7))
      (some (6, 0, 7)) (.next ([3600000000000], [2025000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([4125000000000], [2925000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next
      ([2325000000000], [1800000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next ([3600000000000],
      [2850000000000]) (some (6, 0, 3)) (some (6, 0, 3)) (.next ([3600000000000], [3075000000000])
      (some (6, 0, 3)) (some (6, 0, 3)) (.next ([3375000000000], [3075000000000]) (some (6, 0, 3))
      (some (6, 0, 3)) (.next ([3750000000000], [3450000000000]) (some (6, 0, 3)) (some (6, 0, 3))
      (.next ([1800000000000], [2115000000000]) (some (6, 0, 3)) (some (6, 7, 3)) (.next
      ([3600000000000, 9000000000000], [5400000000000, -9000000000000]) (some (6, 7, 3)) (some (6,
      7, 4)) (.next ([2100000000000], [3300000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([1800000000000, 9000000000000], [4440000000000, -9000000000000]) (some (6, 7, 4)) (some (6,
      7, 4)) (.next ([1800000000000, 9000000000000], [5250000000000]) (some (6, 7, 4)) (some (6, 7,
      4)) (.next ([150000000000], [600000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([375000000000], [1650000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([225000000000],
      [1050000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1050000000000, 9000000000000],
      [5400000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([990000000000], [5250000000000])
      (some (6, 7, 4)) (some (6, 7, 4)) (.next ([840000000000], [4650000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([615000000000], [3600000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([0, 9000000000000], [2325000000000, -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      fan55Owner3Part0)))))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded55_4 : ExcludedOn (model55.B 4 ++ [step55.q]) 9000000000000 (model55.caps 4)
    (model55.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1800000000000], [150000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([1425000000000], [375000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([5250000000000], [1800000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([2700000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1800000000000,
      9000000000000], [3825000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([1800000000000, 9000000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([1800000000000, 9000000000000], [5400000000000, -9000000000000]) (some (4, 1, 5)) (some (4,
      1, 5)) (.next ([1125000000000], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([750000000000], [6300000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0,
      9000000000000], [5250000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
      ([0], [4500000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([-150000000000],
      [1950000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-375000000000], [1800000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1800000000000], [7050000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-4500000000000], [7200000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-3825000000000, 9000000000000], [5625000000000]) (some (0, 1, 3)) (some (0, 5, 3))
      (.next ([-4500000000000], [6300000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-5400000000000, 9000000000000], [7200000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([-4500000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([-6300000000000], [7050000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5250000000000,
      9000000000000], [5250000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
      (some (0, 5, 4)) (some (0, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded55_5 : ExcludedOn (model55.B 5 ++ [step55.q]) 9000000000000 (model55.caps 5)
    (model55.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6450000000000], [150000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([7200000000000], [1800000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2400000000000], [5175000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([750000000000], [1650000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1800000000000,
      9000000000000], [5925000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1275000000000],
      [7725000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0, 9000000000000], [7200000000000,
      -9000000000000]) (some (4, 1, 2)) (some (4, 1, 4)) (.next ([0, 0], [1800000000000,
      9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-150000000000], [6600000000000])
      (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1800000000000], [9000000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-5175000000000], [7575000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1650000000000], [2400000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-5925000000000, 0], [7725000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-7725000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7200000000000,
      9000000000000], [7200000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded55_6 : ExcludedOn (model55.B 6 ++ [step55.q]) 9000000000000 (model55.caps 6)
    (model55.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_7 : ExcludedOn (model55.B 7 ++ [step55.q]) 9000000000000 (model55.caps 7)
    (model55.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_8 : ExcludedOn (model55.B 8 ++ [step55.q]) 9000000000000 (model55.caps 8)
    (model55.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_9 : ExcludedOn (model55.B 9 ++ [step55.q]) 9000000000000 (model55.caps 9)
    (model55.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked55 : StepValid model55 9000000000000 step55 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded55_1
    · exact excluded55_2
    · exact excluded55_3
    · exact excluded55_4
    · exact excluded55_5
    · exact excluded55_6
    · exact excluded55_7
    · exact excluded55_8
    · exact excluded55_9
theorem next55 : model55.insert step55 = model56 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext200000210000
end ConwaySoifer.Simplified.Certificates

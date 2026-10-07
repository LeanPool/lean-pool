/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext150000160000
import Mathlib.Tactic.FinCases

/-!
# Sext 150000 160000 6

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
namespace Sext150000160000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner4Part0 : FanWitness := (.next ([1125000000000], [2250000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([1350000000000, 9000000000000], [5325000000000]) (some (6, 1, 2)) (some
    (6, 1, 2)) (.next ([450000000000], [2400000000000, -9000000000000]) (some (6, 1, 2)) (some (6,
    1, 2)) (.next ([525000000000], [3225000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([450000000000], [3750000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([450000000000],
    [4125000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([75000000000], [4125000000000]) (some
    (5, 1, 2)) (some (5, 1, 2)) (.next ([0], [5325000000000]) (some (5, 1, 2)) (some (5, 1, 6))
    (.next ([-375000000000], [3075000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-750000000000], [4875000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1650000000000],
    [5325000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2625000000000], [5700000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-450000000000], [900000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-4875000000000], [9075000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-1050000000000], [1875000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2775000000000, 9000000000000], [4575000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-600000000000], [975000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2250000000000],
    [3375000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-5325000000000], [6675000000000,
    9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2400000000000, 9000000000000],
    [2850000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3225000000000],
    [3750000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3750000000000], [4200000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4125000000000], [4575000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-4125000000000], [4200000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.terminal (some (0, 1, 6)) (some (0, 1, 6)) (some (0, 1, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan49Owner4Part0 : FanWitness := (.next ([1800000000000, 9000000000000], [2775000000000,
    -9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([375000000000], [600000000000]) (some
    (6, 1, 2)) (some (6, 1, 2)) (.next ([675000000000], [2400000000000, -9000000000000]) (some (6,
    1, 2)) (some (6, 1, 2)) (.next ([1350000000000, 9000000000000], [5325000000000]) (some (5, 1,
    2)) (some (5, 1, 2)) (.next ([750000000000], [3000000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([675000000000], [3750000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([450000000000], [4125000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([300000000000],
    [3900000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([0], [5325000000000]) (some (5, 1,
    2)) (some (5, 1, 6)) (.next ([-375000000000], [3075000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-750000000000], [4875000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1650000000000], [5325000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2625000000000],
    [5700000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-450000000000], [900000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4650000000000], [9075000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-1050000000000], [1875000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-2775000000000, 9000000000000], [4575000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-600000000000], [975000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2400000000000, 9000000000000], [3075000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1,
    6)) (.next ([-5325000000000], [6675000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-3000000000000], [3750000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-3750000000000], [4425000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4125000000000],
    [4575000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3900000000000], [4200000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.terminal (some (0, 1, 6)) (some (0, 1, 6)) (some (0, 1,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan51Owner3Part0 : FanWitness := (.next ([150000000000], [4875000000000]) (some (6, 2, 7)) (some
    (6, 2, 7)) (.next ([0], [1350000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([-75000000000], [4125000000000]) (some (0, 2, 7)) (some (0, 3, 7)) (.next ([-375000000000],
    [4950000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-450000000000], [5250000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-375000000000], [4350000000000]) (some (0, 3, 7))
    (some (0, 3, 7)) (.next ([-375000000000], [4125000000000]) (some (0, 3, 7)) (some (0, 3, 7))
    (.next ([-375000000000], [3600000000000, -9000000000000]) (some (0, 3, 7)) (some (0, 4, 7))
    (.next ([-450000000000], [3900000000000, -9000000000000]) (some (0, 4, 7)) (some (1, 4, 7))
    (.next ([-675000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-675000000000], [3900000000000, -9000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-900000000000, -9000000000000], [4425000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-1350000000000, -9000000000000], [5925000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-75000000000], [300000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-1350000000000, -9000000000000], [2700000000000, 18000000000000]) (some (1, 4, 7)) (some (2,
    4, 7)) (.next ([-4950000000000], [9150000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next
    ([-5250000000000], [9375000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-5250000000000],
    [9150000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-3075000000000, 9000000000000],
    [4875000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-4950000000000, 0], [5925000000000,
    9000000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-5250000000000, 0], [6150000000000,
    9000000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-5250000000000, 0], [5925000000000,
    9000000000000]) (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-4425000000000], [4875000000000])
    (some (2, 4, 7)) (some (2, 4, 7)) (.next ([-4875000000000], [5025000000000]) (some (2, 4, 7))
    (some (2, 4, 7)) (.terminal (some (2, 4, 7)) (some (2, 7, 5)) (some (2, 7,
    7)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner0Part0 : FanWitness := (.next ([0], [900000000000]) (some (7, 4, 5)) (some (7, 4, 5))
    (.next ([-555000000000], [7575000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-1005000000000], [7200000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-675000000000],
    [3825000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-1650000000000], [7350000000000])
    (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-1650000000000], [6450000000000]) (some (7, 4, 5))
    (some (7, 4, 5)) (.next ([-750000000000], [2625000000000]) (some (7, 4, 5)) (some (7, 4, 5))
    (.next ([-1125000000000], [3450000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next
    ([-3180000000000], [9450000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-375000000000],
    [825000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([-1530000000000], [3000000000000])
    (some (7, 4, 5)) (some (7, 4, 6)) (.next ([-3300000000000], [5475000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4200000000000], [6375000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-4125000000000], [5925000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-1530000000000], [2100000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5025000000000],
    [6825000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-4575000000000], [5550000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-5475000000000], [6450000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.next ([-4200000000000], [4725000000000]) (some (7, 4, 6)) (some (7, 4, 6))
    (.next ([-5100000000000], [5625000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next
    ([-6300000000000], [6945000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-1200000000000],
    [1275000000000]) (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-7125000000000], [7395000000000])
    (some (7, 4, 6)) (some (7, 4, 6)) (.next ([-2175000000000], [2250000000000]) (some (7, 4, 6))
    (some (7, 4, 6)) (.terminal (some (7, 4, 6)) (some (7, 4, 6)) (some (7, 4,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner3Part0 : FanWitness := (.next ([-75000000000], [4125000000000]) (some (0, 7, 5)) (some
    (0, 7, 5)) (.next ([-375000000000], [4950000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-450000000000], [5250000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-375000000000],
    [4350000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-375000000000], [4125000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-375000000000], [3600000000000, -9000000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-450000000000], [3900000000000, -9000000000000])
    (some (0, 7, 5)) (some (1, 7, 5)) (.next ([-675000000000], [5250000000000]) (some (1, 7, 5))
    (some (1, 7, 5)) (.next ([-675000000000], [3900000000000, -9000000000000]) (some (1, 7, 5))
    (some (1, 7, 5)) (.next ([-900000000000, -9000000000000], [4425000000000]) (some (1, 7, 5))
    (some (1, 7, 5)) (.next ([-75000000000], [300000000000]) (some (1, 7, 5)) (some (1, 7, 5))
    (.next ([-1575000000000], [5925000000000]) (some (1, 7, 5)) (some (2, 7, 5)) (.next
    ([-1575000000000], [5625000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-1800000000000],
    [5850000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-1875000000000], [4425000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-1350000000000, -9000000000000], [2700000000000,
    18000000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-4950000000000, 9000000000000],
    [9300000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-3075000000000, 9000000000000],
    [4875000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-6300000000000], [9300000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-6300000000000], [7950000000000, -9000000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-4950000000000, 0], [5925000000000, 9000000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-5250000000000, 0], [6150000000000, 9000000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-5250000000000, 0], [5925000000000, 9000000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-4425000000000], [4875000000000]) (some (2, 7, 5))
    (some (2, 7, 5)) (.terminal (some (2, 7, 5)) (some (2, 7, 5)) (some (2, 7,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan52Owner3Part1 : FanWitness := (.next ([4575000000000], [375000000000]) (some (6, 2, 7)) (some
    (6, 2, 7)) (.next ([4800000000000], [450000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([3975000000000], [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3750000000000],
    [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3225000000000, -9000000000000],
    [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3450000000000, -9000000000000],
    [450000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4575000000000], [675000000000]) (some
    (6, 2, 7)) (some (6, 2, 7)) (.next ([3225000000000, -9000000000000], [675000000000]) (some (6,
    2, 7)) (some (6, 2, 7)) (.next ([3525000000000, -9000000000000], [900000000000, 9000000000000])
    (some (6, 2, 7)) (some (6, 2, 7)) (.next ([225000000000], [75000000000]) (some (6, 2, 7)) (some
    (6, 2, 7)) (.next ([4350000000000], [1575000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([4050000000000], [1575000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4050000000000],
    [1800000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2550000000000], [1875000000000])
    (some (6, 2, 7)) (some (6, 7, 7)) (.next ([1350000000000, 9000000000000], [1350000000000,
    9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4350000000000, 9000000000000],
    [4950000000000, -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([1800000000000,
    9000000000000], [3075000000000, -9000000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
    ([3000000000000], [6300000000000]) (some (6, 7, 4)) (some (6, 7, 5)) (.next ([1650000000000,
    -9000000000000], [6300000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([975000000000,
    9000000000000], [4950000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([900000000000,
    9000000000000], [5250000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([675000000000,
    9000000000000], [5250000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([450000000000],
    [4425000000000]) (some (6, 7, 5)) (some (6, 7, 5)) (.next ([0], [1350000000000, 9000000000000])
    (some (6, 7, 5)) (some (6, 7, 5)) fan52Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan53Owner3Part0 : FanWitness := (.next ([-75000000000], [4125000000000]) (some (0, 2, 7)) (some
    (0, 3, 7)) (.next ([-375000000000], [4950000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
    ([-450000000000], [5250000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-375000000000],
    [4350000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-375000000000], [4125000000000])
    (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-375000000000], [3600000000000, -9000000000000])
    (some (0, 3, 7)) (some (0, 4, 7)) (.next ([-450000000000], [3900000000000, -9000000000000])
    (some (0, 4, 7)) (some (1, 4, 7)) (.next ([-675000000000], [5250000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-1575000000000], [9525000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-675000000000], [3900000000000, -9000000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-1875000000000], [9750000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-1875000000000], [9525000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-900000000000,
    -9000000000000], [4425000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-75000000000],
    [300000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-1500000000000], [5400000000000])
    (some (1, 4, 7)) (some (2, 4, 7)) (.next ([-1350000000000, -9000000000000], [2700000000000,
    18000000000000]) (some (2, 4, 7)) (some (2, 7, 7)) (.next ([-3600000000000, 9000000000000],
    [6975000000000, -9000000000000]) (some (2, 7, 7)) (some (2, 7, 7)) (.next ([-4950000000000],
    [8325000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-3075000000000, 9000000000000],
    [4875000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-6300000000000, -9000000000000],
    [8325000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-4950000000000, 0], [5925000000000,
    9000000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-5250000000000, 0], [6150000000000,
    9000000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-5250000000000, 0], [5925000000000,
    9000000000000]) (some (2, 7, 5)) (some (2, 7, 5)) (.next ([-4425000000000], [4875000000000])
    (some (2, 7, 5)) (some (2, 7, 5)) (.terminal (some (2, 7, 5)) (some (2, 7, 5)) (some (2, 7,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan53Owner3Part1 : FanWitness := (.next ([4575000000000], [375000000000]) (some (6, 2, 7)) (some
    (6, 2, 7)) (.next ([4800000000000], [450000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([3975000000000], [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3750000000000],
    [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3225000000000, -9000000000000],
    [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3450000000000, -9000000000000],
    [450000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4575000000000], [675000000000]) (some
    (6, 2, 7)) (some (6, 2, 7)) (.next ([7950000000000], [1575000000000]) (some (6, 2, 7)) (some (6,
    2, 7)) (.next ([3225000000000, -9000000000000], [675000000000]) (some (6, 2, 7)) (some (6, 2,
    7)) (.next ([7875000000000], [1875000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([7650000000000], [1875000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3525000000000,
    -9000000000000], [900000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([225000000000], [75000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3900000000000],
    [1500000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1350000000000, 9000000000000],
    [1350000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3375000000000, 0],
    [3600000000000, -9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3375000000000],
    [4950000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1800000000000, 9000000000000],
    [3075000000000, -9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([2025000000000,
    -9000000000000], [6300000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([975000000000, 9000000000000], [4950000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([900000000000, 9000000000000], [5250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([675000000000, 9000000000000], [5250000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
    ([450000000000], [4425000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([0], [1350000000000,
    9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) fan53Owner3Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan55Owner0Part0 : FanWitness := (.next ([0], [900000000000]) (some (0, 4, 7)) (some (0, 4, 7))
    (.next ([-555000000000], [7575000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
    ([-1005000000000], [7200000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-975000000000],
    [4725000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-2550000000000], [7050000000000])
    (some (0, 4, 7)) (some (0, 4, 7)) (.next ([-2925000000000], [7875000000000]) (some (0, 4, 5))
    (some (0, 4, 5)) (.next ([-1875000000000], [4725000000000]) (some (0, 4, 5)) (some (0, 4, 5))
    (.next ([-3750000000000], [8325000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next
    ([-375000000000], [825000000000]) (some (0, 4, 5)) (some (0, 4, 5)) (.next ([-1530000000000],
    [3000000000000]) (some (0, 4, 5)) (some (1, 4, 6)) (.next ([-4200000000000], [7950000000000])
    (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-3300000000000], [5475000000000]) (some (1, 4, 6))
    (some (1, 4, 6)) (.next ([-4200000000000], [6375000000000]) (some (1, 4, 6)) (some (1, 4, 6))
    (.next ([-4125000000000], [5925000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-1530000000000], [2100000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-5025000000000],
    [6825000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-2445000000000], [3195000000000])
    (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-4575000000000], [5550000000000]) (some (1, 4, 6))
    (some (1, 7, 6)) (.next ([-5475000000000], [6450000000000]) (some (1, 7, 6)) (some (1, 7, 6))
    (.next ([-4200000000000], [4725000000000]) (some (1, 7, 6)) (some (1, 7, 6)) (.next
    ([-5100000000000], [5625000000000]) (some (1, 7, 6)) (some (2, 7, 6)) (.next ([-6300000000000],
    [6945000000000]) (some (2, 7, 6)) (some (2, 7, 6)) (.next ([-1200000000000], [1275000000000])
    (some (2, 7, 6)) (some (2, 7, 6)) (.next ([-7125000000000], [7395000000000]) (some (2, 7, 6))
    (some (2, 7, 6)) (.terminal (some (2, 7, 6)) (some (2, 7, 6)) (some (2, 7,
    6)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2700000000000], [375000000000]) (some (6, 0, 1))
      (some (6, 1, 1)) (.next ([4125000000000], [750000000000]) (some (6, 1, 1)) (some (6, 1, 1))
      (.next ([3675000000000], [1650000000000]) (some (6, 1, 1)) (some (6, 1, 2)) (.next
      ([3075000000000], [2625000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([450000000000],
      [450000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([4200000000000], [4875000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([825000000000], [1050000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([1800000000000, 9000000000000], [2775000000000, -9000000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([375000000000], [600000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) fan48Owner4Part0)))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel)
      0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [75000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([5250000000000], [600000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([3600000000000], [1725000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([5250000000000], [4200000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5325000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-75000000000], [4200000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-600000000000], [5850000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-1725000000000], [5325000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4200000000000], [9450000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2700000000000], [375000000000]) (some (6, 0, 1))
      (some (6, 1, 1)) (.next ([4125000000000], [750000000000]) (some (6, 1, 1)) (some (6, 1, 1))
      (.next ([3675000000000], [1650000000000]) (some (6, 1, 1)) (some (6, 1, 2)) (.next
      ([3075000000000], [2625000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([450000000000],
      [450000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([4425000000000], [4650000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([825000000000], [1050000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) fan49Owner4Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4350000000000], [75000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([5250000000000], [825000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([3600000000000], [1725000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([5250000000000], [4425000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [5325000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-75000000000], [4425000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-825000000000], [6075000000000]) (some (0, 1, 3))
      (some (0, 3, 3)) (.next ([-1725000000000], [5325000000000]) (some (0, 3, 2)) (some (0, 3, 2))
      (.next ([-4425000000000], [9675000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded49_4
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
  apply ExclusionHint.sound (.pair 3 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3900000000000], [1800000000000]) (some (0, 4,
      2)) (some (0, 4, 2)) (.next ([5925000000000, 9000000000000], [3525000000000, -9000000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2025000000000, 9000000000000], [1725000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([4575000000000], [4875000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1350000000000, 9000000000000], [3555000000000, 0])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([675000000000], [3075000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([1020000000000], [4875000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([195000000000], [2880000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next ([0],
      [3555000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1800000000000], [5700000000000])
      (some (4, 4, 2)) (some (4, 4, 3)) (.next ([-3525000000000, 9000000000000], [9450000000000, 0])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-1725000000000, 9000000000000], [3750000000000, 0])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4875000000000], [9450000000000]) (some (4, 1, 3))
      (some (4, 2, 3)) (.next ([-3555000000000, 0], [4905000000000, 9000000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-3075000000000], [3750000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.next ([-4875000000000], [5895000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-2880000000000], [3075000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (4, 2, 0)) (some (4, 2, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_3 : ExcludedOn (model51.B 3 ++ [step51.q]) 9000000000000 (model51.caps 3)
    (model51.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [75000000000]) (some (5, 2, 7))
      (some (6, 2, 7)) (.next ([4575000000000], [375000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      (.next ([4800000000000], [450000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([3975000000000], [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3750000000000],
      [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3225000000000, -9000000000000],
      [375000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3450000000000, -9000000000000],
      [450000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4575000000000], [675000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3225000000000, -9000000000000], [675000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([3525000000000, -9000000000000], [900000000000,
      9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4575000000000], [1350000000000,
      9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([225000000000], [75000000000]) (some
      (6, 2, 7)) (some (6, 2, 7)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4200000000000], [4950000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([4125000000000], [5250000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([3900000000000], [5250000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      (.next ([1800000000000, 9000000000000], [3075000000000, -9000000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([975000000000, 9000000000000], [4950000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([900000000000, 9000000000000], [5250000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([675000000000, 9000000000000], [5250000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([450000000000], [4425000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      fan51Owner3Part0)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded52_0 : ExcludedOn (model52.B 0 ++ [step52.q]) 9000000000000 (model52.caps 0)
    (model52.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000], [555000000000]) (some (6, 7, 4))
      (some (6, 7, 4)) (.next ([6195000000000], [1005000000000]) (some (6, 7, 4)) (some (6, 7, 4))
      (.next ([3150000000000], [675000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next
      ([5700000000000], [1650000000000]) (some (6, 7, 4)) (some (6, 7, 4)) (.next ([4800000000000],
      [1650000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([1875000000000], [750000000000])
      (some (6, 3, 4)) (some (6, 3, 4)) (.next ([2325000000000], [1125000000000]) (some (6, 3, 4))
      (some (6, 3, 4)) (.next ([6270000000000], [3180000000000]) (some (6, 3, 4)) (some (7, 3, 4))
      (.next ([450000000000], [375000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next
      ([1470000000000], [1530000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([2175000000000],
      [3300000000000]) (some (7, 3, 4)) (some (7, 3, 4)) (.next ([2175000000000], [4200000000000])
      (some (7, 3, 4)) (some (7, 3, 4)) (.next ([1800000000000], [4125000000000]) (some (7, 3, 4))
      (some (7, 3, 4)) (.next ([570000000000], [1530000000000]) (some (7, 3, 4)) (some (7, 3, 4))
      (.next ([1800000000000], [5025000000000]) (some (7, 3, 4)) (some (7, 4, 4)) (.next
      ([975000000000], [4575000000000]) (some (7, 4, 4)) (some (7, 4, 4)) (.next ([975000000000],
      [5475000000000]) (some (7, 4, 4)) (some (7, 4, 4)) (.next ([525000000000], [4200000000000])
      (some (7, 4, 4)) (some (7, 4, 4)) (.next ([525000000000], [5100000000000]) (some (7, 4, 4))
      (some (7, 4, 4)) (.next ([645000000000], [6300000000000]) (some (7, 4, 4)) (some (7, 4, 4))
      (.next ([75000000000], [1200000000000]) (some (7, 4, 4)) (some (7, 4, 5)) (.next
      ([270000000000], [7125000000000]) (some (7, 4, 5)) (some (7, 4, 5)) (.next ([75000000000],
      [2175000000000]) (some (7, 4, 5)) (some (7, 4, 5)) fan52Owner0Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_1 : ExcludedOn (model52.B 1 ++ [step52.q]) 9000000000000 (model52.caps 1)
    (model52.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_2 : ExcludedOn (model52.B 2 ++ [step52.q]) 9000000000000 (model52.caps 2)
    (model52.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [75000000000]) (some (5, 2, 7))
      (some (6, 2, 7)) fan52Owner3Part1)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded52_0
    · exact excluded52_1
    · exact excluded52_2
    · exact excluded52_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 2 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_1 : ExcludedOn (model53.B 1 ++ [step53.q]) 9000000000000 (model53.caps 1)
    (model53.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6975000000000, 9000000000000], [2700000000000,
      -9000000000000]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([5625000000000], [4050000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([4275000000000, -9000000000000], [4050000000000, 0])
      (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1350000000000, 9000000000000], [1350000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2700000000000, 9000000000000],
      [9675000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4050000000000], [9675000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-4050000000000, 0], [8325000000000,
      -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1350000000000, -9000000000000],
      [2700000000000, 18000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.terminal (some (3, 1, 3))
      (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4050000000000], [75000000000]) (some (5, 2, 7))
      (some (6, 2, 7)) fan53Owner3Part1)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded53_1
    · exact (hj rfl).elim
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

theorem excluded54_0 : ExcludedOn (model54.B 0 ++ [step54.q]) 9000000000000 (model54.caps 0)
    (model54.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_1 : ExcludedOn (model54.B 1 ++ [step54.q]) 9000000000000 (model54.caps 1)
    (model54.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_2 : ExcludedOn (model54.B 2 ++ [step54.q]) 9000000000000 (model54.caps 2)
    (model54.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_3 : ExcludedOn (model54.B 3 ++ [step54.q]) 9000000000000 (model54.caps 3)
    (model54.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_4 : ExcludedOn (model54.B 4 ++ [step54.q]) 9000000000000 (model54.caps 4)
    (model54.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_5 : ExcludedOn (model54.B 5 ++ [step54.q]) 9000000000000 (model54.caps 5)
    (model54.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_6 : ExcludedOn (model54.B 6 ++ [step54.q]) 9000000000000 (model54.caps 6)
    (model54.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded54_8 : ExcludedOn (model54.B 8 ++ [step54.q]) 9000000000000 (model54.caps 8)
    (model54.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded54_0
    · exact excluded54_1
    · exact excluded54_2
    · exact excluded54_3
    · exact excluded54_4
    · exact excluded54_5
    · exact excluded54_6
    · exact (hj rfl).elim
    · exact excluded54_8
    · exact excluded54_9
theorem next54 : model54.insert step54 = model55 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded55_0 : ExcludedOn (model55.B 0 ++ [step55.q]) 9000000000000 (model55.caps 0)
    (model55.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000], [555000000000]) (some (6, 2, 7))
      (some (6, 3, 7)) (.next ([6195000000000], [1005000000000]) (some (6, 3, 7)) (some (6, 3, 7))
      (.next ([3750000000000], [975000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next
      ([4500000000000], [2550000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([4950000000000],
      [2925000000000]) (some (6, 3, 7)) (some (6, 3, 7)) (.next ([2850000000000], [1875000000000])
      (some (6, 3, 7)) (some (6, 3, 7)) (.next ([4575000000000], [3750000000000]) (some (6, 3, 7))
      (some (6, 3, 7)) (.next ([450000000000], [375000000000]) (some (6, 3, 7)) (some (6, 3, 7))
      (.next ([1470000000000], [1530000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next
      ([3750000000000], [4200000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([2175000000000],
      [3300000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([2175000000000], [4200000000000])
      (some (0, 3, 7)) (some (0, 3, 7)) (.next ([1800000000000], [4125000000000]) (some (0, 3, 7))
      (some (0, 3, 7)) (.next ([570000000000], [1530000000000]) (some (0, 3, 7)) (some (0, 3, 7))
      (.next ([1800000000000], [5025000000000]) (some (0, 3, 7)) (some (0, 4, 7)) (.next
      ([750000000000], [2445000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([975000000000],
      [4575000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([975000000000], [5475000000000])
      (some (0, 4, 7)) (some (0, 4, 7)) (.next ([525000000000], [4200000000000]) (some (0, 4, 7))
      (some (0, 4, 7)) (.next ([525000000000], [5100000000000]) (some (0, 4, 7)) (some (0, 4, 7))
      (.next ([645000000000], [6300000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next
      ([75000000000], [1200000000000]) (some (0, 4, 7)) (some (0, 4, 7)) (.next ([270000000000],
      [7125000000000]) (some (0, 4, 7)) (some (0, 4, 7)) fan55Owner0Part0))))))))))))))))))))))))
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded55_2 : ExcludedOn (model55.B 2 ++ [step55.q]) 9000000000000 (model55.caps 2)
    (model55.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_3 : ExcludedOn (model55.B 3 ++ [step55.q]) 9000000000000 (model55.caps 3)
    (model55.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_4 : ExcludedOn (model55.B 4 ++ [step55.q]) 9000000000000 (model55.caps 4)
    (model55.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_5 : ExcludedOn (model55.B 5 ++ [step55.q]) 9000000000000 (model55.caps 5)
    (model55.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_6 : ExcludedOn (model55.B 6 ++ [step55.q]) 9000000000000 (model55.caps 6)
    (model55.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4725000000000, 9000000000000], [150000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3375000000000], [1500000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1500000000000], [2775000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1350000000000, 9000000000000], [7650000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1350000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-150000000000, 9000000000000],
      [4875000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1500000000000], [4875000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2775000000000, 9000000000000], [4275000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7650000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_7 : ExcludedOn (model55.B 7 ++ [step55.q]) 9000000000000 (model55.caps 7)
    (model55.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded55_8 : ExcludedOn (model55.B 8 ++ [step55.q]) 9000000000000 (model55.caps 8)
    (model55.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded55_0
    · exact (hj rfl).elim
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

end Sext150000160000
end ConwaySoifer.Simplified.Certificates

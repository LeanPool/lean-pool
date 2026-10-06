/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext260000270000
import Mathlib.Tactic.FinCases

/-!
# Sext 260000 270000 4

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
namespace Sext260000270000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part0 : FanWitness := (.next ([-2250000000000], [6930000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-135000000000], [360000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3000000000000], [7305000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1170000000000], [2535000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3420000000000],
    [7305000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-795000000000], [1590000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3795000000000], [7260000000000]) (some (0, 2, 5))
    (some (0, 2, 6)) (.next ([-1170000000000], [2115000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-225000000000], [405000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1215000000000], [1965000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-1125000000000],
    [1695000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-795000000000], [1170000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-4365000000000], [6135000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-1215000000000], [1545000000000]) (some (0, 3, 6)) (some (9, 3, 6))
    (.next ([-4695000000000], [5625000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([-5115000000000], [6045000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-5055000000000],
    [5850000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-5475000000000], [6270000000000])
    (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-5865000000000], [6420000000000]) (some (9, 3, 6))
    (some (9, 3, 6)) (.next ([-5235000000000], [5625000000000]) (some (9, 3, 6)) (some (9, 3, 6))
    (.next ([-5655000000000], [6045000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next
    ([-6225000000000], [6645000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-6285000000000],
    [6420000000000]) (some (9, 3, 6)) (some (9, 3, 6)) (.next ([-6405000000000], [6420000000000])
    (some (9, 3, 6)) (some (9, 3, 6)) (.terminal (some (9, 3, 6)) (some (9, 3, 6)) (some (9, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part1 : FanWitness := (.next ([795000000000], [5475000000000]) (some (0, 9, 3)) (some
    (0, 9, 3)) (.next ([555000000000], [5865000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next
    ([390000000000], [5235000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next ([390000000000],
    [5655000000000]) (some (0, 9, 3)) (some (0, 9, 4)) (.next ([420000000000], [6225000000000])
    (some (0, 9, 4)) (some (0, 9, 4)) (.next ([135000000000], [6285000000000]) (some (0, 9, 4))
    (some (0, 9, 4)) (.next ([15000000000], [6405000000000]) (some (0, 9, 4)) (some (0, 9, 4))
    (.next ([0], [540000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([-285000000000],
    [6660000000000]) (some (0, 9, 4)) (some (0, 9, 5)) (.next ([-45000000000], [840000000000]) (some
    (0, 9, 5)) (some (0, 9, 5)) (.next ([-405000000000], [6825000000000]) (some (0, 9, 5)) (some (0,
    9, 5)) (.next ([-420000000000], [7020000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
    ([-45000000000], [420000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-825000000000],
    [7200000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-375000000000], [2910000000000])
    (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-660000000000], [3885000000000]) (some (0, 9, 5))
    (some (0, 9, 5)) (.next ([-885000000000], [4290000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-885000000000], [3750000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-795000000000], [2910000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1980000000000],
    [7230000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2115000000000], [7590000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1830000000000], [6510000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-375000000000], [1170000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-2520000000000], [7770000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    fan32Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan32Owner0Part2 : FanWitness := (.next ([2865000000000], [885000000000]) (some (8, 9, 3)) (some
    (8, 9, 3)) (.next ([2115000000000], [795000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next
    ([5250000000000], [1980000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([5475000000000],
    [2115000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([4680000000000], [1830000000000])
    (some (8, 9, 3)) (some (8, 9, 3)) (.next ([795000000000], [375000000000]) (some (8, 9, 3)) (some
    (8, 9, 3)) (.next ([5250000000000], [2520000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next
    ([4680000000000], [2250000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([225000000000],
    [135000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([4305000000000], [3000000000000])
    (some (8, 9, 3)) (some (8, 9, 3)) (.next ([1365000000000], [1170000000000]) (some (8, 9, 3))
    (some (8, 9, 3)) (.next ([3885000000000], [3420000000000]) (some (8, 9, 3)) (some (8, 9, 3))
    (.next ([795000000000], [795000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next
    ([3465000000000], [3795000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([945000000000],
    [1170000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([180000000000], [225000000000]) (some
    (8, 9, 3)) (some (8, 9, 3)) (.next ([750000000000], [1215000000000]) (some (8, 9, 3)) (some (8,
    9, 3)) (.next ([570000000000], [1125000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next
    ([375000000000], [795000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next ([1770000000000],
    [4365000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next ([330000000000], [1215000000000])
    (some (0, 9, 3)) (some (0, 9, 3)) (.next ([930000000000], [4695000000000]) (some (0, 9, 3))
    (some (0, 9, 3)) (.next ([930000000000], [5115000000000]) (some (0, 9, 3)) (some (0, 9, 3))
    (.next ([795000000000], [5055000000000]) (some (0, 9, 3)) (some (0, 9, 3))
    fan32Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part0 : FanWitness := (.next ([-795000000000], [1590000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-1125000000000], [2220000000000]) (some (0, 2, 5)) (some (0, 2, 6))
    (.next ([-3600000000000], [6750000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1170000000000], [2115000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-225000000000],
    [405000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4020000000000], [7170000000000])
    (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-1215000000000], [1965000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-4770000000000], [7545000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-1125000000000], [1695000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-795000000000], [1170000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5190000000000],
    [7545000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5565000000000], [7500000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-1215000000000], [1545000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-4695000000000], [5625000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-5115000000000], [6045000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-5055000000000], [5850000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5475000000000],
    [6270000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5865000000000], [6420000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5235000000000], [5625000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-5655000000000], [6045000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-6225000000000], [6645000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-6135000000000], [6375000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-6285000000000],
    [6420000000000]) (some (0, 3, 6)) (some (9, 3, 6)) (.next ([-6405000000000], [6420000000000])
    (some (9, 3, 6)) (some (9, 3, 6)) (.terminal (some (9, 3, 6)) (some (9, 3, 6)) (some (9, 3,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part1 : FanWitness := (.next ([555000000000], [5865000000000]) (some (0, 9, 3)) (some
    (0, 9, 3)) (.next ([390000000000], [5235000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next
    ([390000000000], [5655000000000]) (some (0, 9, 3)) (some (0, 9, 4)) (.next ([420000000000],
    [6225000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([240000000000], [6135000000000])
    (some (0, 9, 4)) (some (0, 9, 4)) (.next ([135000000000], [6285000000000]) (some (0, 9, 4))
    (some (0, 9, 4)) (.next ([15000000000], [6405000000000]) (some (0, 9, 4)) (some (0, 9, 4))
    (.next ([0], [540000000000]) (some (0, 9, 4)) (some (0, 9, 4)) (.next ([-285000000000],
    [6660000000000]) (some (0, 9, 4)) (some (0, 9, 5)) (.next ([-45000000000], [840000000000]) (some
    (0, 9, 5)) (some (0, 9, 5)) (.next ([-405000000000], [6825000000000]) (some (0, 9, 5)) (some (0,
    9, 5)) (.next ([-420000000000], [7020000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
    ([-45000000000], [420000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-825000000000],
    [7200000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-375000000000], [2910000000000])
    (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-795000000000], [2910000000000]) (some (0, 9, 5))
    (some (0, 9, 5)) (.next ([-1980000000000], [7230000000000]) (some (0, 9, 5)) (some (0, 9, 5))
    (.next ([-2115000000000], [7590000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next
    ([-375000000000], [1170000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-2520000000000],
    [7770000000000]) (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-135000000000], [360000000000])
    (some (0, 9, 5)) (some (0, 9, 5)) (.next ([-900000000000], [2355000000000]) (some (0, 9, 5))
    (some (0, 9, 5)) (.next ([-1125000000000], [2760000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1170000000000], [2535000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    fan33Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner0Part2 : FanWitness := (.next ([5475000000000], [2115000000000]) (some (8, 9, 3))
    (some (8, 9, 3)) (.next ([795000000000], [375000000000]) (some (8, 9, 3)) (some (8, 9, 3))
    (.next ([5250000000000], [2520000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next
    ([225000000000], [135000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([1455000000000],
    [900000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([1635000000000], [1125000000000])
    (some (8, 9, 3)) (some (8, 9, 3)) (.next ([1365000000000], [1170000000000]) (some (8, 9, 3))
    (some (8, 9, 3)) (.next ([795000000000], [795000000000]) (some (8, 9, 3)) (some (8, 9, 3))
    (.next ([1095000000000], [1125000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next
    ([3150000000000], [3600000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([945000000000],
    [1170000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([180000000000], [225000000000]) (some
    (8, 9, 3)) (some (8, 9, 3)) (.next ([3150000000000], [4020000000000]) (some (8, 9, 3)) (some (8,
    9, 3)) (.next ([750000000000], [1215000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next
    ([2775000000000], [4770000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([570000000000],
    [1125000000000]) (some (8, 9, 3)) (some (8, 9, 3)) (.next ([375000000000], [795000000000]) (some
    (0, 9, 3)) (some (0, 9, 3)) (.next ([2355000000000], [5190000000000]) (some (0, 9, 3)) (some (0,
    9, 3)) (.next ([1935000000000], [5565000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next
    ([330000000000], [1215000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next ([930000000000],
    [4695000000000]) (some (0, 9, 3)) (some (0, 9, 3)) (.next ([930000000000], [5115000000000])
    (some (0, 9, 3)) (some (0, 9, 3)) (.next ([795000000000], [5055000000000]) (some (0, 9, 3))
    (some (0, 9, 3)) (.next ([795000000000], [5475000000000]) (some (0, 9, 3)) (some (0, 9, 3))
    fan33Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part0 : FanWitness := (.next ([-795000000000], [1590000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-3660000000000], [7170000000000]) (some (0, 2, 5)) (some (0, 2, 6))
    (.next ([-2865000000000], [5580000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-4080000000000], [7545000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1170000000000],
    [2115000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-225000000000], [405000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1215000000000], [1965000000000]) (some (0, 2, 6))
    (some (0, 3, 6)) (.next ([-1125000000000], [1695000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-795000000000], [1170000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-5775000000000], [8115000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2910000000000],
    [3795000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-1215000000000], [1545000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-4695000000000], [5625000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-5115000000000], [6045000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-3135000000000], [3660000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-5055000000000], [5850000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5475000000000],
    [6270000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-2910000000000], [3255000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-5865000000000], [6420000000000]) (some (0, 3, 6))
    (some (0, 9, 6)) (.next ([-5235000000000], [5625000000000]) (some (0, 9, 6)) (some (0, 9, 6))
    (.next ([-5655000000000], [6045000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next
    ([-6225000000000], [6645000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-6285000000000],
    [6420000000000]) (some (0, 9, 6)) (some (0, 9, 6)) (.next ([-6405000000000], [6420000000000])
    (some (0, 9, 6)) (some (0, 9, 6)) (.terminal (some (0, 9, 6)) (some (0, 9, 6)) (some (0, 9,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part1 : FanWitness := (.next ([345000000000], [2910000000000]) (some (0, 2, 9)) (some
    (0, 2, 9)) (.next ([555000000000], [5865000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next
    ([390000000000], [5235000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([390000000000],
    [5655000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([420000000000], [6225000000000])
    (some (0, 2, 9)) (some (0, 2, 9)) (.next ([135000000000], [6285000000000]) (some (0, 2, 9))
    (some (0, 2, 9)) (.next ([15000000000], [6405000000000]) (some (0, 2, 9)) (some (0, 2, 9))
    (.next ([0], [540000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-285000000000],
    [6660000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-45000000000], [840000000000]) (some
    (0, 2, 9)) (some (0, 2, 9)) (.next ([-405000000000], [6825000000000]) (some (0, 2, 9)) (some (0,
    2, 9)) (.next ([-420000000000], [7020000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next
    ([-45000000000], [420000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-825000000000],
    [7200000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-375000000000], [2910000000000])
    (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-795000000000], [2910000000000]) (some (0, 2, 9))
    (some (0, 2, 9)) (.next ([-1980000000000], [7230000000000]) (some (0, 2, 9)) (some (0, 2, 9))
    (.next ([-2115000000000], [7590000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next
    ([-375000000000], [1170000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-2520000000000],
    [7770000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-135000000000], [360000000000])
    (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-1170000000000], [2535000000000]) (some (0, 2, 9))
    (some (0, 2, 9)) (.next ([-2865000000000], [6000000000000]) (some (0, 2, 9)) (some (0, 2, 9))
    (.next ([-3240000000000], [6750000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    fan34Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner0Part2 : FanWitness := (.next ([5475000000000], [2115000000000]) (some (8, 0, 9))
    (some (8, 1, 9)) (.next ([795000000000], [375000000000]) (some (8, 1, 9)) (some (8, 1, 9))
    (.next ([5250000000000], [2520000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
    ([225000000000], [135000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([1365000000000],
    [1170000000000]) (some (8, 1, 9)) (some (8, 2, 9)) (.next ([3135000000000], [2865000000000])
    (some (8, 2, 9)) (some (8, 2, 9)) (.next ([3510000000000], [3240000000000]) (some (8, 2, 9))
    (some (8, 2, 9)) (.next ([795000000000], [795000000000]) (some (8, 2, 9)) (some (8, 2, 9))
    (.next ([3510000000000], [3660000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
    ([2715000000000], [2865000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([3465000000000],
    [4080000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([945000000000], [1170000000000])
    (some (8, 2, 9)) (some (8, 2, 9)) (.next ([180000000000], [225000000000]) (some (8, 2, 9)) (some
    (8, 2, 9)) (.next ([750000000000], [1215000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next
    ([570000000000], [1125000000000]) (some (8, 2, 9)) (some (8, 2, 9)) (.next ([375000000000],
    [795000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([2340000000000], [5775000000000])
    (some (0, 2, 9)) (some (0, 2, 9)) (.next ([885000000000], [2910000000000]) (some (0, 2, 9))
    (some (0, 2, 9)) (.next ([330000000000], [1215000000000]) (some (0, 2, 9)) (some (0, 2, 9))
    (.next ([930000000000], [4695000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next
    ([930000000000], [5115000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([525000000000],
    [3135000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([795000000000], [5055000000000])
    (some (0, 2, 9)) (some (0, 2, 9)) (.next ([795000000000], [5475000000000]) (some (0, 2, 9))
    (some (0, 2, 9)) fan34Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner4Part0 : FanWitness := (.next ([2628000000000], [1872000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([270000000000], [195000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([2340000000000, 9000000000000], [5055000000000]) (some (5, 1, 3)) (some (5, 1, 4))
    (.next ([465000000000, 9000000000000], [3855000000000, -9000000000000]) (some (5, 1, 4)) (some
    (5, 1, 4)) (.next ([555000000000, 9000000000000], [6660000000000]) (some (5, 1, 4)) (some (5, 1,
    4)) (.next ([0, 9000000000000], [4125000000000, -9000000000000]) (some (5, 1, 4)) (some (5, 1,
    4)) (.next ([0], [5055000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([-267000000000],
    [4680000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-180000000000], [1785000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-735000000000], [6930000000000]) (some (0, 1, 4))
    (some (0, 6, 4)) (.next ([-930000000000], [7395000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-468000000000], [2250000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-663000000000], [2715000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1785000000000],
    [6660000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1875000000000], [6195000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2340000000000], [6750000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-2535000000000], [7215000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2340000000000], [6465000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1872000000000], [4500000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-195000000000],
    [465000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-5055000000000], [7395000000000,
    9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3855000000000, 9000000000000],
    [4320000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6660000000000], [7215000000000,
    9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4125000000000, 9000000000000],
    [4125000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 5))
    (some (0, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner5Part0 : FanWitness := (.next ([4395000000000], [2625000000000]) (some (5, 1, 2))
    (some (5, 1, 3)) (.next ([4125000000000], [3525000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([2625000000000], [2865000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([1785000000000], [2340000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2340000000000,
    9000000000000], [5310000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1260000000000],
    [3705000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1500000000000], [5235000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([240000000000], [1530000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([180000000000], [2685000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([0, 9000000000000], [1785000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([0, 0], [2340000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-285000000000, 9000000000000], [7020000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next
    ([-525000000000, 9000000000000], [5490000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-915000000000], [2625000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2625000000000],
    [7020000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3525000000000], [7650000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2865000000000], [5490000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-2340000000000], [4125000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([-5310000000000, 0], [7650000000000, 9000000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([-3705000000000], [4965000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-5235000000000], [6735000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1530000000000],
    [1770000000000]) (some (0, 2, 3)) (some (0, 2, 5)) (.next ([-2685000000000], [2865000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1785000000000, 9000000000000], [1785000000000, 0])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner2Part0 : FanWitness := (.next ([4035000000000, 9000000000000], [2340000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2715000000000, 9000000000000],
    [1980000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2355000000000,
    -9000000000000], [1965000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([2340000000000, 9000000000000], [2340000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([4320000000000, -9000000000000], [4680000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([1965000000000], [2715000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([1695000000000], [4680000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([375000000000], [4320000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([285000000000],
    [4035000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 9000000000000], [6660000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0, 0], [2340000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-645000000000, -9000000000000],
    [4680000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-360000000000], [1680000000000])
    (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-2340000000000], [9000000000000]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-2340000000000, 9000000000000], [6375000000000, 0]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-1980000000000, 9000000000000], [4695000000000, 0]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-1965000000000, -9000000000000], [4320000000000]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-2340000000000, -9000000000000], [4680000000000, 18000000000000])
    (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-4680000000000, -9000000000000], [9000000000000])
    (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-2715000000000], [4680000000000]) (some (1, 5, 4))
    (some (1, 5, 4)) (.next ([-4680000000000], [6375000000000]) (some (1, 5, 4)) (some (1, 5, 4))
    (.next ([-4320000000000], [4695000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next
    ([-4035000000000], [4320000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-6660000000000,
    9000000000000], [6660000000000, 0]) (some (1, 5, 4)) (some (5, 5, 4)) (.terminal (some (5, 3,
    4)) (some (5, 3, 0)) (some (5, 3, 4)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [285000000000]) (some (6, 9, 3))
      (some (7, 9, 3)) (.next ([795000000000], [45000000000]) (some (7, 9, 3)) (some (7, 9, 3))
      (.next ([6420000000000], [405000000000]) (some (7, 9, 3)) (some (7, 9, 3)) (.next
      ([6600000000000], [420000000000]) (some (7, 9, 3)) (some (7, 9, 3)) (.next ([375000000000],
      [45000000000]) (some (7, 9, 3)) (some (7, 9, 3)) (.next ([6375000000000], [825000000000])
      (some (7, 9, 3)) (some (8, 9, 3)) (.next ([2535000000000], [375000000000]) (some (8, 9, 3))
      (some (8, 9, 3)) (.next ([3225000000000], [660000000000]) (some (8, 9, 3)) (some (8, 9, 3))
      (.next ([3405000000000], [885000000000]) (some (8, 9, 3)) (some (8, 9, 3))
      fan32Owner0Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2865000000000, 0], [1170000000000,
      -9000000000000]) (some (2, 3, 1)) (some (2, 3, 2)) (.next ([6375000000000], [3795000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2865000000000], [3510000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([2340000000000, 9000000000000], [6660000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1170000000000, 9000000000000],
      [4035000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-3795000000000,
      9000000000000], [10170000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3510000000000], [6375000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-6660000000000,
      9000000000000], [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 2)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked32 : StepValid model32 9000000000000 step32 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded32_0
    · exact excluded32_1
    · exact excluded32_2
    · exact excluded32_3
    · exact excluded32_4
    · exact (hj rfl).elim
    · exact excluded32_6
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [285000000000]) (some (6, 9, 3))
      (some (7, 9, 3)) (.next ([795000000000], [45000000000]) (some (7, 9, 3)) (some (7, 9, 3))
      (.next ([6420000000000], [405000000000]) (some (7, 9, 3)) (some (7, 9, 3)) (.next
      ([6600000000000], [420000000000]) (some (7, 9, 3)) (some (7, 9, 3)) (.next ([375000000000],
      [45000000000]) (some (7, 9, 3)) (some (7, 9, 3)) (.next ([6375000000000], [825000000000])
      (some (7, 9, 3)) (some (8, 9, 3)) (.next ([2535000000000], [375000000000]) (some (8, 9, 3))
      (some (8, 9, 3)) (.next ([2115000000000], [795000000000]) (some (8, 9, 3)) (some (8, 9, 3))
      (.next ([5250000000000], [1980000000000]) (some (8, 9, 3)) (some (8, 9, 3))
      fan33Owner0Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000], [1980000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([4605000000000], [4035000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([2340000000000, 9000000000000], [6660000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([360000000000, 9000000000000], [2265000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1980000000000], [4605000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4035000000000, 9000000000000], [8640000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-6660000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2265000000000, 9000000000000],
      [2625000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded33_0
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact (hj rfl).elim
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000], [285000000000]) (some (6, 0, 9))
      (some (7, 0, 9)) (.next ([795000000000], [45000000000]) (some (7, 0, 9)) (some (7, 0, 9))
      (.next ([6420000000000], [405000000000]) (some (7, 0, 9)) (some (7, 0, 9)) (.next
      ([6600000000000], [420000000000]) (some (7, 0, 9)) (some (7, 0, 9)) (.next ([375000000000],
      [45000000000]) (some (7, 0, 9)) (some (7, 0, 9)) (.next ([6375000000000], [825000000000])
      (some (7, 0, 9)) (some (8, 0, 9)) (.next ([2535000000000], [375000000000]) (some (8, 0, 9))
      (some (8, 0, 9)) (.next ([2115000000000], [795000000000]) (some (8, 0, 9)) (some (8, 0, 9))
      (.next ([5250000000000], [1980000000000]) (some (8, 0, 9)) (some (8, 0, 9))
      fan34Owner0Part2)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6375000000000, 9000000000000], [285000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([4035000000000], [2625000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2340000000000, 9000000000000], [6660000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [2625000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2340000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-285000000000, 9000000000000],
      [6660000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2625000000000], [6660000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6660000000000, 9000000000000], [9000000000000, 0])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2625000000000, 9000000000000], [2625000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 3)) (some (0, 1,
      3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_8 : ExcludedOn (model34.B 8 ++ [step34.q]) 9000000000000 (model34.caps 8)
    (model34.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_9 : ExcludedOn (model34.B 9 ++ [step34.q]) 9000000000000 (model34.caps 9)
    (model34.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked34 : StepValid model34 9000000000000 step34 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded34_0
    · exact (hj rfl).elim
    · exact excluded34_2
    · exact excluded34_3
    · exact excluded34_4
    · exact excluded34_5
    · exact excluded34_6
    · exact excluded34_7
    · exact excluded34_8
    · exact excluded34_9
theorem next34 : model34.insert step34 = model35 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded35_0 : ExcludedOn (model35.B 0 ++ [step35.q]) 9000000000000 (model35.caps 0)
    (model35.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6735000000000, 9000000000000], [285000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([4965000000000, 9000000000000],
      [525000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1710000000000],
      [915000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([4395000000000], [2625000000000])
      (some (5, 1, 2)) (some (5, 1, 3)) (.next ([2625000000000], [2865000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([3945000000000], [5310000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([2340000000000, 9000000000000], [5310000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([1080000000000], [5490000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([1320000000000], [7020000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([240000000000],
      [1530000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([180000000000], [2685000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [2340000000000, 9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-285000000000, 9000000000000], [7020000000000, 0]) (some (5, 1,
      3)) (some (5, 2, 3)) (.next ([-525000000000, 9000000000000], [5490000000000, 0]) (some (5, 2,
      3)) (some (5, 2, 3)) (.next ([-915000000000], [2625000000000]) (some (5, 2, 3)) (some (5, 2,
      3)) (.next ([-2625000000000], [7020000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-2865000000000], [5490000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-5310000000000], [9255000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5310000000000,
      0], [7650000000000, 9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-5490000000000], [6570000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-7020000000000], [8340000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
      ([-1530000000000], [1770000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next
      ([-2685000000000], [2865000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (5, 2,
      5)) (some (0, 2, 5)) (some (5, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_8 : ExcludedOn (model35.B 8 ++ [step35.q]) 9000000000000 (model35.caps 8)
    (model35.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_9 : ExcludedOn (model35.B 9 ++ [step35.q]) 9000000000000 (model35.caps 9)
    (model35.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked35 : StepValid model35 9000000000000 step35 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded35_0
    · exact excluded35_1
    · exact excluded35_2
    · exact excluded35_3
    · exact (hj rfl).elim
    · exact excluded35_5
    · exact excluded35_6
    · exact excluded35_7
    · exact excluded35_8
    · exact excluded35_9
theorem next35 : model35.insert step35 = model36 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4413000000000], [267000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([1605000000000], [180000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([6195000000000], [735000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([6465000000000], [930000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1782000000000],
      [468000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2052000000000], [663000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4875000000000], [1785000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([4320000000000], [1875000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4410000000000], [2340000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([4680000000000], [2535000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4125000000000],
      [2340000000000]) (some (5, 1, 3)) (some (5, 1, 3)) fan36Owner4Part0)))))))))))) (den :=
      9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6735000000000, 9000000000000], [285000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) (.next ([4965000000000, 9000000000000],
      [525000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1710000000000],
      [915000000000]) (some (5, 1, 2)) (some (5, 1, 2)) fan36Owner5Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked36 : StepValid model36 9000000000000 step36 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded36_1
    · exact excluded36_2
    · exact excluded36_3
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000, -9000000000000], [2340000000000,
      9000000000000]) (some (3, 4, 1)) none (.next ([2340000000000], [1695000000000]) none none
      (.next ([2625000000000], [2340000000000]) none none (.next ([2340000000000, 9000000000000],
      [2340000000000, 9000000000000]) none none (.next ([2340000000000, 9000000000000],
      [4320000000000, -9000000000000]) none none (.next ([285000000000, -9000000000000],
      [4680000000000, 9000000000000]) none none (.next ([0, 9000000000000], [2625000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0], [2340000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-2340000000000, -9000000000000],
      [6660000000000, 0]) (some (4, 1, 2)) (some (4, 1, 3)) (.next ([-1695000000000],
      [4035000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2340000000000], [4965000000000])
      (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2340000000000, -9000000000000], [4680000000000,
      18000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4320000000000, 9000000000000],
      [6660000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-4680000000000, -9000000000000],
      [4965000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-2625000000000, 9000000000000],
      [2625000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.terminal (some (4, 1, 3)) (some (4, 1,
      3)) (some (4, 1, 3))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4035000000000, -9000000000000], [645000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1320000000000], [360000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([6660000000000], [2340000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan37Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4680000000000, 9000000000000], [4320000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2340000000000, 9000000000000],
      [4320000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2340000000000,
      9000000000000], [6660000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([2340000000000], [6660000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [2340000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-4320000000000,
      9000000000000], [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4320000000000,
      9000000000000], [6660000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6660000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.next
      ([-6660000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1,
      3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked37 : StepValid model37 9000000000000 step37 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded37_1
    · exact excluded37_2
    · exact excluded37_3
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext260000270000
end ConwaySoifer.Simplified.Certificates

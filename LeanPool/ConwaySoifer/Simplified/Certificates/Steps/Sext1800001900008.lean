/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext180000190000
import Mathlib.Tactic.FinCases

/-!
# Sext 180000 190000 8

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
namespace Sext180000190000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan64Owner3Part0 : FanWitness := (.next ([750000000000], [2490000000000]) (some (5, 0, 3)) (some
    (5, 6, 3)) (.next ([1620000000000, 9000000000000], [6000000000000]) (some (5, 6, 3)) (some (5,
    6, 3)) (.next ([1620000000000, 9000000000000], [6270000000000, -9000000000000]) (some (5, 6, 3))
    (some (5, 6, 3)) (.next ([375000000000], [4950000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([0, 9000000000000], [3000000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3))
    (.next ([0], [6000000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([-675000000000],
    [5625000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-375000000000], [2940000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-330000000000], [2325000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1620000000000, 9000000000000], [6750000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-1620000000000], [4620000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-3000000000000], [7620000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1425000000000], [3135000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3240000000000],
    [6750000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3330000000000, 9000000000000],
    [5325000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3270000000000], [4890000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3750000000000], [5130000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-3510000000000], [4650000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-6000000000000], [7890000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2490000000000], [3240000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6000000000000,
    0], [7620000000000, 9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-6270000000000,
    9000000000000], [7890000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-4950000000000],
    [5325000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3000000000000, 9000000000000],
    [3000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.terminal (some (0, 6, 4)) (some (0, 6, 4))
    (some (0, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan64Owner4Part0 : FanWitness := (.next ([5625000000000], [1620000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1140000000000], [1110000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([495000000000], [1125000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([2715000000000], [6285000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1620000000000,
    9000000000000], [5130000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1620000000000, 9000000000000], [5175000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1575000000000], [5175000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([510000000000],
    [1755000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([510000000000, 9000000000000],
    [7380000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([450000000000],
    [6795000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [5625000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [5175000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-1110000000000], [9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([-1620000000000], [7245000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-1110000000000], [2250000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1125000000000],
    [1620000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-6285000000000], [9000000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5130000000000, 9000000000000], [6750000000000])
    (some (0, 1, 5)) (some (0, 5, 5)) (.next ([-5175000000000], [6795000000000, 9000000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-5175000000000], [6750000000000]) (some (0, 5, 5))
    (some (0, 5, 5)) (.next ([-1755000000000], [2265000000000]) (some (0, 5, 5)) (some (0, 5, 5))
    (.next ([-7380000000000, 9000000000000], [7890000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-6795000000000], [7245000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-5625000000000, 9000000000000], [5625000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan65Owner0Part0 : FanWitness := (.next ([-360000000000], [540000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-4500000000000], [6660000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    (.next ([-2070000000000], [2985000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-2610000000000], [3720000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-1875000000000],
    [2610000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-4365000000000], [5985000000000])
    (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-540000000000], [735000000000]) (some (1, 5, 8))
    (some (1, 5, 8)) (.next ([-1290000000000], [1725000000000]) (some (1, 5, 8)) (some (1, 5, 9))
    (.next ([-1695000000000], [2235000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-5235000000000], [6855000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-3150000000000],
    [3900000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4545000000000], [5625000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5415000000000], [6495000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-1995000000000], [2355000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-1455000000000], [1665000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-2190000000000], [2445000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4065000000000],
    [4500000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-6105000000000], [6645000000000])
    (some (1, 5, 9)) (some (2, 5, 9)) (.next ([-4935000000000], [5370000000000]) (some (2, 5, 9))
    (some (2, 5, 9)) (.next ([-6195000000000], [6540000000000]) (some (2, 5, 9)) (some (2, 5, 9))
    (.next ([-6480000000000], [6840000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next
    ([-6570000000000], [6735000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next ([-6855000000000],
    [7020000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next ([-1275000000000], [1290000000000])
    (some (2, 5, 9)) (some (2, 5, 9)) (.terminal (some (2, 5, 9)) (some (2, 5, 9)) (some (2, 5,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan65Owner0Part1 : FanWitness := (.next ([-1110000000000], [7860000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-165000000000], [1080000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([-300000000000], [1485000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1560000000000], [7290000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1755000000000], [7380000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1515000000000], [5745000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-480000000000],
    [1125000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-915000000000], [2100000000000])
    (some (0, 4, 10)) (some (1, 4, 10)) (.next ([-180000000000], [375000000000]) (some (1, 4, 10))
    (some (1, 4, 10)) (.next ([-375000000000], [750000000000]) (some (1, 4, 10)) (some (1, 4, 10))
    (.next ([-195000000000], [375000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next
    ([-2880000000000], [5415000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-105000000000],
    [195000000000]) (some (1, 4, 10)) (some (1, 4, 10)) (.next ([-1110000000000], [1920000000000])
    (some (1, 4, 10)) (some (1, 5, 10)) (.next ([-3255000000000], [5610000000000]) (some (1, 5, 10))
    (some (1, 5, 10)) (.next ([-3750000000000], [6285000000000]) (some (1, 5, 10)) (some (1, 5, 10))
    (.next ([-915000000000], [1485000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-1995000000000], [3225000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-3630000000000], [5790000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-3870000000000], [6105000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-4125000000000], [6480000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-3960000000000], [6000000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next
    ([-2190000000000], [3315000000000]) (some (1, 5, 10)) (some (1, 5, 10)) (.next ([-735000000000],
    [1110000000000]) (some (1, 5, 10)) (some (1, 5, 10)) fan65Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan65Owner0Part2 : FanWitness := (.next ([435000000000], [1290000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([540000000000], [1695000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([1620000000000], [5235000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([750000000000], [3150000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([1080000000000],
    [4545000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([1080000000000], [5415000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([360000000000], [1995000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([210000000000], [1455000000000]) (some (0, 3, 10)) (some (0, 4, 10))
    (.next ([255000000000], [2190000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([435000000000], [4065000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([540000000000],
    [6105000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([435000000000], [4935000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([345000000000], [6195000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([360000000000], [6480000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([165000000000], [6570000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([165000000000], [6855000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([15000000000],
    [1275000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([0], [870000000000]) (some (0, 4,
    10)) (some (0, 4, 10)) (.next ([-30000000000], [6945000000000]) (some (0, 4, 10)) (some (0, 4,
    10)) (.next ([-375000000000], [7590000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-570000000000], [7680000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-375000000000],
    [3795000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-915000000000], [7770000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-645000000000], [4875000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) fan65Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan65Owner0Part3 : FanWitness := (.next ([1185000000000], [915000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([195000000000], [180000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([375000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([180000000000],
    [195000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([2535000000000], [2880000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([90000000000], [105000000000]) (some (9, 3, 5)) (some
    (9, 3, 5)) (.next ([810000000000], [1110000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([2355000000000], [3255000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([2535000000000],
    [3750000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([570000000000], [915000000000]) (some
    (9, 3, 5)) (some (9, 3, 5)) (.next ([1230000000000], [1995000000000]) (some (9, 3, 5)) (some (9,
    3, 5)) (.next ([2160000000000], [3630000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([2235000000000], [3870000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([2355000000000],
    [4125000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([2040000000000], [3960000000000])
    (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1125000000000], [2190000000000]) (some (9, 3, 5))
    (some (9, 3, 10)) (.next ([375000000000], [735000000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([180000000000], [360000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([2160000000000], [4500000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([915000000000],
    [2070000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([1110000000000], [2610000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([735000000000], [1875000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([1620000000000], [4365000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([195000000000], [540000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    fan65Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner2Part0 : FanWitness := (.next ([4950000000000], [1245000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([4875000000000], [1305000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([750000000000], [495000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([2745000000000, 9000000000000], [3825000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([4140000000000], [6180000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([1620000000000, 9000000000000], [6570000000000, 0]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([1125000000000], [5445000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([390000000000, 0], [2130000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([390000000000], [3750000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([375000000000],
    [4950000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [5445000000000]) (some (0, 1,
    3)) (some (0, 1, 3)) (.next ([-810000000000], [4935000000000]) (some (0, 1, 3)) (some (0, 1, 4))
    (.next ([-1245000000000], [6195000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-1305000000000], [6180000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-495000000000],
    [1245000000000]) (some (0, 1, 4)) (some (0, 5, 4)) (.next ([-3825000000000, 9000000000000],
    [6570000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6180000000000],
    [10320000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3330000000000, 9000000000000],
    [5325000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6570000000000, 0],
    [8190000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-5445000000000],
    [6570000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2130000000000, 9000000000000],
    [2520000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3750000000000],
    [4140000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4950000000000], [5325000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 0)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan67Owner0Part0 : FanWitness := (.next ([-3630000000000], [5790000000000]) (some (1, 5, 8))
    (some (1, 5, 8)) (.next ([-4125000000000], [6480000000000]) (some (1, 5, 8)) (some (1, 5, 8))
    (.next ([-2190000000000], [3315000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next
    ([-735000000000], [1110000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-360000000000],
    [540000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-4500000000000], [6660000000000])
    (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-4365000000000], [5985000000000]) (some (1, 5, 8))
    (some (1, 5, 8)) (.next ([-540000000000], [735000000000]) (some (1, 5, 8)) (some (1, 5, 8))
    (.next ([-3000000000000], [4050000000000]) (some (1, 5, 8)) (some (1, 5, 9)) (.next
    ([-1290000000000], [1725000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5235000000000],
    [6855000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4545000000000], [5625000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5415000000000], [6495000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-1995000000000], [2355000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-1455000000000], [1665000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-2190000000000], [2445000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4065000000000],
    [4500000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-6105000000000], [6645000000000])
    (some (1, 5, 9)) (some (2, 5, 9)) (.next ([-4935000000000], [5370000000000]) (some (2, 5, 9))
    (some (2, 5, 9)) (.next ([-6195000000000], [6540000000000]) (some (2, 5, 9)) (some (2, 5, 9))
    (.next ([-6480000000000], [6840000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next
    ([-6570000000000], [6735000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next ([-6855000000000],
    [7020000000000]) (some (2, 5, 9)) (some (2, 5, 9)) (.next ([-1275000000000], [1290000000000])
    (some (2, 5, 9)) (some (2, 5, 9)) (.terminal (some (2, 5, 9)) (some (2, 5, 9)) (some (2, 5,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan67Owner0Part1 : FanWitness := (.next ([-300000000000], [1485000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-1560000000000], [7290000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([-1755000000000], [7380000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1515000000000], [4800000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-1695000000000], [5175000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1890000000000],
    [5550000000000]) (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-2430000000000], [6285000000000])
    (some (0, 4, 6)) (some (0, 4, 6)) (.next ([-1305000000000], [3360000000000]) (some (0, 4, 6))
    (some (0, 4, 6)) (.next ([-480000000000], [1125000000000]) (some (0, 4, 6)) (some (0, 4, 6))
    (.next ([-1395000000000], [3255000000000]) (some (0, 4, 6)) (some (1, 4, 6)) (.next
    ([-915000000000], [2100000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-2970000000000],
    [6465000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-180000000000], [375000000000])
    (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-375000000000], [750000000000]) (some (1, 4, 6))
    (some (1, 4, 7)) (.next ([-195000000000], [375000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-2130000000000], [4050000000000]) (some (1, 4, 7)) (some (1, 4, 8)) (.next
    ([-2880000000000], [5415000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-105000000000],
    [195000000000]) (some (1, 4, 8)) (some (1, 4, 8)) (.next ([-1110000000000], [1920000000000])
    (some (1, 4, 8)) (some (1, 5, 8)) (.next ([-3255000000000], [5610000000000]) (some (1, 5, 8))
    (some (1, 5, 8)) (.next ([-3750000000000], [6285000000000]) (some (1, 5, 8)) (some (1, 5, 8))
    (.next ([-3615000000000], [5985000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next
    ([-915000000000], [1485000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-1995000000000],
    [3225000000000]) (some (1, 5, 8)) (some (1, 5, 8)) fan67Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan67Owner0Part2 : FanWitness := (.next ([195000000000], [540000000000]) (some (0, 3, 10)) (some
    (0, 3, 10)) (.next ([1050000000000], [3000000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next
    ([435000000000], [1290000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([1620000000000],
    [5235000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([1080000000000], [4545000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) (.next ([1080000000000], [5415000000000]) (some (0, 3, 10))
    (some (0, 3, 10)) (.next ([360000000000], [1995000000000]) (some (0, 3, 10)) (some (0, 3, 10))
    (.next ([210000000000], [1455000000000]) (some (0, 3, 10)) (some (0, 4, 10)) (.next
    ([255000000000], [2190000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([435000000000],
    [4065000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([540000000000], [6105000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([435000000000], [4935000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([345000000000], [6195000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    (.next ([360000000000], [6480000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([165000000000], [6570000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([165000000000],
    [6855000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([15000000000], [1275000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([0], [870000000000]) (some (0, 4, 10)) (some (0, 4,
    10)) (.next ([-30000000000], [6945000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next
    ([-375000000000], [7590000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-570000000000],
    [7680000000000]) (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-915000000000], [7770000000000])
    (some (0, 4, 10)) (some (0, 4, 10)) (.next ([-1110000000000], [7860000000000]) (some (0, 4, 10))
    (some (0, 4, 10)) (.next ([-165000000000], [1080000000000]) (some (0, 4, 10)) (some (0, 4, 10))
    fan67Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan67Owner0Part3 : FanWitness := (.next ([2055000000000], [1305000000000]) (some (9, 3, 5))
    (some (9, 3, 5)) (.next ([645000000000], [480000000000]) (some (9, 3, 5)) (some (9, 3, 5))
    (.next ([1860000000000], [1395000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
    ([1185000000000], [915000000000]) (some (9, 3, 5)) (some (9, 3, 10)) (.next ([3495000000000],
    [2970000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([195000000000], [180000000000])
    (some (9, 3, 10)) (some (9, 3, 10)) (.next ([375000000000], [375000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([180000000000], [195000000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([1920000000000], [2130000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([2535000000000], [2880000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([90000000000],
    [105000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([810000000000], [1110000000000])
    (some (9, 3, 10)) (some (9, 3, 10)) (.next ([2355000000000], [3255000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([2535000000000], [3750000000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([2370000000000], [3615000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([570000000000], [915000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([1230000000000],
    [1995000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([2160000000000], [3630000000000])
    (some (9, 3, 10)) (some (9, 3, 10)) (.next ([2355000000000], [4125000000000]) (some (9, 3, 10))
    (some (9, 3, 10)) (.next ([1125000000000], [2190000000000]) (some (9, 3, 10)) (some (9, 3, 10))
    (.next ([375000000000], [735000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next
    ([180000000000], [360000000000]) (some (9, 3, 10)) (some (9, 3, 10)) (.next ([2160000000000],
    [4500000000000]) (some (0, 3, 10)) (some (0, 3, 10)) (.next ([1620000000000], [4365000000000])
    (some (0, 3, 10)) (some (0, 3, 10)) fan67Owner0Part2))))))))))))))))))))))))

theorem excluded64_1 : ExcludedOn (model64.B 1 ++ [step64.q]) 9000000000000 (model64.caps 1)
    (model64.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_2 : ExcludedOn (model64.B 2 ++ [step64.q]) 9000000000000 (model64.caps 2)
    (model64.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2430000000000], [15000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([4950000000000], [1245000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([750000000000], [495000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([2745000000000, 9000000000000], [3825000000000, -9000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (0, 5,
      3)) (some (0, 5, 3)) (.next ([2730000000000, 9000000000000], [6270000000000, -9000000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1620000000000, 9000000000000], [6570000000000, 0])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([1125000000000], [5445000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) (.next ([1110000000000], [7890000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([375000000000], [4950000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0],
      [5445000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-15000000000], [2445000000000])
      (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-1245000000000], [6195000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-495000000000], [1245000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3825000000000, 9000000000000], [6570000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3330000000000, 9000000000000], [5325000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-6270000000000, 9000000000000], [9000000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-6570000000000, 0], [8190000000000, 9000000000000]) (some (0, 3, 4)) (some (5, 3, 4))
      (.next ([-5445000000000], [6570000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-7890000000000], [9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-4950000000000], [5325000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3,
      4)) (some (5, 3, 0)) (some (5, 3, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded64_3 : ExcludedOn (model64.B 3 ++ [step64.q]) 9000000000000 (model64.caps 3)
    (model64.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [675000000000]) (some (4, 0, 6))
      (some (5, 0, 6)) (.next ([2565000000000], [375000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([5130000000000, 9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6)) (some (5,
      0, 6)) (.next ([3000000000000], [1620000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([4620000000000], [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1710000000000],
      [1425000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3510000000000], [3240000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1995000000000, 9000000000000], [3330000000000,
      -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1620000000000], [3270000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 3))
      (some (5, 0, 3)) (.next ([1140000000000], [3510000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      (.next ([1890000000000], [6000000000000]) (some (5, 0, 3)) (some (5, 0, 3))
      fan64Owner3Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded64_4 : ExcludedOn (model64.B 4 ++ [step64.q]) 9000000000000 (model64.caps 4)
    (model64.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7890000000000], [1110000000000]) (some (4, 0,
      5)) (some (4, 1, 5)) fan64Owner4Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded64_5 : ExcludedOn (model64.B 5 ++ [step64.q]) 9000000000000 (model64.caps 5)
    (model64.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_6 : ExcludedOn (model64.B 6 ++ [step64.q]) 9000000000000 (model64.caps 6)
    (model64.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_7 : ExcludedOn (model64.B 7 ++ [step64.q]) 9000000000000 (model64.caps 7)
    (model64.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_8 : ExcludedOn (model64.B 8 ++ [step64.q]) 9000000000000 (model64.caps 8)
    (model64.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_9 : ExcludedOn (model64.B 9 ++ [step64.q]) 9000000000000 (model64.caps 9)
    (model64.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked64 : StepValid model64 9000000000000 step64 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded64_1
    · exact excluded64_2
    · exact excluded64_3
    · exact excluded64_4
    · exact excluded64_5
    · exact excluded64_6
    · exact excluded64_7
    · exact excluded64_8
    · exact excluded64_9
theorem next64 : model64.insert step64 = model65 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded65_0 : ExcludedOn (model65.B 0 ++ [step65.q]) 9000000000000 (model65.caps 0)
    (model65.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6915000000000], [30000000000]) (some (9, 2, 5))
      (some (9, 3, 5)) (.next ([7215000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([7110000000000], [570000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([3420000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([6855000000000],
      [915000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4230000000000], [645000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([6750000000000], [1110000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([915000000000], [165000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([1185000000000], [300000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([5730000000000], [1560000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([5625000000000],
      [1755000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([4230000000000], [1515000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([645000000000], [480000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) fan65Owner0Part3))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded65_2 : ExcludedOn (model65.B 2 ++ [step65.q]) 9000000000000 (model65.caps 2)
    (model65.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_3 : ExcludedOn (model65.B 3 ++ [step65.q]) 9000000000000 (model65.caps 3)
    (model65.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_4 : ExcludedOn (model65.B 4 ++ [step65.q]) 9000000000000 (model65.caps 4)
    (model65.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_5 : ExcludedOn (model65.B 5 ++ [step65.q]) 9000000000000 (model65.caps 5)
    (model65.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_6 : ExcludedOn (model65.B 6 ++ [step65.q]) 9000000000000 (model65.caps 6)
    (model65.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4230000000000, 9000000000000], [4770000000000,
      -9000000000000]) (some (3, 0, 1)) (some (3, 0, 2)) (.next ([2610000000000], [6390000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1620000000000, 9000000000000], [4770000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1620000000000, 9000000000000],
      [7380000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1620000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-4770000000000,
      9000000000000], [9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-6390000000000],
      [9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4770000000000, 9000000000000],
      [6390000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7380000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1,
      3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_7 : ExcludedOn (model65.B 7 ++ [step65.q]) 9000000000000 (model65.caps 7)
    (model65.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_8 : ExcludedOn (model65.B 8 ++ [step65.q]) 9000000000000 (model65.caps 8)
    (model65.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_9 : ExcludedOn (model65.B 9 ++ [step65.q]) 9000000000000 (model65.caps 9)
    (model65.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked65 : StepValid model65 9000000000000 step65 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded65_0
    · exact (hj rfl).elim
    · exact excluded65_2
    · exact excluded65_3
    · exact excluded65_4
    · exact excluded65_5
    · exact excluded65_6
    · exact excluded65_7
    · exact excluded65_8
    · exact excluded65_9
theorem next65 : model65.insert step65 = model66 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded66_0 : ExcludedOn (model66.B 0 ++ [step66.q]) 9000000000000 (model66.caps 0)
    (model66.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_2 : ExcludedOn (model66.B 2 ++ [step66.q]) 9000000000000 (model66.caps 2)
    (model66.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [810000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) fan66Owner2Part0)) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
  decide +kernel

theorem excluded66_3 : ExcludedOn (model66.B 3 ++ [step66.q]) 9000000000000 (model66.caps 3)
    (model66.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_4 : ExcludedOn (model66.B 4 ++ [step66.q]) 9000000000000 (model66.caps 4)
    (model66.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_5 : ExcludedOn (model66.B 5 ++ [step66.q]) 9000000000000 (model66.caps 5)
    (model66.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_6 : ExcludedOn (model66.B 6 ++ [step66.q]) 9000000000000 (model66.caps 6)
    (model66.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_7 : ExcludedOn (model66.B 7 ++ [step66.q]) 9000000000000 (model66.caps 7)
    (model66.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [834000000000]) (some (2, 4, 1))
      (some (3, 4, 2)) (.next ([3630000000000, -9000000000000], [834000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([5250000000000], [1350000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([5250000000000], [4140000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([3630000000000, -9000000000000], [4140000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1170000000000, -9000000000000], [1620000000000, 9000000000000]) (some (0, 4, 2)) (some (0,
      4, 2)) (.next ([1956000000000], [3294000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([0], [3306000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-834000000000],
      [6084000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next ([-834000000000, 0], [4464000000000,
      -9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1350000000000], [6600000000000])
      (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-4140000000000], [9390000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-4140000000000, 0], [7770000000000, -9000000000000]) (some (4, 1,
      2)) (some (4, 1, 2)) (.next ([-1620000000000, -9000000000000], [2790000000000]) (some (4, 1,
      2)) (some (4, 1, 2)) (.next ([-3294000000000], [5250000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.terminal (some (4, 1, 2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded66_8 : ExcludedOn (model66.B 8 ++ [step66.q]) 9000000000000 (model66.caps 8)
    (model66.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_9 : ExcludedOn (model66.B 9 ++ [step66.q]) 9000000000000 (model66.caps 9)
    (model66.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked66 : StepValid model66 9000000000000 step66 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded66_0
    · exact (hj rfl).elim
    · exact excluded66_2
    · exact excluded66_3
    · exact excluded66_4
    · exact excluded66_5
    · exact excluded66_6
    · exact excluded66_7
    · exact excluded66_8
    · exact excluded66_9
theorem next66 : model66.insert step66 = model67 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded67_0 : ExcludedOn (model67.B 0 ++ [step67.q]) 9000000000000 (model67.caps 0)
    (model67.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6915000000000], [30000000000]) (some (9, 2, 5))
      (some (9, 3, 5)) (.next ([7215000000000], [375000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([7110000000000], [570000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([6855000000000], [915000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([6750000000000],
      [1110000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([915000000000], [165000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([1185000000000], [300000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) (.next ([5730000000000], [1560000000000]) (some (9, 3, 5)) (some (9, 3, 5))
      (.next ([5625000000000], [1755000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next
      ([3285000000000], [1515000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([3480000000000],
      [1695000000000]) (some (9, 3, 5)) (some (9, 3, 5)) (.next ([3660000000000], [1890000000000])
      (some (9, 3, 5)) (some (9, 3, 5)) (.next ([3855000000000], [2430000000000]) (some (9, 3, 5))
      (some (9, 3, 5)) fan67Owner0Part3))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded67_2 : ExcludedOn (model67.B 2 ++ [step67.q]) 9000000000000 (model67.caps 2)
    (model67.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_3 : ExcludedOn (model67.B 3 ++ [step67.q]) 9000000000000 (model67.caps 3)
    (model67.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_4 : ExcludedOn (model67.B 4 ++ [step67.q]) 9000000000000 (model67.caps 4)
    (model67.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_5 : ExcludedOn (model67.B 5 ++ [step67.q]) 9000000000000 (model67.caps 5)
    (model67.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_6 : ExcludedOn (model67.B 6 ++ [step67.q]) 9000000000000 (model67.caps 6)
    (model67.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [1125000000000, -9000000000000])
      (some (2, 0, 1)) (some (2, 0, 2)) (.next ([4050000000000, 9000000000000], [2205000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([2430000000000], [3825000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1620000000000, 9000000000000], [7380000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1620000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1125000000000, 9000000000000],
      [4950000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2205000000000,
      9000000000000], [6255000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3825000000000],
      [6255000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7380000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_7 : ExcludedOn (model67.B 7 ++ [step67.q]) 9000000000000 (model67.caps 7)
    (model67.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_8 : ExcludedOn (model67.B 8 ++ [step67.q]) 9000000000000 (model67.caps 8)
    (model67.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_9 : ExcludedOn (model67.B 9 ++ [step67.q]) 9000000000000 (model67.caps 9)
    (model67.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked67 : StepValid model67 9000000000000 step67 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded67_0
    · exact (hj rfl).elim
    · exact excluded67_2
    · exact excluded67_3
    · exact excluded67_4
    · exact excluded67_5
    · exact excluded67_6
    · exact excluded67_7
    · exact excluded67_8
    · exact excluded67_9
theorem next67 : model67.insert step67 = model68 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates

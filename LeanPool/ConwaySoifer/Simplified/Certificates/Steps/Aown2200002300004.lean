/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown220000230000
import Mathlib.Tactic.FinCases

/-!
# Aown 220000 230000 4

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
namespace Aown220000230000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner2Part0 : FanWitness := (.next ([4050000000000, -9000000000000], [6105000000000,
    9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([375000000000], [1260000000000]) (some
    (0, 5, 2)) (some (0, 5, 2)) (.next ([1605000000000], [5505000000000]) (some (0, 5, 2)) (some (0,
    5, 3)) (.next ([1260000000000], [4770000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1230000000000], [5790000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([855000000000],
    [4530000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([855000000000, 0], [6165000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([0, 0], [2835000000000,
    9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([0, -9000000000000], [375000000000,
    0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-90000000000, -9000000000000], [750000000000, 0])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-90000000000], [375000000000]) (some (0, 5, 4)) (some
    (0, 5, 4)) (.next ([-1980000000000, -9000000000000], [7365000000000, 9000000000000]) (some (0,
    5, 4)) (some (0, 5, 4)) (.next ([-3270000000000], [10155000000000]) (some (0, 5, 4)) (some (0,
    5, 4)) (.next ([-3135000000000, -9000000000000], [6030000000000, 0]) (some (0, 5, 4)) (some (0,
    5, 4)) (.next ([-3135000000000], [5655000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-975000000000], [1725000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3045000000000],
    [5280000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6105000000000, -9000000000000],
    [10155000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1260000000000], [1635000000000])
    (some (0, 2, 4)) (some (5, 2, 4)) (.next ([-5505000000000], [7110000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-4770000000000], [6030000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-5790000000000], [7020000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([-4530000000000], [5385000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-6165000000000,
    9000000000000], [7020000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal
    (some (5, 2, 4)) (some (5, 2, 0)) (some (5, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner2Part0 : FanWitness := (.next ([750000000000], [975000000000]) (some (0, 5, 2)) (some
    (0, 5, 2)) (.next ([375000000000], [1260000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next
    ([1605000000000], [5505000000000]) (some (0, 5, 2)) (some (0, 5, 3)) (.next ([1230000000000],
    [5790000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([855000000000], [4530000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([855000000000, 0], [6165000000000, -9000000000000])
    (some (0, 5, 3)) (some (0, 5, 4)) (.next ([210000000000], [2295000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([525000000000, -9000000000000], [7155000000000, 9000000000000]) (some
    (0, 5, 4)) (some (0, 5, 4)) (.next ([0, 0], [2835000000000, 9000000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([0, -9000000000000], [375000000000, 0]) (some (0, 5, 4)) (some (0, 5,
    4)) (.next ([-90000000000, -9000000000000], [750000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-90000000000], [375000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-1980000000000, -9000000000000], [7365000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5,
    4)) (.next ([-660000000000], [2130000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-570000000000], [1755000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4320000000000],
    [7680000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-975000000000], [1725000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1260000000000], [1635000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-5505000000000], [7110000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-5790000000000], [7020000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-4530000000000], [5385000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-6165000000000,
    9000000000000], [7020000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-2295000000000], [2505000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-7155000000000,
    -9000000000000], [7680000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2, 4))
    (some (5, 2, 0)) (some (5, 2, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner0Part0 : FanWitness := (.next ([-2475000000000], [3525000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-120000000000], [165000000000]) (some (2, 7, 10)) (some (2, 8, 10))
    (.next ([-4725000000000], [6360000000000]) (some (2, 8, 10)) (some (3, 8, 10)) (.next
    ([-1320000000000], [1755000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-3825000000000], [4980000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-4965000000000], [6315000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-5166000000000], [6561000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next ([-201000000000],
    [246000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next ([-1080000000000], [1314000000000])
    (some (3, 8, 10)) (some (3, 8, 10)) (.next ([-5625000000000], [6795000000000]) (some (3, 8, 10))
    (some (3, 8, 10)) (.next ([-1410000000000], [1695000000000]) (some (3, 8, 10)) (some (3, 8, 10))
    (.next ([-4005000000000], [4785000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-6000000000000], [6975000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-4050000000000], [4665000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-1695000000000], [1935000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-6165000000000], [7020000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-1575000000000], [1740000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-3825000000000], [4125000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-1860000000000], [1980000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-2295000000000], [2430000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-6480000000000], [6795000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-3630000000000], [3750000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-1455000000000], [1494000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.next
    ([-3510000000000], [3585000000000]) (some (3, 8, 10)) (some (3, 8, 10)) (.terminal (some (3, 8,
    10)) (some (3, 8, 10)) (some (3, 8, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner0Part1 : FanWitness := (.next ([-3090000000000], [7005000000000]) (some (12, 7, 10))
    (some (12, 7, 10)) (.next ([-3291000000000], [7251000000000]) (some (12, 7, 10)) (some (12, 7,
    10)) (.next ([-420000000000], [915000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next
    ([-225000000000], [459000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next ([-540000000000],
    [1080000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next ([-3750000000000],
    [7485000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next ([-420000000000], [834000000000])
    (some (12, 7, 10)) (some (12, 7, 10)) (.next ([-465000000000], [900000000000]) (some (12, 7,
    10)) (some (12, 7, 10)) (.next ([-660000000000], [1275000000000]) (some (1, 7, 10)) (some (1, 7,
    10)) (.next ([-195000000000], [375000000000]) (some (1, 7, 10)) (some (1, 7, 10)) (.next
    ([-4125000000000], [7665000000000]) (some (1, 7, 10)) (some (2, 7, 10)) (.next ([-540000000000],
    [999000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-780000000000], [1440000000000])
    (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-240000000000], [441000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-4290000000000], [7710000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    (.next ([-3810000000000], [6780000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next
    ([-315000000000], [540000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-4605000000000],
    [7485000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-3390000000000], [5445000000000])
    (some (2, 7, 10)) (some (2, 7, 10)) (.next ([-3345000000000], [5160000000000]) (some (2, 7, 10))
    (some (2, 7, 10)) (.next ([-4785000000000], [7290000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    (.next ([-4830000000000], [7170000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next
    ([-1035000000000], [1515000000000]) (some (2, 7, 10)) (some (2, 7, 10)) (.next
    ([-3591000000000], [5205000000000]) (some (2, 7, 10)) (some (2, 7, 10))
    fan36Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner0Part2 : FanWitness := (.next ([0], [855000000000]) (some (12, 6, 9)) (some (12, 7,
    9)) (.next ([-60000000000], [6660000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next
    ([-225000000000], [6705000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-81000000000],
    [1620000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-420000000000], [6915000000000])
    (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-660000000000], [6870000000000]) (some (12, 7, 9))
    (some (12, 7, 9)) (.next ([-555000000000], [4860000000000]) (some (12, 7, 9)) (some (12, 7, 9))
    (.next ([-861000000000], [7116000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next
    ([-45000000000], [285000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-195000000000],
    [1230000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-1320000000000], [7350000000000])
    (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-1695000000000], [7530000000000]) (some (12, 7, 9))
    (some (12, 7, 9)) (.next ([-315000000000], [1395000000000]) (some (12, 7, 9)) (some (12, 7, 9))
    (.next ([-1860000000000], [7575000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next
    ([-1245000000000], [4905000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-690000000000],
    [2565000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-180000000000], [660000000000])
    (some (12, 7, 9)) (some (12, 7, 10)) (.next ([-2175000000000], [7350000000000]) (some (12, 7,
    10)) (some (12, 7, 10)) (.next ([-2355000000000], [7155000000000]) (some (12, 7, 10)) (some (12,
    7, 10)) (.next ([-2400000000000], [7035000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next
    ([-375000000000], [1035000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next
    ([-2850000000000], [7050000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next
    ([-495000000000], [1200000000000]) (some (12, 7, 10)) (some (12, 7, 10)) (.next
    ([-225000000000], [540000000000]) (some (12, 7, 10)) (some (12, 7, 10))
    fan36Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner0Part3 : FanWitness := (.next ([1050000000000], [2475000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([45000000000], [120000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([1635000000000], [4725000000000]) (some (10, 5, 8)) (some (10, 6, 8)) (.next
    ([435000000000], [1320000000000]) (some (10, 6, 8)) (some (12, 6, 8)) (.next ([1155000000000],
    [3825000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([1350000000000], [4965000000000])
    (some (12, 6, 8)) (some (12, 6, 8)) (.next ([1395000000000], [5166000000000]) (some (12, 6, 8))
    (some (12, 6, 8)) (.next ([45000000000], [201000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([234000000000], [1080000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next
    ([1170000000000], [5625000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([285000000000],
    [1410000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([780000000000], [4005000000000])
    (some (12, 6, 8)) (some (12, 6, 8)) (.next ([975000000000], [6000000000000]) (some (12, 6, 8))
    (some (12, 6, 8)) (.next ([615000000000], [4050000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([240000000000], [1695000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next
    ([855000000000], [6165000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([165000000000],
    [1575000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([300000000000], [3825000000000])
    (some (12, 6, 8)) (some (12, 6, 8)) (.next ([120000000000], [1860000000000]) (some (12, 6, 8))
    (some (12, 6, 8)) (.next ([135000000000], [2295000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([315000000000], [6480000000000]) (some (12, 6, 8)) (some (12, 6, 9)) (.next
    ([120000000000], [3630000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([39000000000],
    [1455000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([75000000000], [3510000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) fan36Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan36Owner0Part4 : FanWitness := (.next ([3915000000000], [3090000000000]) (some (10, 3, 8))
    (some (10, 4, 8)) (.next ([3960000000000], [3291000000000]) (some (10, 4, 8)) (some (10, 4, 8))
    (.next ([495000000000], [420000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next
    ([234000000000], [225000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([540000000000],
    [540000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([3735000000000], [3750000000000])
    (some (10, 4, 8)) (some (10, 4, 8)) (.next ([414000000000], [420000000000]) (some (10, 4, 8))
    (some (10, 4, 8)) (.next ([435000000000], [465000000000]) (some (10, 4, 8)) (some (10, 4, 8))
    (.next ([615000000000], [660000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next
    ([180000000000], [195000000000]) (some (10, 4, 8)) (some (10, 4, 8)) (.next ([3540000000000],
    [4125000000000]) (some (10, 4, 8)) (some (10, 5, 8)) (.next ([459000000000], [540000000000])
    (some (10, 5, 8)) (some (10, 5, 8)) (.next ([660000000000], [780000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([201000000000], [240000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([3420000000000], [4290000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([2970000000000], [3810000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([225000000000],
    [315000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([2880000000000], [4605000000000])
    (some (10, 5, 8)) (some (10, 5, 8)) (.next ([2055000000000], [3390000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([1815000000000], [3345000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([2505000000000], [4785000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([2340000000000], [4830000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([480000000000],
    [1035000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([1614000000000], [3591000000000])
    (some (10, 5, 8)) (some (10, 5, 8)) fan36Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part0 : FanWitness := (.next ([-4830000000000], [7170000000000]) (some (2, 7, 12))
    (some (2, 7, 12)) (.next ([-1035000000000], [1515000000000]) (some (2, 7, 12)) (some (2, 7, 12))
    (.next ([-3591000000000], [5205000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next
    ([-2475000000000], [3525000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next
    ([-5445000000000], [7725000000000]) (some (2, 7, 12)) (some (2, 8, 12)) (.next ([-120000000000],
    [165000000000]) (some (2, 8, 12)) (some (2, 8, 12)) (.next ([-3825000000000], [4980000000000])
    (some (2, 8, 12)) (some (3, 8, 12)) (.next ([-4965000000000], [6315000000000]) (some (3, 8, 12))
    (some (3, 8, 12)) (.next ([-5166000000000], [6561000000000]) (some (3, 8, 12)) (some (3, 8, 12))
    (.next ([-201000000000], [246000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-1080000000000], [1314000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-5625000000000], [6795000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-1410000000000], [1695000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-4005000000000], [4785000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-6000000000000], [6975000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-4050000000000], [4665000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-6165000000000], [7020000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-1575000000000], [1740000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-3825000000000], [4125000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-2295000000000], [2430000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-6480000000000], [6795000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-3630000000000], [3750000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-1455000000000], [1494000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.next
    ([-3510000000000], [3585000000000]) (some (3, 8, 12)) (some (3, 8, 12)) (.terminal (some (3, 8,
    12)) (some (3, 8, 12)) (some (3, 8, 12)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part1 : FanWitness := (.next ([-2175000000000], [7350000000000]) (some (0, 7, 10))
    (some (0, 7, 10)) (.next ([-1380000000000], [4200000000000]) (some (0, 7, 10)) (some (0, 7, 10))
    (.next ([-2355000000000], [7155000000000]) (some (0, 7, 10)) (some (0, 7, 10)) (.next
    ([-2400000000000], [7035000000000]) (some (0, 7, 10)) (some (0, 7, 10)) (.next ([-375000000000],
    [1035000000000]) (some (0, 7, 10)) (some (0, 7, 10)) (.next ([-495000000000], [1200000000000])
    (some (0, 7, 10)) (some (0, 7, 10)) (.next ([-225000000000], [540000000000]) (some (0, 7, 10))
    (some (0, 7, 10)) (.next ([-690000000000], [1635000000000]) (some (0, 7, 10)) (some (0, 7, 10))
    (.next ([-3090000000000], [7005000000000]) (some (0, 7, 10)) (some (0, 7, 12)) (.next
    ([-3291000000000], [7251000000000]) (some (0, 7, 12)) (some (0, 7, 12)) (.next ([-420000000000],
    [915000000000]) (some (0, 7, 12)) (some (0, 7, 12)) (.next ([-225000000000], [459000000000])
    (some (0, 7, 12)) (some (0, 7, 12)) (.next ([-540000000000], [1080000000000]) (some (0, 7, 12))
    (some (1, 7, 12)) (.next ([-3750000000000], [7485000000000]) (some (1, 7, 12)) (some (1, 7, 12))
    (.next ([-420000000000], [834000000000]) (some (1, 7, 12)) (some (1, 7, 12)) (.next
    ([-195000000000], [375000000000]) (some (1, 7, 12)) (some (1, 7, 12)) (.next ([-4125000000000],
    [7665000000000]) (some (1, 7, 12)) (some (2, 7, 12)) (.next ([-540000000000], [999000000000])
    (some (2, 7, 12)) (some (2, 7, 12)) (.next ([-4290000000000], [7710000000000]) (some (2, 7, 12))
    (some (2, 7, 12)) (.next ([-3810000000000], [6780000000000]) (some (2, 7, 12)) (some (2, 7, 12))
    (.next ([-315000000000], [540000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next
    ([-4605000000000], [7485000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next
    ([-3345000000000], [5160000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next
    ([-4785000000000], [7290000000000]) (some (2, 7, 12)) (some (2, 7, 12))
    fan37Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part2 : FanWitness := (.next ([0], [855000000000]) (some (12, 6, 9)) (some (12, 7,
    9)) (.next ([-60000000000], [6660000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next
    ([-225000000000], [6705000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-240000000000],
    [6111000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-285000000000], [5910000000000])
    (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-81000000000], [1620000000000]) (some (0, 7, 9))
    (some (0, 7, 9)) (.next ([-465000000000], [6570000000000]) (some (0, 7, 9)) (some (0, 7, 9))
    (.next ([-660000000000], [6945000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next
    ([-660000000000], [6870000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-780000000000],
    [7110000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-555000000000], [4860000000000])
    (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-861000000000], [7116000000000]) (some (0, 7, 9))
    (some (0, 7, 9)) (.next ([-195000000000], [1230000000000]) (some (0, 7, 9)) (some (0, 7, 9))
    (.next ([-1320000000000], [7425000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next
    ([-1320000000000], [7350000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-1245000000000],
    [6495000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-1695000000000], [7605000000000])
    (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-1695000000000], [7530000000000]) (some (0, 7, 9))
    (some (0, 7, 9)) (.next ([-315000000000], [1395000000000]) (some (0, 7, 9)) (some (0, 7, 9))
    (.next ([-1860000000000], [7650000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next
    ([-1860000000000], [7575000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-1245000000000],
    [4905000000000]) (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-690000000000], [2565000000000])
    (some (0, 7, 9)) (some (0, 7, 9)) (.next ([-180000000000], [660000000000]) (some (0, 7, 9))
    (some (0, 7, 10)) fan37Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part3 : FanWitness := (.next ([2340000000000], [4830000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([480000000000], [1035000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([1614000000000], [3591000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([1050000000000], [2475000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([2280000000000],
    [5445000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([45000000000], [120000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([1155000000000], [3825000000000]) (some (12, 5, 8))
    (some (12, 6, 8)) (.next ([1350000000000], [4965000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([1395000000000], [5166000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next
    ([45000000000], [201000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([234000000000],
    [1080000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([1170000000000], [5625000000000])
    (some (12, 6, 8)) (some (12, 6, 8)) (.next ([285000000000], [1410000000000]) (some (12, 6, 8))
    (some (12, 6, 8)) (.next ([780000000000], [4005000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([975000000000], [6000000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next
    ([615000000000], [4050000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([855000000000],
    [6165000000000]) (some (12, 6, 8)) (some (12, 6, 8)) (.next ([165000000000], [1575000000000])
    (some (12, 6, 8)) (some (12, 6, 8)) (.next ([300000000000], [3825000000000]) (some (12, 6, 8))
    (some (12, 6, 8)) (.next ([135000000000], [2295000000000]) (some (12, 6, 8)) (some (12, 6, 8))
    (.next ([315000000000], [6480000000000]) (some (12, 6, 8)) (some (12, 6, 9)) (.next
    ([120000000000], [3630000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([39000000000],
    [1455000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([75000000000], [3510000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) fan37Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner0Part4 : FanWitness := (.next ([5175000000000], [2175000000000]) (some (12, 3, 8))
    (some (12, 3, 8)) (.next ([2820000000000], [1380000000000]) (some (12, 3, 8)) (some (12, 3, 8))
    (.next ([4800000000000], [2355000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
    ([4635000000000], [2400000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([660000000000],
    [375000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([705000000000], [495000000000])
    (some (12, 3, 8)) (some (12, 3, 8)) (.next ([315000000000], [225000000000]) (some (12, 3, 8))
    (some (12, 3, 8)) (.next ([945000000000], [690000000000]) (some (12, 3, 8)) (some (12, 4, 8))
    (.next ([3915000000000], [3090000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([3960000000000], [3291000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([495000000000],
    [420000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([234000000000], [225000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([540000000000], [540000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([3735000000000], [3750000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([414000000000], [420000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([180000000000], [195000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([3540000000000],
    [4125000000000]) (some (12, 4, 8)) (some (12, 5, 8)) (.next ([459000000000], [540000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([3420000000000], [4290000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([2970000000000], [3810000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([225000000000], [315000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([2880000000000], [4605000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([1815000000000],
    [3345000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([2505000000000], [4785000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) fan37Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan37Owner2Part0 : FanWitness := (.next ([2955000000000], [3750000000000]) (some (0, 1, 2))
    (some (0, 1, 2)) (.next ([750000000000], [975000000000]) (some (0, 1, 2)) (some (0, 1, 2))
    (.next ([375000000000], [1260000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
    ([1605000000000], [5505000000000]) (some (0, 1, 2)) (some (0, 1, 3)) (.next ([1230000000000],
    [5790000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([855000000000], [4530000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([855000000000, 0], [6165000000000, -9000000000000])
    (some (0, 1, 3)) (some (0, 1, 4)) (.next ([0, 0], [2835000000000, 9000000000000]) (some (0, 1,
    4)) (some (0, 1, 4)) (.next ([0, -9000000000000], [375000000000, 0]) (some (0, 1, 4)) (some (0,
    1, 4)) (.next ([-90000000000, -9000000000000], [750000000000, 0]) (some (0, 1, 4)) (some (0, 1,
    4)) (.next ([-90000000000], [375000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([-1980000000000, -9000000000000], [7365000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 2,
    4)) (.next ([-660000000000, -9000000000000], [2430000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-3000000000000], [7680000000000]) (some (0, 2, 4)) (some (5, 2, 4)) (.next
    ([-3375000000000], [7965000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3750000000000,
    0], [8340000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-2430000000000],
    [4605000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-3750000000000], [6705000000000])
    (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-975000000000], [1725000000000]) (some (5, 2, 4))
    (some (5, 2, 4)) (.next ([-1260000000000], [1635000000000]) (some (5, 2, 4)) (some (5, 2, 4))
    (.next ([-5505000000000], [7110000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
    ([-5790000000000], [7020000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-4530000000000],
    [5385000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-6165000000000, 9000000000000],
    [7020000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.terminal (some (5, 2, 4))
    (some (5, 2, 0)) (some (5, 2, 4)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 8 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_7 : ExcludedOn (model32.B 7 ++ [step32.q]) 9000000000000 (model32.caps 7)
    (model32.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_8 : ExcludedOn (model32.B 8 ++ [step32.q]) 9000000000000 (model32.caps 8)
    (model32.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_9 : ExcludedOn (model32.B 9 ++ [step32.q]) 9000000000000 (model32.caps 9)
    (model32.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5250000000000], [870000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([3630000000000], [936000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3270000000000, -9000000000000], [870000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4314000000000, 0], [3456000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 3))
      (.next ([4314000000000], [5436000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([2334000000000, -9000000000000], [5436000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1110000000000, 9000000000000], [4140000000000, -9000000000000]) (some (4, 1, 3)) (some (4,
      1, 3)) (.next ([0, 0], [1980000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-870000000000], [6120000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-936000000000], [4566000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-870000000000],
      [4140000000000, -9000000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next ([-3456000000000,
      9000000000000], [7770000000000, -9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([-5436000000000], [9750000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5436000000000], [7770000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-4140000000000, 9000000000000], [5250000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([660000000000, -9000000000000],
      [90000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([285000000000],
      [90000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([5385000000000, 0], [1980000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([6885000000000], [3270000000000])
      (some (0, 5, 2)) (some (0, 5, 2)) (.next ([2895000000000, -9000000000000], [3135000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([2520000000000], [3135000000000])
      (some (0, 5, 2)) (some (0, 5, 2)) (.next ([750000000000], [975000000000]) (some (0, 5, 2))
      (some (0, 5, 2)) (.next ([2235000000000], [3045000000000]) (some (0, 5, 2)) (some (0, 5, 2))
      fan33Owner2Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5625000000000], [405000000000]) (some (4, 0, 1))
      (some (4, 0, 2)) (.next ([4950000000000, 9000000000000], [2895000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1815000000000], [2655000000000]) (some (4, 0, 2))
      (some (4, 0, 2)) (.next ([1935000000000], [2940000000000]) (some (4, 0, 2)) (some (4, 0, 2))
      (.next ([2970000000000], [4875000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([120000000000], [285000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1980000000000,
      9000000000000], [5910000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1575000000000,
      9000000000000], [6030000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [1980000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-405000000000],
      [6030000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-2895000000000, 9000000000000],
      [7845000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-2655000000000], [4470000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2940000000000], [4875000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-4875000000000], [7845000000000]) (some (0, 1, 2)) (some (0, 1, 4))
      (.next ([-285000000000], [405000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5910000000000, 0], [7890000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-6030000000000, 0], [7605000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.terminal (some (0, 1, 4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded33_7 : ExcludedOn (model33.B 7 ++ [step33.q]) 9000000000000 (model33.caps 7)
    (model33.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_8 : ExcludedOn (model33.B 8 ++ [step33.q]) 9000000000000 (model33.caps 8)
    (model33.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_9 : ExcludedOn (model33.B 9 ++ [step33.q]) 9000000000000 (model33.caps 9)
    (model33.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked33 : StepValid model33 9000000000000 step33 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
    · exact excluded33_6
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3300000000000, 9000000000000], [525000000000,
      -9000000000000]) none none (.next ([1125000000000, 0], [195000000000, 9000000000000]) none
      none (.next ([1845000000000, -9000000000000], [660000000000, 9000000000000]) none none (.next
      ([3825000000000], [3435000000000]) none none (.next ([1980000000000, 9000000000000],
      [1980000000000, 9000000000000]) none none (.next ([1980000000000, 9000000000000],
      [2775000000000, -9000000000000]) none none (.next ([855000000000, 9000000000000],
      [1785000000000]) none none (.next ([660000000000], [1380000000000]) (some (4, 2, 3)) (some (4,
      2, 3)) (.next ([1785000000000], [4095000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([0], [6735000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-525000000000, 9000000000000], [3825000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-195000000000, -9000000000000], [1320000000000, 9000000000000]) (some (4, 2, 3)) (some (4,
      2, 3)) (.next ([-660000000000, -9000000000000], [2505000000000, 0]) (some (4, 2, 3)) (some (4,
      2, 3)) (.next ([-3435000000000], [7260000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-1980000000000, -9000000000000], [3960000000000, 18000000000000]) (some (4, 2, 3)) (some (4,
      2, 3)) (.next ([-2775000000000, 9000000000000], [4755000000000, 0]) (some (4, 2, 3)) (some (4,
      2, 3)) (.next ([-1785000000000], [2640000000000, 9000000000000]) (some (4, 2, 3)) (some (4, 2,
      3)) (.next ([-1380000000000], [2040000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-4095000000000], [5880000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) none none))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([660000000000, -9000000000000],
      [90000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([285000000000],
      [90000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([5385000000000, 0], [1980000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([1470000000000], [660000000000])
      (some (0, 5, 2)) (some (0, 5, 2)) (.next ([1185000000000], [570000000000]) (some (0, 5, 2))
      (some (0, 5, 2)) (.next ([3360000000000], [4320000000000]) (some (0, 5, 2)) (some (0, 5, 2))
      fan34Owner2Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_7 : ExcludedOn (model34.B 7 ++ [step34.q]) 9000000000000 (model34.caps 7)
    (model34.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded34_1
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
  apply ExclusionHint.sound (.pair 7 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3564000000000], [750000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([5655000000000, 0], [1980000000000, 9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([1584000000000, -9000000000000], [750000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([2520000000000, -9000000000000], [1530000000000, 9000000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2430000000000, 9000000000000], [2070000000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4905000000000], [4314000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1980000000000, 9000000000000], [1980000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1605000000000], [4500000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1230000000000, 9000000000000], [4314000000000, 0])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([450000000000], [4050000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([186000000000], [3114000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([0, 0], [1980000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next
      ([-750000000000], [4314000000000]) (some (5, 1, 4)) (some (5, 2, 4)) (.next ([-1980000000000,
      -9000000000000], [7635000000000, 9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-750000000000, 0], [2334000000000, -9000000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next
      ([-1530000000000, -9000000000000], [4050000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
      ([-2070000000000, 9000000000000], [4500000000000, 0]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-4314000000000], [9219000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1980000000000,
      -9000000000000], [3960000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-4500000000000], [6105000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4314000000000,
      0], [5544000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 5)) (.next
      ([-4050000000000], [4500000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.next
      ([-3114000000000], [3300000000000]) (some (5, 3, 5)) (some (5, 3, 5)) (.terminal (some (5, 3,
      5)) (some (0, 3, 5)) (some (5, 3, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_7 : ExcludedOn (model35.B 7 ++ [step35.q]) 9000000000000 (model35.caps 7)
    (model35.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded36_0 : ExcludedOn (model36.B 0 ++ [step36.q]) 9000000000000 (model36.caps 0)
    (model36.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6600000000000], [60000000000]) (some (10, 3, 8))
      (some (10, 3, 8)) (.next ([6480000000000], [225000000000]) (some (10, 3, 8)) (some (10, 3, 8))
      (.next ([1539000000000], [81000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
      ([6495000000000], [420000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([6210000000000],
      [660000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([4305000000000], [555000000000])
      (some (10, 3, 8)) (some (10, 3, 8)) (.next ([6255000000000], [861000000000]) (some (10, 3, 8))
      (some (10, 3, 8)) (.next ([240000000000], [45000000000]) (some (10, 3, 8)) (some (10, 3, 8))
      (.next ([1035000000000], [195000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
      ([6030000000000], [1320000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
      ([5835000000000], [1695000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
      ([1080000000000], [315000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([5715000000000],
      [1860000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([3660000000000], [1245000000000])
      (some (10, 3, 8)) (some (10, 3, 8)) (.next ([1875000000000], [690000000000]) (some (10, 3, 8))
      (some (10, 3, 8)) (.next ([480000000000], [180000000000]) (some (10, 3, 8)) (some (10, 3, 8))
      (.next ([5175000000000], [2175000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
      ([4800000000000], [2355000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next
      ([4635000000000], [2400000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([660000000000],
      [375000000000]) (some (10, 3, 8)) (some (10, 3, 8)) (.next ([4200000000000], [2850000000000])
      (some (10, 3, 8)) (some (10, 3, 8)) (.next ([705000000000], [495000000000]) (some (10, 3, 8))
      (some (10, 3, 8)) (.next ([315000000000], [225000000000]) (some (10, 3, 8)) (some (10, 3, 8))
      fan36Owner0Part4))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_1 : ExcludedOn (model36.B 1 ++ [step36.q]) 9000000000000 (model36.caps 1)
    (model36.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7680000000000], [900000000000]) (some (2, 0, 3))
      (some (2, 1, 3)) (.next ([4335000000000], [4245000000000]) (some (2, 1, 3)) (some (2, 1, 3))
      (.next ([1980000000000, 9000000000000], [3345000000000]) (some (2, 1, 3)) (some (2, 1, 3))
      (.next ([1080000000000, 9000000000000], [6600000000000, -9000000000000]) (some (2, 1, 3))
      (some (2, 1, 3)) (.next ([0], [3345000000000]) (some (2, 1, 3)) (some (2, 1, 3)) (.next
      ([-900000000000], [8580000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4245000000000],
      [8580000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3345000000000], [5325000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 3, 3)) (.next ([-6600000000000, 9000000000000],
      [7680000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.terminal (some (0, 3, 2)) (some (0, 3,
      2)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded36_0
    · exact excluded36_1
    · exact excluded36_2
    · exact (hj rfl).elim
    · exact excluded36_4
    · exact excluded36_5
    · exact excluded36_6
    · exact excluded36_7
    · exact excluded36_8
    · exact excluded36_9
theorem next36 : model36.insert step36 = model37 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded37_0 : ExcludedOn (model37.B 0 ++ [step37.q]) 9000000000000 (model37.caps 0)
    (model37.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6600000000000], [60000000000]) (some (12, 3, 8))
      (some (12, 3, 8)) (.next ([6480000000000], [225000000000]) (some (12, 3, 8)) (some (12, 3, 8))
      (.next ([5871000000000], [240000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([5625000000000], [285000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([1539000000000],
      [81000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([6105000000000], [465000000000])
      (some (12, 3, 8)) (some (12, 3, 8)) (.next ([6285000000000], [660000000000]) (some (12, 3, 8))
      (some (12, 3, 8)) (.next ([6210000000000], [660000000000]) (some (12, 3, 8)) (some (12, 3, 8))
      (.next ([6330000000000], [780000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([4305000000000], [555000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([6255000000000],
      [861000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([1035000000000], [195000000000])
      (some (12, 3, 8)) (some (12, 3, 8)) (.next ([6105000000000], [1320000000000]) (some (12, 3,
      8)) (some (12, 3, 8)) (.next ([6030000000000], [1320000000000]) (some (12, 3, 8)) (some (12,
      3, 8)) (.next ([5250000000000], [1245000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([5910000000000], [1695000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([5835000000000], [1695000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next
      ([1080000000000], [315000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([5790000000000],
      [1860000000000]) (some (12, 3, 8)) (some (12, 3, 8)) (.next ([5715000000000], [1860000000000])
      (some (12, 3, 8)) (some (12, 3, 8)) (.next ([3660000000000], [1245000000000]) (some (12, 3,
      8)) (some (12, 3, 8)) (.next ([1875000000000], [690000000000]) (some (12, 3, 8)) (some (12, 3,
      8)) (.next ([480000000000], [180000000000]) (some (12, 3, 8)) (some (12, 3, 8))
      fan37Owner0Part4))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_1 : ExcludedOn (model37.B 1 ++ [step37.q]) 9000000000000 (model37.caps 1)
    (model37.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([375000000000, -9000000000000], [0,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([660000000000, -9000000000000],
      [90000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([285000000000],
      [90000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([5385000000000, 0], [1980000000000,
      9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([1770000000000, -9000000000000],
      [660000000000, 9000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([4680000000000],
      [3000000000000]) (some (0, 5, 2)) (some (0, 5, 2)) (.next ([4590000000000], [3375000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([4590000000000, -9000000000000], [3750000000000, 0])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([2175000000000], [2430000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) fan37Owner2Part0)))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded37_0
    · exact excluded37_1
    · exact excluded37_2
    · exact (hj rfl).elim
    · exact excluded37_4
    · exact excluded37_5
    · exact excluded37_6
    · exact excluded37_7
    · exact excluded37_8
    · exact excluded37_9
theorem next37 : model37.insert step37 = model38 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown220000230000
end ConwaySoifer.Simplified.Certificates

/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint220000230000
import Mathlib.Tactic.FinCases

/-!
# Sint 220000 230000 5

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
namespace Sint220000230000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part0 : FanWitness := (.next ([-420000000000], [573000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-1560000000000], [2100000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-5166000000000], [6906000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-5517000000000], [7257000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-5625000000000], [7305000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-360000000000],
    [465000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-5166000000000], [6561000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-5517000000000], [6912000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-5850000000000], [7290000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-5625000000000], [6960000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-5850000000000], [7209000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-6030000000000], [7365000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-6090000000000], [7410000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-6030000000000], [7284000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-6246000000000], [7365000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-621000000000],
    [729000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-5310000000000], [6210000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-6090000000000], [7065000000000]) (some (12, 6, 9))
    (some (12, 7, 9)) (.next ([-5490000000000], [6285000000000]) (some (12, 7, 9)) (some (12, 7, 9))
    (.next ([-6246000000000], [7020000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next
    ([-561000000000], [621000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-1665000000000],
    [1740000000000]) (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-6705000000000], [6825000000000])
    (some (12, 7, 9)) (some (12, 7, 9)) (.next ([-6705000000000], [6744000000000]) (some (12, 7, 9))
    (some (12, 7, 9)) (.terminal (some (12, 7, 9)) (some (12, 7, 9)) (some (12, 7,
    9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part1 : FanWitness := (.next ([-2520000000000], [6255000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([-540000000000], [1215000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([-420000000000], [924000000000]) (some (12, 5, 8)) (some (12, 5, 9)) (.next
    ([-810000000000], [1665000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-585000000000],
    [1200000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-540000000000], [1080000000000])
    (some (12, 5, 9)) (some (12, 5, 9)) (.next ([-666000000000], [1281000000000]) (some (12, 5, 9))
    (some (12, 5, 9)) (.next ([-1161000000000], [2160000000000]) (some (12, 5, 9)) (some (12, 5, 9))
    (.next ([-540000000000], [999000000000]) (some (12, 5, 9)) (some (12, 5, 9)) (.next
    ([-60000000000], [108000000000]) (some (12, 5, 9)) (some (12, 6, 9)) (.next ([-885000000000],
    [1560000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-621000000000], [1080000000000])
    (some (12, 6, 9)) (some (12, 6, 9)) (.next ([-105000000000], [180000000000]) (some (12, 6, 9))
    (some (12, 6, 9)) (.next ([-4311000000000], [7371000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    (.next ([-4491000000000], [7446000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-4662000000000], [7722000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-4770000000000], [7770000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-4842000000000], [7797000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-4950000000000], [7845000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-5235000000000], [7875000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-5415000000000], [7950000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-5391000000000], [7830000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-1512000000000], [2160000000000]) (some (12, 6, 9)) (some (12, 6, 9)) (.next
    ([-5571000000000], [7905000000000]) (some (12, 6, 9)) (some (12, 6, 9))
    fan41Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part2 : FanWitness := (.next ([-225000000000], [6705000000000]) (some (12, 4, 8))
    (some (12, 5, 8)) (.next ([-306000000000], [6705000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([-81000000000], [1620000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-420000000000], [6165000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-162000000000],
    [1701000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-765000000000], [6165000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-60000000000], [459000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([-1575000000000], [8730000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([-855000000000], [4515000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-900000000000], [4716000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-1755000000000],
    [8805000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-45000000000], [201000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-960000000000], [4155000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([-1008000000000], [4095000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([-1440000000000], [5715000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-1521000000000], [5796000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-432000000000],
    [1620000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-2430000000000], [8265000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-513000000000], [1701000000000]) (some (12, 5, 8))
    (some (12, 5, 8)) (.next ([-2430000000000], [7920000000000]) (some (12, 5, 8)) (some (12, 5, 8))
    (.next ([-480000000000], [1560000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next
    ([-1359000000000], [4095000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-561000000000],
    [1641000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-465000000000], [1320000000000])
    (some (12, 5, 8)) (some (12, 5, 8)) fan41Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part3 : FanWitness := (.next ([540000000000], [1560000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([1740000000000], [5166000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([1740000000000], [5517000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([1680000000000], [5625000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([105000000000],
    [360000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1395000000000], [5166000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1395000000000], [5517000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([1440000000000], [5850000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([1335000000000], [5625000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([1359000000000], [5850000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1335000000000],
    [6030000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1320000000000], [6090000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1254000000000], [6030000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([1119000000000], [6246000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([108000000000], [621000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([900000000000], [5310000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([975000000000],
    [6090000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([795000000000], [5490000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([774000000000], [6246000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([60000000000], [561000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([75000000000], [1665000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([120000000000], [6705000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([39000000000],
    [6705000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([0], [351000000000]) (some (12, 4,
    8)) (some (12, 4, 8)) fan41Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part4 : FanWitness := (.next ([675000000000], [540000000000]) (some (12, 3, 7)) (some
    (12, 3, 7)) (.next ([504000000000], [420000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next
    ([855000000000], [810000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([615000000000],
    [585000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([540000000000], [540000000000])
    (some (12, 3, 7)) (some (12, 3, 7)) (.next ([615000000000], [666000000000]) (some (12, 3, 7))
    (some (12, 3, 7)) (.next ([999000000000], [1161000000000]) (some (12, 3, 7)) (some (12, 3, 7))
    (.next ([459000000000], [540000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next
    ([48000000000], [60000000000]) (some (12, 3, 7)) (some (12, 4, 7)) (.next ([675000000000],
    [885000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next ([459000000000], [621000000000])
    (some (12, 4, 7)) (some (12, 4, 7)) (.next ([75000000000], [105000000000]) (some (12, 4, 7))
    (some (12, 4, 7)) (.next ([3060000000000], [4311000000000]) (some (12, 4, 7)) (some (12, 4, 8))
    (.next ([2955000000000], [4491000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([3060000000000], [4662000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([3000000000000],
    [4770000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([2955000000000], [4842000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([2895000000000], [4950000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([2640000000000], [5235000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([2535000000000], [5415000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([2439000000000], [5391000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([648000000000],
    [1512000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([2334000000000], [5571000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([153000000000], [420000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) fan41Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner0Part5 : FanWitness := (.next ([6399000000000], [306000000000]) (some (10, 12, 7))
    (some (10, 12, 7)) (.next ([1539000000000], [81000000000]) (some (10, 12, 7)) (some (10, 12, 7))
    (.next ([5745000000000], [420000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next
    ([1539000000000], [162000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next ([5400000000000],
    [765000000000]) (some (10, 12, 7)) (some (10, 12, 7)) (.next ([399000000000], [60000000000])
    (some (10, 12, 7)) (some (10, 12, 7)) (.next ([7155000000000], [1575000000000]) (some (10, 12,
    7)) (some (10, 12, 7)) (.next ([3660000000000], [855000000000]) (some (10, 12, 7)) (some (10,
    12, 7)) (.next ([3816000000000], [900000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next
    ([7050000000000], [1755000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([156000000000],
    [45000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([3195000000000], [960000000000])
    (some (10, 2, 7)) (some (10, 3, 7)) (.next ([3087000000000], [1008000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([4275000000000], [1440000000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([4275000000000], [1521000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([1188000000000], [432000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([5835000000000],
    [2430000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([1188000000000], [513000000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([5490000000000], [2430000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([1080000000000], [480000000000]) (some (10, 3, 7)) (some (12, 3, 7))
    (.next ([2736000000000], [1359000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next
    ([1080000000000], [561000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([855000000000],
    [465000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([3735000000000], [2520000000000])
    (some (12, 3, 7)) (some (12, 3, 7)) fan41Owner0Part4))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan41Owner4Part0 : FanWitness := (.next ([4770000000000], [405000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([5115000000000, 0], [1980000000000, 9000000000000]) (some (4, 1, 3)) (some
    (4, 1, 3)) (.next ([2070000000000], [1050000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
    ([2895000000000, -9000000000000], [2055000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1,
    5)) (.next ([3825000000000], [3195000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1920000000000], [1905000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1980000000000],
    [2250000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2865000000000], [4230000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1845000000000, -9000000000000], [5175000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([645000000000], [2055000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([165000000000], [4875000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([0, 0], [1980000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([-75000000000], [4950000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-405000000000],
    [5175000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-1980000000000, -9000000000000],
    [7095000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1050000000000],
    [3120000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2055000000000, -9000000000000],
    [4950000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3195000000000], [7020000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1905000000000], [3825000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2250000000000], [4230000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-4230000000000], [7095000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-5175000000000, -9000000000000], [7020000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-2055000000000], [2700000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4875000000000],
    [5040000000000]) (some (0, 2, 4)) (some (0, 3, 4)) (.terminal (some (0, 3, 4)) (some (0, 3, 4))
    (some (0, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part0 : FanWitness := (.next ([-420000000000], [573000000000]) (some (1, 6, 12))
    (some (1, 6, 12)) (.next ([-1560000000000], [2100000000000]) (some (1, 6, 12)) (some (1, 6, 12))
    (.next ([-5166000000000], [6906000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-5517000000000], [7257000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-5625000000000], [7305000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next ([-360000000000],
    [465000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next ([-5166000000000], [6561000000000])
    (some (1, 6, 12)) (some (2, 6, 12)) (.next ([-5517000000000], [6912000000000]) (some (2, 6, 12))
    (some (2, 6, 12)) (.next ([-5850000000000], [7290000000000]) (some (2, 6, 12)) (some (2, 6, 12))
    (.next ([-5625000000000], [6960000000000]) (some (2, 6, 12)) (some (2, 6, 12)) (.next
    ([-5850000000000], [7209000000000]) (some (2, 6, 12)) (some (2, 6, 12)) (.next
    ([-6030000000000], [7365000000000]) (some (2, 6, 12)) (some (2, 6, 12)) (.next
    ([-6090000000000], [7410000000000]) (some (2, 6, 12)) (some (2, 6, 12)) (.next
    ([-6030000000000], [7284000000000]) (some (2, 6, 12)) (some (2, 6, 12)) (.next
    ([-6246000000000], [7365000000000]) (some (2, 6, 12)) (some (2, 6, 12)) (.next ([-621000000000],
    [729000000000]) (some (2, 6, 12)) (some (2, 6, 12)) (.next ([-5310000000000], [6210000000000])
    (some (2, 6, 12)) (some (2, 6, 12)) (.next ([-6090000000000], [7065000000000]) (some (2, 6, 12))
    (some (2, 7, 12)) (.next ([-5490000000000], [6285000000000]) (some (2, 7, 12)) (some (2, 7, 12))
    (.next ([-6246000000000], [7020000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next
    ([-561000000000], [621000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next ([-1665000000000],
    [1740000000000]) (some (2, 7, 12)) (some (2, 7, 12)) (.next ([-6705000000000], [6825000000000])
    (some (2, 7, 12)) (some (2, 7, 12)) (.next ([-6705000000000], [6744000000000]) (some (2, 7, 12))
    (some (2, 7, 12)) (.terminal (some (2, 7, 12)) (some (2, 7, 12)) (some (2, 7,
    12)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part1 : FanWitness := (.next ([-420000000000], [924000000000]) (some (0, 5, 8)) (some
    (0, 5, 9)) (.next ([-810000000000], [1665000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next
    ([-585000000000], [1200000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-1575000000000],
    [3195000000000]) (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-540000000000], [1080000000000])
    (some (0, 5, 9)) (some (0, 5, 9)) (.next ([-666000000000], [1281000000000]) (some (0, 5, 9))
    (some (0, 5, 9)) (.next ([-1035000000000], [1980000000000]) (some (0, 5, 9)) (some (0, 5, 9))
    (.next ([-1161000000000], [2160000000000]) (some (0, 5, 9)) (some (0, 5, 12)) (.next
    ([-540000000000], [999000000000]) (some (0, 5, 12)) (some (0, 5, 12)) (.next ([-60000000000],
    [108000000000]) (some (0, 5, 12)) (some (0, 6, 12)) (.next ([-885000000000], [1560000000000])
    (some (0, 6, 12)) (some (1, 6, 12)) (.next ([-621000000000], [1080000000000]) (some (1, 6, 12))
    (some (1, 6, 12)) (.next ([-105000000000], [180000000000]) (some (1, 6, 12)) (some (1, 6, 12))
    (.next ([-4311000000000], [7371000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-4491000000000], [7446000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-4662000000000], [7722000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-4770000000000], [7770000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-4842000000000], [7797000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-4950000000000], [7845000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-5235000000000], [7875000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-5415000000000], [7950000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-5391000000000], [7830000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-1512000000000], [2160000000000]) (some (1, 6, 12)) (some (1, 6, 12)) (.next
    ([-5571000000000], [7905000000000]) (some (1, 6, 12)) (some (1, 6, 12))
    fan42Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part2 : FanWitness := (.next ([0], [351000000000]) (some (12, 4, 8)) (some (12, 4,
    8)) (.next ([-225000000000], [6705000000000]) (some (12, 4, 8)) (some (12, 5, 8)) (.next
    ([-240000000000], [6462000000000]) (some (12, 5, 8)) (some (12, 5, 8)) (.next ([-240000000000],
    [6111000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-306000000000], [6705000000000])
    (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-300000000000], [6570000000000]) (some (0, 5, 8))
    (some (0, 5, 8)) (.next ([-81000000000], [1620000000000]) (some (0, 5, 8)) (some (0, 5, 8))
    (.next ([-420000000000], [6165000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next
    ([-660000000000], [7035000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-162000000000],
    [1701000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-861000000000], [7191000000000])
    (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-765000000000], [6165000000000]) (some (0, 5, 8))
    (some (0, 5, 8)) (.next ([-60000000000], [459000000000]) (some (0, 5, 8)) (some (0, 5, 8))
    (.next ([-45000000000], [201000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next
    ([-1860000000000], [7650000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-1941000000000],
    [7650000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-432000000000], [1620000000000])
    (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-513000000000], [1701000000000]) (some (0, 5, 8))
    (some (0, 5, 8)) (.next ([-480000000000], [1560000000000]) (some (0, 5, 8)) (some (0, 5, 8))
    (.next ([-2400000000000], [7110000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next
    ([-561000000000], [1641000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-465000000000],
    [1320000000000]) (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-690000000000], [1635000000000])
    (some (0, 5, 8)) (some (0, 5, 8)) (.next ([-540000000000], [1215000000000]) (some (0, 5, 8))
    (some (0, 5, 8)) fan42Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part3 : FanWitness := (.next ([153000000000], [420000000000]) (some (12, 4, 8)) (some
    (12, 4, 8)) (.next ([540000000000], [1560000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([1740000000000], [5166000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1740000000000],
    [5517000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1680000000000], [5625000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([105000000000], [360000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([1395000000000], [5166000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([1395000000000], [5517000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([1440000000000], [5850000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1335000000000],
    [5625000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1359000000000], [5850000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([1335000000000], [6030000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([1320000000000], [6090000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([1254000000000], [6030000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([1119000000000], [6246000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([108000000000],
    [621000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([900000000000], [5310000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([975000000000], [6090000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([795000000000], [5490000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([774000000000], [6246000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([60000000000], [561000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([75000000000],
    [1665000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([120000000000], [6705000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([39000000000], [6705000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) fan42Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part4 : FanWitness := (.next ([504000000000], [420000000000]) (some (12, 3, 7)) (some
    (12, 3, 7)) (.next ([855000000000], [810000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next
    ([615000000000], [585000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([1620000000000],
    [1575000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([540000000000], [540000000000])
    (some (12, 3, 7)) (some (12, 3, 7)) (.next ([615000000000], [666000000000]) (some (12, 3, 7))
    (some (12, 3, 7)) (.next ([945000000000], [1035000000000]) (some (12, 3, 7)) (some (12, 3, 7))
    (.next ([999000000000], [1161000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next
    ([459000000000], [540000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([48000000000],
    [60000000000]) (some (12, 3, 7)) (some (12, 4, 7)) (.next ([675000000000], [885000000000]) (some
    (12, 4, 7)) (some (12, 4, 7)) (.next ([459000000000], [621000000000]) (some (12, 4, 7)) (some
    (12, 4, 7)) (.next ([75000000000], [105000000000]) (some (12, 4, 7)) (some (12, 4, 7)) (.next
    ([3060000000000], [4311000000000]) (some (12, 4, 7)) (some (12, 4, 8)) (.next ([2955000000000],
    [4491000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([3060000000000], [4662000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([3000000000000], [4770000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([2955000000000], [4842000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    (.next ([2895000000000], [4950000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next
    ([2640000000000], [5235000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([2535000000000],
    [5415000000000]) (some (12, 4, 8)) (some (12, 4, 8)) (.next ([2439000000000], [5391000000000])
    (some (12, 4, 8)) (some (12, 4, 8)) (.next ([648000000000], [1512000000000]) (some (12, 4, 8))
    (some (12, 4, 8)) (.next ([2334000000000], [5571000000000]) (some (12, 4, 8)) (some (12, 4, 8))
    fan42Owner0Part3))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_1 : ExcludedOn (model40.B 1 ++ [step40.q]) 9000000000000 (model40.caps 1)
    (model40.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6120000000000], [360000000000, 9000000000000])
      (some (2, 4, 1)) (some (3, 4, 1)) (.next ([1230000000000], [390000000000]) (some (3, 4, 1))
      (some (3, 4, 1)) (.next ([5730000000000], [1980000000000, 9000000000000]) (some (3, 4, 1))
      (some (3, 4, 2)) (.next ([6120000000000], [2265000000000]) (some (3, 4, 2)) (some (3, 4, 2))
      (.next ([5730000000000], [3885000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([1620000000000], [4500000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1980000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-360000000000,
      -9000000000000], [6480000000000, 9000000000000]) (some (0, 4, 2)) (some (4, 4, 2)) (.next
      ([-390000000000], [1620000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next ([-1980000000000,
      -9000000000000], [7710000000000, 9000000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-2265000000000], [8385000000000]) (some (4, 4, 2)) (some (4, 4, 2)) (.next
      ([-3885000000000], [9615000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-4500000000000], [6120000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6120000000000], [810000000000]) (some (0, 0, 3))
      (some (0, 1, 3)) (.next ([3885000000000], [5115000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([2070000000000], [3045000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([1005000000000], [2880000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [6930000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-810000000000], [6930000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-5115000000000], [9000000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-3045000000000], [5115000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2880000000000], [3885000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked40 : StepValid model40 9000000000000 step40 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded40_0
    · exact excluded40_1
    · exact excluded40_2
    · exact excluded40_3
    · exact (hj rfl).elim
    · exact excluded40_5
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6480000000000], [225000000000]) (some (9, 12,
      7)) (some (10, 12, 7)) fan41Owner0Part5))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [75000000000]) (some (4, 0, 3))
      (some (4, 1, 3)) fan41Owner4Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_9 : ExcludedOn (model41.B 9 ++ [step41.q]) 9000000000000 (model41.caps 9)
    (model41.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked41 : StepValid model41 9000000000000 step41 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded41_0
    · exact excluded41_1
    · exact excluded41_2
    · exact (hj rfl).elim
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6480000000000], [225000000000]) (some (12, 2,
      7)) (some (12, 2, 7)) (.next ([6222000000000], [240000000000]) (some (12, 2, 7)) (some (12, 2,
      7)) (.next ([5871000000000], [240000000000]) (some (12, 2, 7)) (some (12, 2, 7)) (.next
      ([6399000000000], [306000000000]) (some (12, 2, 7)) (some (12, 2, 7)) (.next ([6270000000000],
      [300000000000]) (some (12, 2, 7)) (some (12, 2, 7)) (.next ([1539000000000], [81000000000])
      (some (12, 2, 7)) (some (12, 2, 7)) (.next ([5745000000000], [420000000000]) (some (12, 2, 7))
      (some (12, 2, 7)) (.next ([6375000000000], [660000000000]) (some (12, 2, 7)) (some (12, 2, 7))
      (.next ([1539000000000], [162000000000]) (some (12, 2, 7)) (some (12, 2, 7)) (.next
      ([6330000000000], [861000000000]) (some (12, 2, 7)) (some (12, 2, 7)) (.next ([5400000000000],
      [765000000000]) (some (12, 2, 7)) (some (12, 2, 7)) (.next ([399000000000], [60000000000])
      (some (12, 2, 7)) (some (12, 2, 7)) (.next ([156000000000], [45000000000]) (some (12, 2, 7))
      (some (12, 2, 7)) (.next ([5790000000000], [1860000000000]) (some (12, 2, 7)) (some (12, 3,
      7)) (.next ([5709000000000], [1941000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next
      ([1188000000000], [432000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([1188000000000],
      [513000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([1080000000000], [480000000000])
      (some (12, 3, 7)) (some (12, 3, 7)) (.next ([4710000000000], [2400000000000]) (some (12, 3,
      7)) (some (12, 3, 7)) (.next ([1080000000000], [561000000000]) (some (12, 3, 7)) (some (12, 3,
      7)) (.next ([855000000000], [465000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next
      ([945000000000], [690000000000]) (some (12, 3, 7)) (some (12, 3, 7)) (.next ([675000000000],
      [540000000000]) (some (12, 3, 7)) (some (12, 3, 7)) fan42Owner0Part4))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000, -9000000000000], [1980000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1770000000000, -9000000000000],
      [660000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4590000000000,
      -9000000000000], [3750000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1320000000000], [2430000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1980000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1980000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-660000000000,
      -9000000000000], [2430000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3750000000000,
      0], [8340000000000, -9000000000000]) (some (0, 1, 2)) (some (3, 1, 2)) (.next
      ([-2430000000000], [3750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_6 : ExcludedOn (model42.B 6 ++ [step42.q]) 9000000000000 (model42.caps 6)
    (model42.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked42 : StepValid model42 9000000000000 step42 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded42_0
    · exact excluded42_1
    · exact excluded42_2
    · exact (hj rfl).elim
    · exact excluded42_4
    · exact excluded42_5
    · exact excluded42_6
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint220000230000
end ConwaySoifer.Simplified.Certificates

/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint220000230000
import Mathlib.Tactic.FinCases

/-!
# Sint 220000 230000 4

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
def fan32Owner6Part0 : FanWitness := (.next ([1530000000000, 9000000000000], [2520000000000,
    -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1230000000000, 9000000000000],
    [2730000000000, -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2070000000000,
    -9000000000000], [6930000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([375000000000, 0], [1980000000000, -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([375000000000], [3960000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next ([90000000000],
    [4200000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([0, 0], [1980000000000,
    9000000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-165000000000], [3675000000000])
    (some (6, 2, 4)) (some (6, 3, 4)) (.next ([-450000000000], [4500000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-375000000000], [3585000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-750000000000], [4710000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-990000000000], [4665000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-1605000000000,
    -9000000000000], [5940000000000, 9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-90000000000], [300000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2970000000000,
    9000000000000], [7020000000000, -9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-1980000000000, -9000000000000], [3960000000000, 18000000000000]) (some (6, 3, 4)) (some (6,
    3, 4)) (.next ([-4950000000000], [9000000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-2730000000000, -9000000000000], [4710000000000]) (some (6, 3, 4)) (some (6, 3, 5)) (.next
    ([-2520000000000, 9000000000000], [4050000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-2730000000000, 9000000000000], [3960000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-6930000000000, -9000000000000], [9000000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-1980000000000, 9000000000000], [2355000000000, -9000000000000]) (some (6, 3, 5)) (some (6, 3,
    5)) (.next ([-3960000000000], [4335000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.next
    ([-4200000000000], [4290000000000]) (some (6, 3, 5)) (some (6, 3, 5)) (.terminal (some (6, 3,
    5)) (some (6, 3, 5)) (some (6, 3, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan33Owner6Part0 : FanWitness := (.next ([1980000000000, -9000000000000], [2730000000000,
    9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([1530000000000, 9000000000000],
    [2520000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([1230000000000,
    9000000000000], [2730000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([1980000000000, 9000000000000], [5160000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([375000000000, 0], [1980000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([375000000000], [3960000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([0, 0],
    [1980000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-165000000000],
    [3675000000000]) (some (0, 2, 6)) (some (0, 3, 6)) (.next ([-450000000000], [4500000000000])
    (some (0, 3, 6)) (some (0, 3, 6)) (.next ([-375000000000], [3585000000000]) (some (0, 3, 6))
    (some (0, 3, 6)) (.next ([-750000000000], [4710000000000]) (some (0, 3, 6)) (some (1, 3, 6))
    (.next ([-1110000000000], [5610000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-1200000000000], [5910000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-1605000000000,
    -9000000000000], [5940000000000, 9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-90000000000], [300000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-1980000000000,
    -9000000000000], [3960000000000, 18000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-4785000000000], [9120000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-2430000000000,
    -9000000000000], [4500000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-2730000000000,
    -9000000000000], [4710000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-2520000000000,
    9000000000000], [4050000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-2730000000000,
    9000000000000], [3960000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-5160000000000, 0],
    [7140000000000, 9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-1980000000000,
    9000000000000], [2355000000000, -9000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-3960000000000], [4335000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.terminal (some (1, 3,
    6)) (some (1, 3, 6)) (some (1, 3, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner5Part0 : FanWitness := (.next ([750000000000], [4200000000000]) (some (6, 1, 4)) (some
    (6, 1, 4)) (.next ([135000000000], [2115000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next
    ([270000000000, -9000000000000], [6750000000000, 9000000000000]) (some (0, 1, 4)) (some (0, 1,
    4)) (.next ([75000000000], [3465000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
    ([30000000000], [4215000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0], [4905000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-45000000000], [750000000000]) (some (0, 1, 4)) (some
    (0, 2, 4)) (.next ([-660000000000], [4875000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1230000000000, -9000000000000], [6180000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2,
    4)) (.next ([-570000000000], [2070000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1980000000000, -9000000000000], [6885000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2,
    4)) (.next ([-1800000000000], [4770000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1965000000000], [4110000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1980000000000,
    -9000000000000], [4050000000000]) (some (0, 2, 4)) (some (0, 2, 6)) (.next ([-2640000000000,
    -9000000000000], [4875000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4770000000000],
    [7020000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3300000000000], [4200000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-660000000000], [825000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-4050000000000], [4905000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-4200000000000], [4950000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-2115000000000], [2250000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-6750000000000,
    -9000000000000], [7020000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-3465000000000],
    [3540000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4215000000000], [4245000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.terminal (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part0 : FanWitness := (.next ([-666000000000], [1281000000000]) (some (0, 5, 7))
    (some (0, 5, 10)) (.next ([-1161000000000], [2160000000000]) (some (0, 5, 10)) (some (0, 5, 10))
    (.next ([-540000000000], [999000000000]) (some (0, 5, 10)) (some (0, 5, 10)) (.next
    ([-60000000000], [108000000000]) (some (0, 5, 10)) (some (0, 6, 10)) (.next ([-621000000000],
    [1080000000000]) (some (0, 6, 10)) (some (1, 6, 10)) (.next ([-1512000000000], [2160000000000])
    (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-420000000000], [573000000000]) (some (1, 6, 10))
    (some (1, 6, 10)) (.next ([-1560000000000], [2100000000000]) (some (1, 6, 10)) (some (1, 6, 10))
    (.next ([-5166000000000], [6906000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-5517000000000], [7257000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-5625000000000], [7305000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-360000000000],
    [465000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-5166000000000], [6561000000000])
    (some (1, 6, 10)) (some (2, 6, 10)) (.next ([-5517000000000], [6912000000000]) (some (2, 6, 10))
    (some (2, 6, 10)) (.next ([-5625000000000], [6960000000000]) (some (2, 6, 10)) (some (2, 6, 10))
    (.next ([-6090000000000], [7410000000000]) (some (2, 6, 10)) (some (2, 6, 10)) (.next
    ([-6246000000000], [7365000000000]) (some (2, 6, 10)) (some (2, 6, 10)) (.next ([-621000000000],
    [729000000000]) (some (2, 6, 10)) (some (2, 6, 10)) (.next ([-6090000000000], [7065000000000])
    (some (2, 6, 10)) (some (2, 6, 10)) (.next ([-6246000000000], [7020000000000]) (some (2, 6, 10))
    (some (2, 6, 10)) (.next ([-561000000000], [621000000000]) (some (2, 6, 10)) (some (2, 6, 10))
    (.next ([-1665000000000], [1740000000000]) (some (2, 6, 10)) (some (2, 6, 10)) (.next
    ([-6705000000000], [6825000000000]) (some (2, 6, 10)) (some (2, 6, 10)) (.next
    ([-6705000000000], [6744000000000]) (some (2, 6, 10)) (some (2, 6, 10)) (.terminal (some (2, 6,
    10)) (some (2, 6, 10)) (some (2, 6, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part1 : FanWitness := (.next ([-225000000000], [6705000000000]) (some (10, 4, 7))
    (some (10, 5, 7)) (.next ([-306000000000], [6705000000000]) (some (10, 5, 7)) (some (10, 5, 7))
    (.next ([-81000000000], [1620000000000]) (some (10, 5, 7)) (some (10, 5, 7)) (.next
    ([-420000000000], [6165000000000]) (some (10, 5, 7)) (some (10, 5, 7)) (.next ([-162000000000],
    [1701000000000]) (some (10, 5, 7)) (some (10, 5, 7)) (.next ([-765000000000], [6165000000000])
    (some (10, 5, 7)) (some (10, 5, 7)) (.next ([-60000000000], [459000000000]) (some (10, 5, 7))
    (some (10, 5, 7)) (.next ([-45000000000], [201000000000]) (some (10, 5, 7)) (some (10, 5, 7))
    (.next ([-1800000000000], [7272000000000]) (some (10, 5, 7)) (some (10, 5, 7)) (.next
    ([-1860000000000], [7380000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-1800000000000],
    [6921000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-432000000000], [1620000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-2220000000000], [7845000000000]) (some (0, 5, 7))
    (some (0, 5, 7)) (.next ([-513000000000], [1701000000000]) (some (0, 5, 7)) (some (0, 5, 7))
    (.next ([-2421000000000], [8001000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next
    ([-480000000000], [1560000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-561000000000],
    [1641000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-3420000000000], [8460000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-3501000000000], [8460000000000]) (some (0, 5, 7))
    (some (0, 5, 7)) (.next ([-1440000000000], [3195000000000]) (some (0, 5, 7)) (some (0, 5, 7))
    (.next ([-420000000000], [924000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next
    ([-585000000000], [1200000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-540000000000],
    [1080000000000]) (some (0, 5, 7)) (some (0, 5, 7)) (.next ([-1785000000000], [3540000000000])
    (some (0, 5, 7)) (some (0, 5, 7)) fan35Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part2 : FanWitness := (.next ([999000000000], [1161000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([459000000000], [540000000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([48000000000], [60000000000]) (some (10, 3, 7)) (some (10, 4, 7)) (.next
    ([459000000000], [621000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([648000000000],
    [1512000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([153000000000], [420000000000])
    (some (10, 4, 7)) (some (10, 4, 7)) (.next ([540000000000], [1560000000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([1740000000000], [5166000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([1740000000000], [5517000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([1680000000000], [5625000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([105000000000],
    [360000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([1395000000000], [5166000000000])
    (some (10, 4, 7)) (some (10, 4, 7)) (.next ([1395000000000], [5517000000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([1335000000000], [5625000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([1320000000000], [6090000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([1119000000000], [6246000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([108000000000],
    [621000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([975000000000], [6090000000000])
    (some (10, 4, 7)) (some (10, 4, 7)) (.next ([774000000000], [6246000000000]) (some (10, 4, 7))
    (some (10, 4, 7)) (.next ([60000000000], [561000000000]) (some (10, 4, 7)) (some (10, 4, 7))
    (.next ([75000000000], [1665000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next
    ([120000000000], [6705000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([39000000000],
    [6705000000000]) (some (10, 4, 7)) (some (10, 4, 7)) (.next ([0], [351000000000]) (some (10, 4,
    7)) (some (10, 4, 7)) fan35Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner0Part3 : FanWitness := (.next ([6399000000000], [306000000000]) (some (10, 2, 6))
    (some (10, 2, 6)) (.next ([1539000000000], [81000000000]) (some (10, 2, 6)) (some (10, 2, 6))
    (.next ([5745000000000], [420000000000]) (some (10, 2, 6)) (some (10, 2, 6)) (.next
    ([1539000000000], [162000000000]) (some (10, 2, 6)) (some (10, 2, 7)) (.next ([5400000000000],
    [765000000000]) (some (10, 2, 7)) (some (10, 2, 7)) (.next ([399000000000], [60000000000]) (some
    (10, 2, 7)) (some (10, 2, 7)) (.next ([156000000000], [45000000000]) (some (10, 2, 7)) (some
    (10, 2, 7)) (.next ([5472000000000], [1800000000000]) (some (10, 2, 7)) (some (10, 3, 7)) (.next
    ([5520000000000], [1860000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([5121000000000],
    [1800000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([1188000000000], [432000000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([5625000000000], [2220000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([1188000000000], [513000000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([5580000000000], [2421000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([1080000000000], [480000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([1080000000000],
    [561000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([5040000000000], [3420000000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([4959000000000], [3501000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) (.next ([1755000000000], [1440000000000]) (some (10, 3, 7)) (some (10, 3, 7))
    (.next ([504000000000], [420000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next
    ([615000000000], [585000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([540000000000],
    [540000000000]) (some (10, 3, 7)) (some (10, 3, 7)) (.next ([1755000000000], [1785000000000])
    (some (10, 3, 7)) (some (10, 3, 7)) (.next ([615000000000], [666000000000]) (some (10, 3, 7))
    (some (10, 3, 7)) fan35Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan39Owner4Part0 : FanWitness := (.next ([2895000000000, -9000000000000], [2055000000000,
    9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2070000000000], [2340000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1980000000000], [2250000000000]) (some (5, 1, 3))
    (some (6, 1, 3)) (.next ([2070000000000, -9000000000000], [2880000000000, 9000000000000]) (some
    (6, 1, 3)) (some (6, 1, 3)) (.next ([2160000000000], [4230000000000]) (some (6, 1, 3)) (some (6,
    1, 3)) (.next ([1995000000000], [4950000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([645000000000], [2055000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([1170000000000],
    [4950000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([0, 0], [1980000000000,
    9000000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-75000000000], [4950000000000]) (some
    (6, 1, 3)) (some (6, 2, 4)) (.next ([-180000000000], [2880000000000]) (some (6, 2, 4)) (some (6,
    2, 4)) (.next ([-540000000000], [4875000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-540000000000], [4050000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-900000000000],
    [4950000000000]) (some (6, 2, 4)) (some (6, 2, 5)) (.next ([-1980000000000, -9000000000000],
    [6390000000000, 9000000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2250000000000],
    [6300000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2055000000000, -9000000000000],
    [4950000000000, 0]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2340000000000], [4410000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-2250000000000], [4230000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-2880000000000, -9000000000000], [4950000000000, 0]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-4230000000000], [6390000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.next ([-4950000000000], [6945000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-2055000000000], [2700000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-4950000000000],
    [6120000000000]) (some (6, 2, 5)) (some (6, 3, 5)) (.terminal (some (6, 3, 5)) (some (0, 3, 5))
    (some (6, 3, 5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_1 : ExcludedOn (model32.B 1 ++ [step32.q]) 9000000000000 (model32.caps 1)
    (model32.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_2 : ExcludedOn (model32.B 2 ++ [step32.q]) 9000000000000 (model32.caps 2)
    (model32.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_3 : ExcludedOn (model32.B 3 ++ [step32.q]) 9000000000000 (model32.caps 3)
    (model32.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_4 : ExcludedOn (model32.B 4 ++ [step32.q]) 9000000000000 (model32.caps 4)
    (model32.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_6 : ExcludedOn (model32.B 6 ++ [step32.q]) 9000000000000 (model32.caps 6)
    (model32.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3510000000000], [165000000000]) (some (5, 6, 3))
      (some (6, 6, 4)) (.next ([4050000000000], [450000000000]) (some (6, 6, 4)) (some (6, 6, 4))
      (.next ([3210000000000], [375000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
      ([3960000000000], [750000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([3675000000000],
      [990000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([4335000000000], [1605000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([210000000000], [90000000000]) (some
      (6, 1, 4)) (some (6, 1, 4)) (.next ([4050000000000, 0], [2970000000000, -9000000000000]) (some
      (6, 1, 4)) (some (6, 1, 4)) (.next ([1980000000000, 9000000000000], [1980000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([4050000000000], [4950000000000])
      (some (6, 1, 4)) (some (6, 1, 4)) (.next ([1980000000000, -9000000000000], [2730000000000,
      9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) fan32Owner6Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 8 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_2 : ExcludedOn (model33.B 2 ++ [step33.q]) 9000000000000 (model33.caps 2)
    (model33.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_3 : ExcludedOn (model33.B 3 ++ [step33.q]) 9000000000000 (model33.caps 3)
    (model33.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_4 : ExcludedOn (model33.B 4 ++ [step33.q]) 9000000000000 (model33.caps 4)
    (model33.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_6 : ExcludedOn (model33.B 6 ++ [step33.q]) 9000000000000 (model33.caps 6)
    (model33.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3510000000000], [165000000000]) (some (6, 1, 3))
      (some (6, 1, 6)) (.next ([4050000000000], [450000000000]) (some (6, 1, 6)) (some (6, 1, 6))
      (.next ([3210000000000], [375000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next
      ([3960000000000], [750000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([4500000000000],
      [1110000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next ([4710000000000], [1200000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4335000000000], [1605000000000, 9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([210000000000], [90000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([1980000000000, 9000000000000], [1980000000000, 9000000000000]) (some
      (0, 1, 6)) (some (0, 1, 6)) (.next ([4335000000000], [4785000000000]) (some (0, 1, 6)) (some
      (0, 1, 6)) (.next ([2070000000000, -9000000000000], [2430000000000, 9000000000000]) (some (0,
      1, 6)) (some (0, 1, 6)) fan33Owner6Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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

theorem excluded34_0 : ExcludedOn (model34.B 0 ++ [step34.q]) 9000000000000 (model34.caps 0)
    (model34.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([705000000000], [45000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([4215000000000], [660000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([4950000000000, 0], [1230000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([1500000000000], [570000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([4905000000000, 0], [1980000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([2970000000000], [1800000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2145000000000],
      [1965000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2070000000000, -9000000000000],
      [1980000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2235000000000,
      -9000000000000], [2640000000000, 9000000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next
      ([2250000000000], [4770000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([900000000000],
      [3300000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([165000000000], [660000000000])
      (some (6, 1, 3)) (some (6, 1, 3)) (.next ([855000000000], [4050000000000]) (some (6, 1, 3))
      (some (6, 1, 4)) fan34Owner5Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded34_1
    · exact excluded34_2
    · exact excluded34_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6480000000000], [225000000000]) (some (10, 2,
      6)) (some (10, 2, 6)) fan35Owner0Part3))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_1 : ExcludedOn (model35.B 1 ++ [step35.q]) 9000000000000 (model35.caps 1)
    (model35.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000, -9000000000000], [1980000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2880000000000], [1620000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5400000000000, -9000000000000], [4500000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([900000000000, -9000000000000], [1620000000000])
      (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1980000000000, 9000000000000]) (some (0, 1,
      1)) (some (3, 1, 1)) (.next ([-1980000000000, -9000000000000], [9000000000000, 0]) (some (3,
      1, 1)) (some (3, 1, 2)) (.next ([-1620000000000], [4500000000000]) (some (3, 1, 2)) (some (3,
      1, 2)) (.next ([-4500000000000, 0], [9900000000000, -9000000000000]) (some (3, 1, 2)) (some
      (3, 1, 2)) (.next ([-1620000000000, 0], [2520000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded35_4
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4950000000000], [2175000000000]) none none
      (.next ([3840000000000, 0], [1980000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2970000000000, -9000000000000], [2175000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1665000000000], [7125000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1980000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2175000000000],
      [7125000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1980000000000, -9000000000000],
      [5820000000000, 9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2175000000000, 0],
      [5145000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7125000000000],
      [8790000000000]) (some (3, 1, 0)) none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000, -9000000000000], [1980000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2970000000000, -9000000000000],
      [2175000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2175000000000],
      [1875000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([195000000000, -9000000000000],
      [3855000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1980000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1980000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-2175000000000, 0], [5145000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-1875000000000], [4050000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3855000000000, -9000000000000], [4050000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_3 : ExcludedOn (model36.B 3 ++ [step36.q]) 9000000000000 (model36.caps 3)
    (model36.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_4 : ExcludedOn (model36.B 4 ++ [step36.q]) 9000000000000 (model36.caps 4)
    (model36.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_7 : ExcludedOn (model36.B 7 ++ [step36.q]) 9000000000000 (model36.caps 7)
    (model36.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_8 : ExcludedOn (model36.B 8 ++ [step36.q]) 9000000000000 (model36.caps 8)
    (model36.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_9 : ExcludedOn (model36.B 9 ++ [step36.q]) 9000000000000 (model36.caps 9)
    (model36.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4770000000000], [2250000000000]) none none
      (.next ([3840000000000, 0], [1980000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2790000000000, -9000000000000], [2250000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1590000000000], [7020000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1980000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2250000000000],
      [7020000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1980000000000, -9000000000000],
      [5820000000000, 9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-2250000000000, 0],
      [5040000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-7020000000000],
      [8610000000000]) (some (3, 1, 0)) none (.terminal none none none))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_2 : ExcludedOn (model37.B 2 ++ [step37.q]) 9000000000000 (model37.caps 2)
    (model37.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7020000000000, -9000000000000], [1980000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2790000000000, -9000000000000],
      [2250000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2250000000000],
      [1980000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([270000000000, -9000000000000],
      [3960000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1980000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1980000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-2250000000000, 0], [5040000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-1980000000000], [4230000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3960000000000, -9000000000000], [4230000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded37_3 : ExcludedOn (model37.B 3 ++ [step37.q]) 9000000000000 (model37.caps 3)
    (model37.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_4 : ExcludedOn (model37.B 4 ++ [step37.q]) 9000000000000 (model37.caps 4)
    (model37.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_5 : ExcludedOn (model37.B 5 ++ [step37.q]) 9000000000000 (model37.caps 5)
    (model37.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_6 : ExcludedOn (model37.B 6 ++ [step37.q]) 9000000000000 (model37.caps 6)
    (model37.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_7 : ExcludedOn (model37.B 7 ++ [step37.q]) 9000000000000 (model37.caps 7)
    (model37.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_8 : ExcludedOn (model37.B 8 ++ [step37.q]) 9000000000000 (model37.caps 8)
    (model37.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded37_9 : ExcludedOn (model37.B 9 ++ [step37.q]) 9000000000000 (model37.caps 9)
    (model37.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded38_0 : ExcludedOn (model38.B 0 ++ [step38.q]) 9000000000000 (model38.caps 0)
    (model38.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_1 : ExcludedOn (model38.B 1 ++ [step38.q]) 9000000000000 (model38.caps 1)
    (model38.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_2 : ExcludedOn (model38.B 2 ++ [step38.q]) 9000000000000 (model38.caps 2)
    (model38.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_3 : ExcludedOn (model38.B 3 ++ [step38.q]) 9000000000000 (model38.caps 3)
    (model38.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6120000000000], [360000000000, 9000000000000])
      (some (2, 4, 1)) (some (4, 4, 1)) (.next ([1230000000000], [390000000000]) (some (4, 4, 1))
      (some (4, 4, 1)) (.next ([5730000000000], [1980000000000, 9000000000000]) (some (4, 4, 1))
      (some (4, 4, 2)) (.next ([1980000000000, 9000000000000], [900000000000, -9000000000000]) (some
      (4, 4, 2)) (some (4, 4, 2)) (.next ([1620000000000], [4500000000000]) (some (4, 0, 2)) (some
      (4, 0, 2)) (.next ([1620000000000], [7380000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([0], [1980000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([-360000000000, -9000000000000], [6480000000000, 9000000000000]) (some (4, 0, 2)) (some (4,
      0, 2)) (.next ([-390000000000], [1620000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next
      ([-1980000000000, -9000000000000], [7710000000000, 9000000000000]) (some (4, 1, 2)) (some (4,
      1, 2)) (.next ([-900000000000, 9000000000000], [2880000000000]) (some (4, 1, 2)) (some (4, 1,
      2)) (.next ([-4500000000000], [6120000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([-7380000000000], [9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.terminal (some (4, 1,
      2)) (some (4, 1, 2)) (some (4, 1, 2))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded38_4 : ExcludedOn (model38.B 4 ++ [step38.q]) 9000000000000 (model38.caps 4)
    (model38.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_5 : ExcludedOn (model38.B 5 ++ [step38.q]) 9000000000000 (model38.caps 5)
    (model38.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_6 : ExcludedOn (model38.B 6 ++ [step38.q]) 9000000000000 (model38.caps 6)
    (model38.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_7 : ExcludedOn (model38.B 7 ++ [step38.q]) 9000000000000 (model38.caps 7)
    (model38.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded38_9 : ExcludedOn (model38.B 9 ++ [step38.q]) 9000000000000 (model38.caps 9)
    (model38.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked38 : StepValid model38 9000000000000 step38 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded38_0
    · exact excluded38_1
    · exact excluded38_2
    · exact excluded38_3
    · exact excluded38_4
    · exact excluded38_5
    · exact excluded38_6
    · exact excluded38_7
    · exact (hj rfl).elim
    · exact excluded38_9
theorem next38 : model38.insert step38 = model39 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded39_0 : ExcludedOn (model39.B 0 ++ [step39.q]) 9000000000000 (model39.caps 0)
    (model39.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_1 : ExcludedOn (model39.B 1 ++ [step39.q]) 9000000000000 (model39.caps 1)
    (model39.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_2 : ExcludedOn (model39.B 2 ++ [step39.q]) 9000000000000 (model39.caps 2)
    (model39.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_3 : ExcludedOn (model39.B 3 ++ [step39.q]) 9000000000000 (model39.caps 3)
    (model39.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_4 : ExcludedOn (model39.B 4 ++ [step39.q]) 9000000000000 (model39.caps 4)
    (model39.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [75000000000]) (some (5, 0, 3))
      (some (5, 1, 3)) (.next ([2700000000000], [180000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([4335000000000], [540000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([3510000000000], [540000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4050000000000],
      [900000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4410000000000, 0], [1980000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([4050000000000], [2250000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) fan39Owner4Part0)))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded39_5 : ExcludedOn (model39.B 5 ++ [step39.q]) 9000000000000 (model39.caps 5)
    (model39.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_6 : ExcludedOn (model39.B 6 ++ [step39.q]) 9000000000000 (model39.caps 6)
    (model39.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_7 : ExcludedOn (model39.B 7 ++ [step39.q]) 9000000000000 (model39.caps 7)
    (model39.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded39_9 : ExcludedOn (model39.B 9 ++ [step39.q]) 9000000000000 (model39.caps 9)
    (model39.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked39 : StepValid model39 9000000000000 step39 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded39_0
    · exact excluded39_1
    · exact excluded39_2
    · exact excluded39_3
    · exact excluded39_4
    · exact excluded39_5
    · exact excluded39_6
    · exact excluded39_7
    · exact (hj rfl).elim
    · exact excluded39_9
theorem next39 : model39.insert step39 = model40 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint220000230000
end ConwaySoifer.Simplified.Certificates

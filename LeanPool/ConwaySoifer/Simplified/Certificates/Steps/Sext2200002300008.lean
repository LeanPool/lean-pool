/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext220000230000
import Mathlib.Tactic.FinCases

/-!
# Sext 220000 230000 8

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
namespace Sext220000230000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan64Owner3Part0 : FanWitness := (.next ([2520000000000], [1980000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([1365000000000], [1275000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([3915000000000], [4095000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next
    ([3345000000000], [3510000000000]) (some (4, 0, 1)) (some (4, 5, 1)) (.next ([1980000000000],
    [2235000000000]) (some (4, 5, 1)) (some (4, 5, 1)) (.next ([3345000000000, 9000000000000],
    [6030000000000, -9000000000000]) (some (4, 5, 1)) (some (4, 5, 2)) (.next ([1980000000000,
    9000000000000], [4755000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1980000000000, 9000000000000], [5460000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1275000000000], [5460000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([1365000000000],
    [8010000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 9000000000000], [2520000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [5460000000000]) (some (4, 5,
    2)) (some (4, 5, 3)) (.next ([-2940000000000], [7440000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-1980000000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1275000000000], [2640000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4095000000000],
    [8010000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3510000000000], [6855000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2235000000000], [4215000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-6030000000000, 9000000000000], [9375000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4755000000000, 9000000000000], [6735000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5460000000000, 0], [7440000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5460000000000], [6735000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-8010000000000], [9375000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2520000000000, 9000000000000], [2520000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan64Owner4Part0 : FanWitness := (.next ([5145000000000], [1980000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([3600000000000], [4035000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([2205000000000], [4410000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1980000000000, 9000000000000], [4410000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([1980000000000, 9000000000000], [4635000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([2355000000000, 9000000000000], [5655000000000, -9000000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([375000000000], [1020000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([510000000000], [1470000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([735000000000], [6390000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([375000000000],
    [7635000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [5145000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [4410000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-510000000000], [2865000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-1980000000000], [7125000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-4035000000000], [7635000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4410000000000],
    [6615000000000]) (some (0, 1, 3)) (some (0, 5, 3)) (.next ([-4410000000000], [6390000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4635000000000, 9000000000000],
    [6615000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5655000000000, 9000000000000],
    [8010000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1020000000000], [1395000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1470000000000], [1980000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-6390000000000], [7125000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-7635000000000], [8010000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-5145000000000, 9000000000000], [5145000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan64Owner5Part0 : FanWitness := (.next ([3000000000000], [4650000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([2625000000000], [4356000000000]) (some (5, 1, 2)) (some (5, 1, 2))
    (.next ([1080000000000], [1920000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([2199000000000], [6051000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1980000000000,
    9000000000000], [5730000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1605000000000,
    9000000000000], [5436000000000, 0]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1905000000000],
    [6720000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([930000000000], [5625000000000])
    (some (5, 1, 2)) (some (5, 1, 5)) (.next ([990000000000, 9000000000000], [6645000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([60000000000, 9000000000000],
    [1020000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 0],
    [1980000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-375000000000],
    [5436000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([-990000000000], [8625000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-294000000000], [669000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4650000000000], [7650000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4356000000000], [6981000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1920000000000], [3000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6051000000000],
    [8250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5730000000000, 0], [7710000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5436000000000, 0], [7041000000000,
    9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6720000000000], [8625000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5625000000000], [6555000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-6645000000000, 9000000000000], [7635000000000, 0]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-1020000000000, 9000000000000], [1080000000000, 0]) (some (0, 2, 5))
    (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan65Owner2Part0 : FanWitness := (.next ([3291000000000, 9000000000000], [2145000000000,
    -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([540000000000], [396000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([2355000000000, 9000000000000], [2685000000000,
    -9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next ([4314000000000], [5235000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([750000000000, 0], [1584000000000, -9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([1980000000000, 9000000000000], [5985000000000, 0])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1311000000000], [4125000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([750000000000], [3564000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([375000000000], [4665000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([189000000000], [4686000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0],
    [5985000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-351000000000], [4290000000000])
    (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-549000000000], [4674000000000]) (some (0, 2, 4))
    (some (0, 5, 4)) (.next ([-945000000000], [5610000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-2145000000000, 9000000000000], [5436000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-396000000000], [936000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-2685000000000, 9000000000000], [5040000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-5235000000000], [9549000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1584000000000,
    9000000000000], [2334000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-5985000000000, 0], [7965000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4125000000000], [5436000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3564000000000],
    [4314000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4665000000000], [5040000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4686000000000], [4875000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5, 0)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner0Part0 : FanWitness := (.next ([-5496000000000], [7935000000000]) (some (1, 6, 9))
    (some (1, 6, 9)) (.next ([-1500000000000], [2160000000000]) (some (1, 6, 9)) (some (1, 6, 9))
    (.next ([-1410000000000], [2025000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next
    ([-120000000000], [165000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-2259000000000],
    [3000000000000]) (some (1, 6, 9)) (some (1, 6, 10)) (.next ([-1455000000000], [1905000000000])
    (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-330000000000], [420000000000]) (some (1, 6, 10))
    (some (1, 6, 10)) (.next ([-1455000000000], [1824000000000]) (some (1, 6, 10)) (some (1, 6, 10))
    (.next ([-2400000000000], [3000000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-1590000000000], [1959000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-6375000000000], [7845000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-201000000000],
    [246000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-4875000000000], [5685000000000])
    (some (1, 6, 10)) (some (1, 6, 10)) (.next ([-5481000000000], [6246000000000]) (some (1, 6, 10))
    (some (1, 6, 10)) (.next ([-5571000000000], [6276000000000]) (some (1, 6, 10)) (some (1, 6, 10))
    (.next ([-5865000000000], [6480000000000]) (some (1, 6, 10)) (some (1, 6, 10)) (.next
    ([-5826000000000], [6246000000000]) (some (1, 6, 10)) (some (12, 6, 10)) (.next
    ([-6315000000000], [6660000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6405000000000], [6690000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6480000000000], [6705000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6570000000000], [6735000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-5916000000000], [6057000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6561000000000], [6705000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.next
    ([-6651000000000], [6735000000000]) (some (12, 6, 10)) (some (12, 6, 10)) (.terminal (some (12,
    6, 10)) (some (12, 6, 10)) (some (12, 6, 10)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner0Part1 : FanWitness := (.next ([-219000000000], [564000000000]) (some (0, 12, 8))
    (some (1, 12, 8)) (.next ([-996000000000], [2445000000000]) (some (1, 12, 8)) (some (1, 12, 8))
    (.next ([-330000000000], [765000000000]) (some (1, 12, 8)) (some (1, 12, 8)) (.next
    ([-1230000000000], [2640000000000]) (some (1, 12, 8)) (some (1, 12, 8)) (.next
    ([-1419000000000], [2919000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-420000000000],
    [834000000000]) (some (1, 5, 8)) (some (1, 5, 8)) (.next ([-1200000000000], [2355000000000])
    (some (1, 5, 8)) (some (1, 5, 9)) (.next ([-1560000000000], [3060000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-360000000000], [705000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-1230000000000], [2295000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-540000000000], [999000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-2916000000000],
    [5316000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-621000000000], [1080000000000])
    (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-4416000000000], [7476000000000]) (some (1, 5, 9))
    (some (1, 5, 9)) (.next ([-1635000000000], [2565000000000]) (some (1, 5, 9)) (some (1, 5, 9))
    (.next ([-1695000000000], [2655000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next
    ([-3750000000000], [5730000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-5250000000000],
    [7890000000000]) (some (1, 5, 9)) (some (1, 5, 9)) (.next ([-60000000000], [90000000000]) (some
    (1, 5, 9)) (some (1, 5, 9)) (.next ([-189000000000], [279000000000]) (some (1, 5, 9)) (some (1,
    5, 9)) (.next ([-3915000000000], [5775000000000]) (some (1, 5, 9)) (some (1, 6, 9)) (.next
    ([-1980000000000], [2910000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-5415000000000],
    [7935000000000]) (some (1, 6, 9)) (some (1, 6, 9)) (.next ([-3996000000000], [5775000000000])
    (some (1, 6, 9)) (some (1, 6, 9)) fan66Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner0Part2 : FanWitness := (.next ([-120000000000], [6825000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([-201000000000], [6906000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([-45000000000], [1170000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-279000000000], [6750000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-399000000000],
    [6915000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-420000000000], [6750000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-480000000000], [6996000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([-540000000000], [6915000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([-90000000000], [1050000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-621000000000], [6996000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-90000000000],
    [969000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-30000000000], [285000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-825000000000], [7440000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([-885000000000], [7530000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    (.next ([-1170000000000], [7785000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-1449000000000], [7875000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-1590000000000], [7875000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-1680000000000], [6930000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-1740000000000], [7020000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next
    ([-2025000000000], [7275000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-189000000000],
    [624000000000]) (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-2304000000000], [7365000000000])
    (some (0, 12, 8)) (some (0, 12, 8)) (.next ([-2445000000000], [7365000000000]) (some (0, 12, 8))
    (some (0, 12, 8)) (.next ([-510000000000], [1365000000000]) (some (0, 12, 8)) (some (0, 12, 8))
    fan66Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner0Part3 : FanWitness := (.next ([615000000000], [1410000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([45000000000], [120000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([741000000000], [2259000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([450000000000], [1455000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([90000000000],
    [330000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([369000000000], [1455000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([600000000000], [2400000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([369000000000], [1590000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([1470000000000], [6375000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([45000000000], [201000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([810000000000],
    [4875000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([765000000000], [5481000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([705000000000], [5571000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([615000000000], [5865000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([420000000000], [5826000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([345000000000], [6315000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([285000000000],
    [6405000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([225000000000], [6480000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([165000000000], [6570000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([141000000000], [5916000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([144000000000], [6561000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([84000000000], [6651000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([0],
    [345000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([-45000000000], [4365000000000])
    (some (0, 12, 7)) (some (0, 12, 8)) fan66Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner0Part4 : FanWitness := (.next ([435000000000], [330000000000]) (some (0, 12, 7)) (some
    (0, 12, 7)) (.next ([1410000000000], [1230000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([1500000000000], [1419000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([414000000000],
    [420000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([1155000000000], [1200000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([1500000000000], [1560000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([345000000000], [360000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([1065000000000], [1230000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([459000000000], [540000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([2400000000000],
    [2916000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([459000000000], [621000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([3060000000000], [4416000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([930000000000], [1635000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([960000000000], [1695000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([1980000000000], [3750000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([2640000000000],
    [5250000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([30000000000], [60000000000]) (some
    (0, 12, 7)) (some (0, 12, 7)) (.next ([90000000000], [189000000000]) (some (0, 12, 7)) (some (0,
    12, 7)) (.next ([1860000000000], [3915000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([930000000000], [1980000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([2520000000000],
    [5415000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([1779000000000], [3996000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([2439000000000], [5496000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([660000000000], [1500000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    fan66Owner0Part3))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan66Owner0Part5 : FanWitness := (.next ([1125000000000], [45000000000]) (some (11, 12, 7))
    (some (11, 12, 7)) (.next ([6471000000000], [279000000000]) (some (11, 12, 7)) (some (11, 12,
    7)) (.next ([6516000000000], [399000000000]) (some (11, 12, 7)) (some (11, 12, 7)) (.next
    ([6330000000000], [420000000000]) (some (11, 12, 7)) (some (11, 12, 7)) (.next ([6516000000000],
    [480000000000]) (some (11, 12, 7)) (some (11, 12, 7)) (.next ([6375000000000], [540000000000])
    (some (11, 12, 7)) (some (11, 12, 7)) (.next ([960000000000], [90000000000]) (some (11, 12, 7))
    (some (11, 12, 7)) (.next ([6375000000000], [621000000000]) (some (11, 12, 7)) (some (11, 12,
    7)) (.next ([879000000000], [90000000000]) (some (11, 12, 7)) (some (11, 12, 7)) (.next
    ([255000000000], [30000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([6615000000000],
    [825000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([6645000000000], [885000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([6615000000000], [1170000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([6426000000000], [1449000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([6285000000000], [1590000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([5250000000000], [1680000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([5280000000000],
    [1740000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([5250000000000], [2025000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) (.next ([435000000000], [189000000000]) (some (0, 12, 7))
    (some (0, 12, 7)) (.next ([5061000000000], [2304000000000]) (some (0, 12, 7)) (some (0, 12, 7))
    (.next ([4920000000000], [2445000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next
    ([855000000000], [510000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([345000000000],
    [219000000000]) (some (0, 12, 7)) (some (0, 12, 7)) (.next ([1449000000000], [996000000000])
    (some (0, 12, 7)) (some (0, 12, 7)) fan66Owner0Part4))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan67Owner5Part0 : FanWitness := (.next ([7995000000000, 9000000000000], [1005000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4875000000000], [2145000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([6015000000000], [2985000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([1290000000000], [855000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([1140000000000], [840000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3000000000000], [4650000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000],
    [1920000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1980000000000, 9000000000000],
    [5730000000000, 0]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([855000000000], [5940000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([285000000000], [2985000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([15000000000], [7920000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([0, 0], [1980000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-165000000000, 9000000000000], [7020000000000, 0]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-1005000000000, 9000000000000], [9000000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-2145000000000], [7020000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2985000000000],
    [9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-855000000000], [2145000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-840000000000], [1980000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4650000000000], [7650000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-1920000000000], [3000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-5730000000000, 0], [7710000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-5940000000000], [6795000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2985000000000],
    [3270000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7920000000000], [7935000000000])
    (some (0, 2, 5)) (some (0, 5, 5)) (.terminal (some (0, 5, 4)) (some (0, 5, 4)) (some (0, 5,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan69Owner4Part0 : FanWitness := (.next ([5280000000000], [1875000000000]) (some (4, 1, 2))
    (some (4, 1, 2)) (.next ([5175000000000], [1845000000000]) (some (4, 1, 2)) (some (4, 1, 2))
    (.next ([5145000000000], [1980000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([2205000000000], [4410000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1980000000000,
    9000000000000], [4410000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1980000000000,
    9000000000000], [4635000000000, -9000000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
    ([765000000000], [1845000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([510000000000],
    [1470000000000]) (some (4, 1, 2)) (some (4, 5, 2)) (.next ([735000000000], [6390000000000])
    (some (4, 5, 2)) (some (4, 5, 3)) (.next ([135000000000, 9000000000000], [7020000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([0, 9000000000000], [5145000000000, -9000000000000]) (some
    (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [4410000000000]) (some (4, 5, 3)) (some (4, 5, 3))
    (.next ([-405000000000], [5175000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-1875000000000], [7155000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1845000000000],
    [7020000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1980000000000], [7125000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4410000000000], [6615000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4410000000000], [6390000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4635000000000, 9000000000000], [6615000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-1845000000000], [2610000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-1470000000000], [1980000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-6390000000000], [7125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-7020000000000],
    [7155000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-5145000000000,
    9000000000000], [5145000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal (some (0, 5, 3))
    (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan69Owner5Part0 : FanWitness := (.next ([765000000000], [60000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([4875000000000], [2145000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([1290000000000], [855000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3825000000000],
    [3885000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next ([1845000000000], [1980000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3000000000000], [4650000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([1080000000000], [1920000000000]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([1980000000000, 9000000000000], [5730000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3))
    (.next ([1680000000000], [5175000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([855000000000], [5940000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 9000000000000],
    [1845000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0],
    [1980000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-165000000000,
    9000000000000], [7020000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-60000000000],
    [825000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2145000000000], [7020000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-855000000000], [2145000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-3885000000000], [7710000000000]) (some (0, 2, 3)) (some (0, 2, 3))
    (.next ([-1980000000000], [3825000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([-4650000000000], [7650000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-1920000000000],
    [3000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5730000000000, 0], [7710000000000,
    9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5175000000000], [6855000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5940000000000], [6795000000000]) (some (0, 2, 3))
    (some (0, 2, 5)) (.next ([-1845000000000, 9000000000000], [1845000000000, 0]) (some (0, 2, 5))
    (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

theorem excluded64_1 : ExcludedOn (model64.B 1 ++ [step64.q]) 9000000000000 (model64.caps 1)
    (model64.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_2 : ExcludedOn (model64.B 2 ++ [step64.q]) 9000000000000 (model64.caps 2)
    (model64.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_3 : ExcludedOn (model64.B 3 ++ [step64.q]) 9000000000000 (model64.caps 3)
    (model64.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [2940000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) fan64Owner3Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded64_4 : ExcludedOn (model64.B 4 ++ [step64.q]) 9000000000000 (model64.caps 4)
    (model64.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2355000000000], [510000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan64Owner4Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded64_5 : ExcludedOn (model64.B 5 ++ [step64.q]) 9000000000000 (model64.caps 5)
    (model64.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5061000000000], [375000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([7635000000000], [990000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([375000000000], [294000000000]) (some (5, 1, 2)) (some (5, 1, 2)) fan64Owner5Part0))))
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded64_6 : ExcludedOn (model64.B 6 ++ [step64.q]) 9000000000000 (model64.caps 6)
    (model64.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded64_7 : ExcludedOn (model64.B 7 ++ [step64.q]) 9000000000000 (model64.caps 7)
    (model64.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_2 : ExcludedOn (model65.B 2 ++ [step65.q]) 9000000000000 (model65.caps 2)
    (model65.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3939000000000], [351000000000]) (some (0, 0, 5))
      (some (0, 0, 5)) (.next ([4125000000000], [549000000000]) (some (0, 0, 5)) (some (0, 0, 5))
      (.next ([4665000000000], [945000000000]) (some (0, 0, 5)) (some (0, 1, 5))
      fan65Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded65_3 : ExcludedOn (model65.B 3 ++ [step65.q]) 9000000000000 (model65.caps 3)
    (model65.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded65_7 : ExcludedOn (model65.B 7 ++ [step65.q]) 9000000000000 (model65.caps 7)
    (model65.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5436000000000], [2334000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([5436000000000], [4314000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1980000000000, 9000000000000], [2970000000000, -9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([486000000000], [4314000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([0], [4950000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next
      ([-2334000000000, 9000000000000], [7770000000000, -9000000000000]) (some (3, 3, 2)) (some (3,
      3, 2)) (.next ([-4314000000000], [9750000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-2970000000000, 9000000000000], [4950000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4314000000000], [4800000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [45000000000]) (some (10, 12,
      6)) (some (11, 12, 7)) (.next ([6705000000000], [120000000000]) (some (11, 12, 7)) (some (11,
      12, 7)) (.next ([6705000000000], [201000000000]) (some (11, 12, 7)) (some (11, 12, 7))
      fan66Owner0Part5))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded66_1 : ExcludedOn (model66.B 1 ++ [step66.q]) 9000000000000 (model66.caps 1)
    (model66.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_2 : ExcludedOn (model66.B 2 ++ [step66.q]) 9000000000000 (model66.caps 2)
    (model66.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_3 : ExcludedOn (model66.B 3 ++ [step66.q]) 9000000000000 (model66.caps 3)
    (model66.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_4 : ExcludedOn (model66.B 4 ++ [step66.q]) 9000000000000 (model66.caps 4)
    (model66.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_6 : ExcludedOn (model66.B 6 ++ [step66.q]) 9000000000000 (model66.caps 6)
    (model66.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2145000000000], [1980000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([4125000000000], [4875000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([1980000000000, 9000000000000], [7020000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 9000000000000], [2145000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1980000000000, 9000000000000]) (some (3, 0,
      2)) (some (3, 0, 2)) (.next ([-1980000000000], [4125000000000]) (some (3, 0, 2)) (some (3, 1,
      2)) (.next ([-4875000000000, 9000000000000], [9000000000000, -9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-7020000000000, 9000000000000], [9000000000000, 0]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-2145000000000, 9000000000000], [2145000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded66_7 : ExcludedOn (model66.B 7 ++ [step66.q]) 9000000000000 (model66.caps 7)
    (model66.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_8 : ExcludedOn (model66.B 8 ++ [step66.q]) 9000000000000 (model66.caps 8)
    (model66.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded66_9 : ExcludedOn (model66.B 9 ++ [step66.q]) 9000000000000 (model66.caps 9)
    (model66.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded66_1
    · exact excluded66_2
    · exact excluded66_3
    · exact excluded66_4
    · exact (hj rfl).elim
    · exact excluded66_6
    · exact excluded66_7
    · exact excluded66_8
    · exact excluded66_9
theorem next66 : model66.insert step66 = model67 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded67_1 : ExcludedOn (model67.B 1 ++ [step67.q]) 9000000000000 (model67.caps 1)
    (model67.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_2 : ExcludedOn (model67.B 2 ++ [step67.q]) 9000000000000 (model67.caps 2)
    (model67.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_3 : ExcludedOn (model67.B 3 ++ [step67.q]) 9000000000000 (model67.caps 3)
    (model67.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_4 : ExcludedOn (model67.B 4 ++ [step67.q]) 9000000000000 (model67.caps 4)
    (model67.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded67_5 : ExcludedOn (model67.B 5 ++ [step67.q]) 9000000000000 (model67.caps 5)
    (model67.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6855000000000, 9000000000000], [165000000000,
      -9000000000000]) (some (4, 0, 5)) (some (4, 1, 5)) fan67Owner5Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded67_6 : ExcludedOn (model67.B 6 ++ [step67.q]) 9000000000000 (model67.caps 6)
    (model67.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1980000000000, 9000000000000], [1005000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2985000000000], [4035000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1980000000000, 9000000000000],
      [7020000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0],
      [1980000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1005000000000,
      9000000000000], [2985000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-4035000000000,
      9000000000000], [7020000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-7020000000000, 9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2))
      (.terminal (some (0, 1, 2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded67_7 : ExcludedOn (model67.B 7 ++ [step67.q]) 9000000000000 (model67.caps 7)
    (model67.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded67_1
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

theorem excluded68_1 : ExcludedOn (model68.B 1 ++ [step68.q]) 9000000000000 (model68.caps 1)
    (model68.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4686000000000], [750000000000]) (some (0, 4, 1))
      (some (0, 4, 2)) (.next ([2706000000000, -9000000000000], [750000000000, 0]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([6375000000000], [3261000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.next ([1980000000000, 9000000000000], [1980000000000, 9000000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([2175000000000], [2970000000000, -9000000000000]) (some (0, 4, 2)) (some
      (0, 4, 2)) (.next ([2175000000000], [4950000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1230000000000, 9000000000000], [5436000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([195000000000, -9000000000000], [6930000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([0], [1980000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-750000000000], [5436000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([-750000000000,
      0], [3456000000000, -9000000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-3261000000000], [9636000000000]) (some (0, 4, 0)) none (.next ([-1980000000000,
      -9000000000000], [3960000000000, 18000000000000]) none none (.next ([-2970000000000,
      9000000000000], [5145000000000, -9000000000000]) (some (4, 4, 0)) (some (4, 4, 0)) (.next
      ([-4950000000000], [7125000000000]) (some (4, 1, 0)) (some (4, 1, 0)) (.next
      ([-5436000000000], [6666000000000, 9000000000000]) (some (4, 1, 0)) (some (4, 1, 0)) (.next
      ([-6930000000000, -9000000000000], [7125000000000, 0]) (some (4, 1, 0)) (some (4, 1, 0))
      (.terminal (some (4, 1, 0)) (some (4, 1, 0)) (some (4, 1, 0))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded68_2 : ExcludedOn (model68.B 2 ++ [step68.q]) 9000000000000 (model68.caps 2)
    (model68.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_3 : ExcludedOn (model68.B 3 ++ [step68.q]) 9000000000000 (model68.caps 3)
    (model68.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_4 : ExcludedOn (model68.B 4 ++ [step68.q]) 9000000000000 (model68.caps 4)
    (model68.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_5 : ExcludedOn (model68.B 5 ++ [step68.q]) 9000000000000 (model68.caps 5)
    (model68.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_6 : ExcludedOn (model68.B 6 ++ [step68.q]) 9000000000000 (model68.caps 6)
    (model68.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3855000000000, 9000000000000], [195000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([1875000000000], [2175000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2175000000000], [2970000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1980000000000, 9000000000000], [7020000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [1980000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-195000000000, 9000000000000],
      [4050000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2175000000000], [4050000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2970000000000, 9000000000000], [5145000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-7020000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_7 : ExcludedOn (model68.B 7 ++ [step68.q]) 9000000000000 (model68.caps 7)
    (model68.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_8 : ExcludedOn (model68.B 8 ++ [step68.q]) 9000000000000 (model68.caps 8)
    (model68.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded68_9 : ExcludedOn (model68.B 9 ++ [step68.q]) 9000000000000 (model68.caps 9)
    (model68.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked68 : StepValid model68 9000000000000 step68 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded68_1
    · exact excluded68_2
    · exact excluded68_3
    · exact excluded68_4
    · exact excluded68_5
    · exact excluded68_6
    · exact excluded68_7
    · exact excluded68_8
    · exact excluded68_9
theorem next68 : model68.insert step68 = model69 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded69_1 : ExcludedOn (model69.B 1 ++ [step69.q]) 9000000000000 (model69.caps 1)
    (model69.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_2 : ExcludedOn (model69.B 2 ++ [step69.q]) 9000000000000 (model69.caps 2)
    (model69.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_3 : ExcludedOn (model69.B 3 ++ [step69.q]) 9000000000000 (model69.caps 3)
    (model69.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_4 : ExcludedOn (model69.B 4 ++ [step69.q]) 9000000000000 (model69.caps 4)
    (model69.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4770000000000], [405000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan69Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded69_5 : ExcludedOn (model69.B 5 ++ [step69.q]) 9000000000000 (model69.caps 5)
    (model69.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6855000000000, 9000000000000], [165000000000,
      -9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan69Owner5Part0)) (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded69_6 : ExcludedOn (model69.B 6 ++ [step69.q]) 9000000000000 (model69.caps 6)
    (model69.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_7 : ExcludedOn (model69.B 7 ++ [step69.q]) 9000000000000 (model69.caps 7)
    (model69.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_8 : ExcludedOn (model69.B 8 ++ [step69.q]) 9000000000000 (model69.caps 8)
    (model69.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded69_9 : ExcludedOn (model69.B 9 ++ [step69.q]) 9000000000000 (model69.caps 9)
    (model69.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked69 : StepValid model69 9000000000000 step69 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded69_1
    · exact excluded69_2
    · exact excluded69_3
    · exact excluded69_4
    · exact excluded69_5
    · exact excluded69_6
    · exact excluded69_7
    · exact excluded69_8
    · exact excluded69_9
theorem next69 : model69.insert step69 = model70 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext220000230000
end ConwaySoifer.Simplified.Certificates

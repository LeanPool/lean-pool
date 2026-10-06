/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext220000230000
import Mathlib.Tactic.FinCases

/-!
# Sext 220000 230000 7

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
def fan57Owner4Part0 : FanWitness := (.next ([2814000000000], [6615000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([834000000000, -9000000000000], [1980000000000, 9000000000000]) (some
    (6, 1, 2)) (some (6, 1, 2)) (.next ([2064000000000], [6360000000000]) (some (6, 1, 2)) (some (6,
    1, 2)) (.next ([1230000000000, 9000000000000], [4380000000000, -9000000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([1200000000000], [5160000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([834000000000], [4605000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([0,
    9000000000000], [2625000000000, -9000000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([0],
    [4410000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([-750000000000], [6360000000000])
    (some (6, 1, 2)) (some (6, 1, 2)) (.next ([-255000000000], [1005000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([-1785000000000], [6390000000000]) (some (6, 1, 2)) (some (6, 1, 3))
    (.next ([-1980000000000], [4605000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([-2010000000000], [3990000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-1755000000000],
    [2985000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-4410000000000], [6615000000000])
    (some (6, 1, 3)) (some (6, 1, 4)) (.next ([-4410000000000], [6390000000000, 9000000000000])
    (some (6, 1, 4)) (some (6, 2, 4)) (.next ([-4635000000000, 9000000000000], [6615000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-6615000000000], [9429000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-1980000000000, -9000000000000], [2814000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-6360000000000], [8424000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-4380000000000, 9000000000000], [5610000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-5160000000000], [6360000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-4605000000000], [5439000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-2625000000000,
    9000000000000], [2625000000000]) (some (6, 2, 4)) (some (6, 2, 6)) (.terminal (some (6, 2, 6))
    (some (0, 2, 6)) (some (6, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan58Owner3Part0 : FanWitness := (.next ([3120000000000, 9000000000000], [1500000000000]) (some
    (4, 0, 1)) (some (4, 0, 1)) (.next ([5235000000000], [2640000000000]) (some (4, 0, 1)) (some (4,
    0, 1)) (.next ([4125000000000], [3000000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next
    ([2145000000000], [1980000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([1140000000000],
    [1500000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([1980000000000], [2610000000000])
    (some (4, 0, 1)) (some (5, 0, 1)) (.next ([1980000000000, 9000000000000], [4755000000000,
    -9000000000000]) (some (5, 0, 1)) (some (5, 0, 2)) (.next ([1980000000000, 9000000000000],
    [5145000000000]) (some (5, 0, 2)) (some (5, 0, 2)) (.next ([1590000000000], [5145000000000])
    (some (5, 0, 2)) (some (5, 0, 2)) (.next ([645000000000], [4620000000000]) (some (5, 0, 2))
    (some (5, 1, 2)) (.next ([0, 9000000000000], [2145000000000, -9000000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([0], [5145000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
    ([-1140000000000], [3645000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-1500000000000,
    0], [4620000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2640000000000],
    [7875000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3000000000000], [7125000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1980000000000], [4125000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-1500000000000], [2640000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-2610000000000], [4590000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-4755000000000, 9000000000000], [6735000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-5145000000000, 0], [7125000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-5145000000000], [6735000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4620000000000],
    [5265000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2145000000000, 9000000000000],
    [2145000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3)) (some (0, 1, 3))
    (some (0, 1, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan59Owner4Part0 : FanWitness := (.next ([1230000000000], [1755000000000]) (some (6, 1, 2))
    (some (6, 1, 2)) (.next ([2205000000000], [4410000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([1980000000000, 9000000000000], [4410000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([1980000000000, 9000000000000], [4635000000000, -9000000000000]) (some (6, 1, 2)) (some
    (6, 1, 2)) (.next ([1230000000000, 9000000000000], [4380000000000, -9000000000000]) (some (6, 1,
    2)) (some (6, 1, 2)) (.next ([1200000000000], [5160000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([0, 9000000000000], [2625000000000, -9000000000000]) (some (6, 1, 2)) (some (6, 1, 2))
    (.next ([0], [4410000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([-750000000000],
    [6360000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-255000000000], [1005000000000])
    (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1785000000000], [6390000000000]) (some (0, 1, 2))
    (some (0, 1, 3)) (.next ([-1065000000000], [2625000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-1980000000000], [4605000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
    ([-3075000000000], [6615000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2820000000000],
    [5610000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2010000000000], [3990000000000])
    (some (0, 1, 3)) (some (0, 1, 6)) (.next ([-4410000000000], [7950000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-1755000000000], [2985000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-4410000000000], [6615000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-4410000000000], [6390000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next
    ([-4635000000000, 9000000000000], [6615000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-4380000000000, 9000000000000], [5610000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-5160000000000], [6360000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2625000000000,
    9000000000000], [2625000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal (some (0, 2, 6))
    (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan61Owner2Part0 : FanWitness := (.next ([4500000000000], [2520000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([3291000000000, 9000000000000], [2145000000000, -9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([540000000000], [396000000000]) (some (0, 5, 3)) (some (0,
    5, 3)) (.next ([2145000000000], [1980000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1605000000000], [1584000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([2355000000000,
    9000000000000], [2685000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
    ([1035000000000], [1485000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1980000000000,
    9000000000000], [5985000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([1311000000000],
    [4125000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([375000000000], [4665000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0], [5985000000000]) (some (0, 2, 3)) (some (0, 2,
    3)) (.next ([-540000000000, 9000000000000], [7020000000000, 0]) (some (0, 2, 3)) (some (0, 2,
    4)) (.next ([-549000000000], [4674000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-945000000000], [5610000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2520000000000],
    [7020000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2145000000000, 9000000000000],
    [5436000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-396000000000], [936000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1980000000000], [4125000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-1584000000000], [3189000000000]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-2685000000000, 9000000000000], [5040000000000, 0]) (some (0, 2, 4)) (some (0, 2, 4))
    (.next ([-1485000000000], [2520000000000]) (some (0, 2, 4)) (some (0, 3, 4)) (.next
    ([-5985000000000, 0], [7965000000000, 9000000000000]) (some (0, 3, 4)) (some (5, 3, 4)) (.next
    ([-4125000000000], [5436000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4665000000000],
    [5040000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0))
    (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner2Part0 : FanWitness := (.next ([4665000000000], [945000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([3291000000000, 9000000000000], [2145000000000, -9000000000000]) (some (0, 5,
    3)) (some (0, 5, 3)) (.next ([540000000000], [396000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([2355000000000, 9000000000000], [2685000000000, -9000000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([3525000000000], [4485000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([3480000000000, 9000000000000], [6030000000000, -9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1980000000000, 9000000000000], [5985000000000, 0]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1311000000000], [4125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([1500000000000], [8010000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([375000000000],
    [4665000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([189000000000], [3885000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0], [5985000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-549000000000], [4674000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next
    ([-945000000000], [5610000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2145000000000,
    9000000000000], [5436000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-396000000000],
    [936000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2685000000000, 9000000000000],
    [5040000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-4485000000000], [8010000000000])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6030000000000, 9000000000000], [9510000000000, 0])
    (some (0, 5, 4)) (some (5, 5, 4)) (.next ([-5985000000000, 0], [7965000000000, 9000000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4125000000000], [5436000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-8010000000000], [9510000000000]) (some (5, 3, 4)) (some (5, 3, 4))
    (.next ([-4665000000000], [5040000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
    ([-3885000000000], [4074000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some (5, 3,
    4)) (some (5, 3, 0)) (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner3Part0 : FanWitness := (.next ([2520000000000], [1980000000000]) (some (4, 0, 5))
    (some (4, 0, 5)) (.next ([1980000000000], [2235000000000]) (some (4, 0, 5)) (some (4, 0, 5))
    (.next ([2490000000000], [3000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([510000000000], [765000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2550000000000],
    [4950000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2490000000000, 9000000000000],
    [5520000000000, -9000000000000]) (some (4, 0, 2)) (some (4, 5, 2)) (.next ([1980000000000,
    9000000000000], [4755000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1980000000000, 9000000000000], [5460000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next
    ([1275000000000], [5460000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([510000000000],
    [7500000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0, 9000000000000], [2520000000000,
    -9000000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([0], [5460000000000]) (some (4, 5,
    2)) (some (4, 5, 3)) (.next ([-2940000000000], [7440000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([-1980000000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2235000000000], [4215000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3000000000000],
    [5490000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-765000000000], [1275000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4950000000000], [7500000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5520000000000, 9000000000000], [8010000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4755000000000, 9000000000000], [6735000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5460000000000, 0], [7440000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-5460000000000], [6735000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-7500000000000], [8010000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-2520000000000, 9000000000000], [2520000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 3)) (some (0, 5, 3)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan63Owner4Part0 : FanWitness := (.next ([5145000000000], [1980000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([885000000000], [990000000000]) (some (4, 1, 5)) (some (4, 1, 5))
    (.next ([990000000000], [1365000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3090000000000], [5400000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2205000000000],
    [4410000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1980000000000, 9000000000000],
    [4410000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1980000000000, 9000000000000],
    [4635000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([510000000000],
    [1470000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([990000000000, 9000000000000],
    [6510000000000, -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([735000000000],
    [6390000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0, 9000000000000], [5145000000000,
    -9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([0], [4410000000000]) (some (4, 1,
    5)) (some (4, 1, 5)) (.next ([-990000000000], [8490000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-1980000000000], [7125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-990000000000], [1875000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-1365000000000],
    [2355000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5400000000000], [8490000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-4410000000000], [6615000000000]) (some (0, 1, 3))
    (some (0, 5, 3)) (.next ([-4410000000000], [6390000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-4635000000000, 9000000000000], [6615000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([-1470000000000], [1980000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-6510000000000, 9000000000000], [7500000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([-6390000000000], [7125000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-5145000000000, 9000000000000], [5145000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.terminal
    (some (0, 5, 3)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

theorem excluded56_0 : ExcludedOn (model56.B 0 ++ [step56.q]) 9000000000000 (model56.caps 0)
    (model56.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 15) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_1 : ExcludedOn (model56.B 1 ++ [step56.q]) 9000000000000 (model56.caps 1)
    (model56.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_2 : ExcludedOn (model56.B 2 ++ [step56.q]) 9000000000000 (model56.caps 2)
    (model56.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_3 : ExcludedOn (model56.B 3 ++ [step56.q]) 9000000000000 (model56.caps 3)
    (model56.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_4 : ExcludedOn (model56.B 4 ++ [step56.q]) 9000000000000 (model56.caps 4)
    (model56.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_5 : ExcludedOn (model56.B 5 ++ [step56.q]) 9000000000000 (model56.caps 5)
    (model56.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_6 : ExcludedOn (model56.B 6 ++ [step56.q]) 9000000000000 (model56.caps 6)
    (model56.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_8 : ExcludedOn (model56.B 8 ++ [step56.q]) 9000000000000 (model56.caps 8)
    (model56.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_9 : ExcludedOn (model56.B 9 ++ [step56.q]) 9000000000000 (model56.caps 9)
    (model56.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked56 : StepValid model56 9000000000000 step56 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded56_0
    · exact excluded56_1
    · exact excluded56_2
    · exact excluded56_3
    · exact excluded56_4
    · exact excluded56_5
    · exact excluded56_6
    · exact (hj rfl).elim
    · exact excluded56_8
    · exact excluded56_9
theorem next56 : model56.insert step56 = model57 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded57_0 : ExcludedOn (model57.B 0 ++ [step57.q]) 9000000000000 (model57.caps 0)
    (model57.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 15) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_1 : ExcludedOn (model57.B 1 ++ [step57.q]) 9000000000000 (model57.caps 1)
    (model57.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_2 : ExcludedOn (model57.B 2 ++ [step57.q]) 9000000000000 (model57.caps 2)
    (model57.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_3 : ExcludedOn (model57.B 3 ++ [step57.q]) 9000000000000 (model57.caps 3)
    (model57.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_4 : ExcludedOn (model57.B 4 ++ [step57.q]) 9000000000000 (model57.caps 4)
    (model57.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5610000000000], [750000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([750000000000], [255000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([4605000000000], [1785000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([2625000000000], [1980000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([1980000000000],
      [2010000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([1230000000000], [1755000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2205000000000], [4410000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([1980000000000, 9000000000000], [4410000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([1980000000000, 9000000000000], [4635000000000, -9000000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) fan57Owner4Part0)))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded57_5 : ExcludedOn (model57.B 5 ++ [step57.q]) 9000000000000 (model57.caps 5)
    (model57.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_6 : ExcludedOn (model57.B 6 ++ [step57.q]) 9000000000000 (model57.caps 6)
    (model57.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_7 : ExcludedOn (model57.B 7 ++ [step57.q]) 9000000000000 (model57.caps 7)
    (model57.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_9 : ExcludedOn (model57.B 9 ++ [step57.q]) 9000000000000 (model57.caps 9)
    (model57.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked57 : StepValid model57 9000000000000 step57 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded57_0
    · exact excluded57_1
    · exact excluded57_2
    · exact excluded57_3
    · exact excluded57_4
    · exact excluded57_5
    · exact excluded57_6
    · exact excluded57_7
    · exact (hj rfl).elim
    · exact excluded57_9
theorem next57 : model57.insert step57 = model58 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded58_0 : ExcludedOn (model58.B 0 ++ [step58.q]) 9000000000000 (model58.caps 0)
    (model58.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 15) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_1 : ExcludedOn (model58.B 1 ++ [step58.q]) 9000000000000 (model58.caps 1)
    (model58.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_2 : ExcludedOn (model58.B 2 ++ [step58.q]) 9000000000000 (model58.caps 2)
    (model58.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_3 : ExcludedOn (model58.B 3 ++ [step58.q]) 9000000000000 (model58.caps 3)
    (model58.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2505000000000], [1140000000000]) (some (3, 0,
      1)) (some (4, 0, 1)) fan58Owner3Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded58_4 : ExcludedOn (model58.B 4 ++ [step58.q]) 9000000000000 (model58.caps 4)
    (model58.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_5 : ExcludedOn (model58.B 5 ++ [step58.q]) 9000000000000 (model58.caps 5)
    (model58.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_6 : ExcludedOn (model58.B 6 ++ [step58.q]) 9000000000000 (model58.caps 6)
    (model58.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_7 : ExcludedOn (model58.B 7 ++ [step58.q]) 9000000000000 (model58.caps 7)
    (model58.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded58_9 : ExcludedOn (model58.B 9 ++ [step58.q]) 9000000000000 (model58.caps 9)
    (model58.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked58 : StepValid model58 9000000000000 step58 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded58_0
    · exact excluded58_1
    · exact excluded58_2
    · exact excluded58_3
    · exact excluded58_4
    · exact excluded58_5
    · exact excluded58_6
    · exact excluded58_7
    · exact (hj rfl).elim
    · exact excluded58_9
theorem next58 : model58.insert step58 = model59 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded59_0 : ExcludedOn (model59.B 0 ++ [step59.q]) 9000000000000 (model59.caps 0)
    (model59.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 15) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_1 : ExcludedOn (model59.B 1 ++ [step59.q]) 9000000000000 (model59.caps 1)
    (model59.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_2 : ExcludedOn (model59.B 2 ++ [step59.q]) 9000000000000 (model59.caps 2)
    (model59.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_4 : ExcludedOn (model59.B 4 ++ [step59.q]) 9000000000000 (model59.caps 4)
    (model59.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5610000000000], [750000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([750000000000], [255000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([4605000000000], [1785000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([1560000000000], [1065000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2625000000000],
      [1980000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([3540000000000], [3075000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([2790000000000], [2820000000000]) (some (6, 1, 2))
      (some (6, 1, 2)) (.next ([1980000000000], [2010000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([3540000000000], [4410000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      fan59Owner4Part0)))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded59_5 : ExcludedOn (model59.B 5 ++ [step59.q]) 9000000000000 (model59.caps 5)
    (model59.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_6 : ExcludedOn (model59.B 6 ++ [step59.q]) 9000000000000 (model59.caps 6)
    (model59.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_7 : ExcludedOn (model59.B 7 ++ [step59.q]) 9000000000000 (model59.caps 7)
    (model59.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded59_8 : ExcludedOn (model59.B 8 ++ [step59.q]) 9000000000000 (model59.caps 8)
    (model59.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2814000000000], [726000000000]) (some (0, 0, 4))
      (some (0, 1, 4)) (.next ([2820000000000], [1140000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([3345000000000], [2115000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([5460000000000], [3540000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([525000000000],
      [975000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1674000000000], [4686000000000])
      (some (0, 1, 2)) (some (0, 1, 3)) (.next ([1500000000000], [6360000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([699000000000], [6186000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([0], [6186000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-726000000000],
      [3540000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1140000000000], [3960000000000])
      (some (0, 1, 3)) (some (0, 4, 3)) (.next ([-2115000000000], [5460000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([-3540000000000], [9000000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([-975000000000], [1500000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-4686000000000], [6360000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-6360000000000], [7860000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.next
      ([-6186000000000], [6885000000000]) (some (0, 4, 3)) (some (0, 4, 3)) (.terminal (some (0, 4,
      3)) (some (0, 4, 0)) (some (0, 4, 3))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded59_9 : ExcludedOn (model59.B 9 ++ [step59.q]) 9000000000000 (model59.caps 9)
    (model59.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked59 : StepValid model59 9000000000000 step59 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded59_0
    · exact excluded59_1
    · exact excluded59_2
    · exact (hj rfl).elim
    · exact excluded59_4
    · exact excluded59_5
    · exact excluded59_6
    · exact excluded59_7
    · exact excluded59_8
    · exact excluded59_9
theorem next59 : model59.insert step59 = model60 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded60_0 : ExcludedOn (model60.B 0 ++ [step60.q]) 9000000000000 (model60.caps 0)
    (model60.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 15) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_1 : ExcludedOn (model60.B 1 ++ [step60.q]) 9000000000000 (model60.caps 1)
    (model60.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_3 : ExcludedOn (model60.B 3 ++ [step60.q]) 9000000000000 (model60.caps 3)
    (model60.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [3315000000000]) (some (3, 0,
      1)) (some (4, 0, 1)) (.next ([2145000000000], [1980000000000]) (some (4, 0, 1)) (some (4, 0,
      1)) (.next ([1035000000000], [1110000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next
      ([3015000000000], [3720000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([1980000000000],
      [2610000000000]) (some (4, 0, 1)) (some (4, 0, 5)) (.next ([3015000000000], [5460000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1980000000000, 9000000000000], [4755000000000,
      -9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1980000000000, 9000000000000],
      [5460000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next ([1275000000000], [5460000000000])
      (some (4, 0, 5)) (some (4, 0, 5)) (.next ([0, 9000000000000], [2145000000000, -9000000000000])
      (some (4, 0, 5)) (some (4, 1, 5)) (.next ([0], [5460000000000]) (some (4, 1, 5)) (some (4, 1,
      5)) (.next ([-3315000000000], [7440000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1980000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-1110000000000], [2145000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-3720000000000], [6735000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-2610000000000], [4590000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-5460000000000], [8475000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-4755000000000,
      9000000000000], [6735000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-5460000000000,
      0], [7440000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([-5460000000000], [6735000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-2145000000000,
      9000000000000], [2145000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.terminal (some (0, 1, 5))
      (some (0, 1, 3)) (some (0, 1, 5))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded60_4 : ExcludedOn (model60.B 4 ++ [step60.q]) 9000000000000 (model60.caps 4)
    (model60.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_5 : ExcludedOn (model60.B 5 ++ [step60.q]) 9000000000000 (model60.caps 5)
    (model60.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_6 : ExcludedOn (model60.B 6 ++ [step60.q]) 9000000000000 (model60.caps 6)
    (model60.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_7 : ExcludedOn (model60.B 7 ++ [step60.q]) 9000000000000 (model60.caps 7)
    (model60.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_8 : ExcludedOn (model60.B 8 ++ [step60.q]) 9000000000000 (model60.caps 8)
    (model60.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded60_9 : ExcludedOn (model60.B 9 ++ [step60.q]) 9000000000000 (model60.caps 9)
    (model60.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked60 : StepValid model60 9000000000000 step60 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded60_0
    · exact excluded60_1
    · exact (hj rfl).elim
    · exact excluded60_3
    · exact excluded60_4
    · exact excluded60_5
    · exact excluded60_6
    · exact excluded60_7
    · exact excluded60_8
    · exact excluded60_9
theorem next60 : model60.insert step60 = model61 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded61_0 : ExcludedOn (model61.B 0 ++ [step61.q]) 9000000000000 (model61.caps 0)
    (model61.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 15) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_1 : ExcludedOn (model61.B 1 ++ [step61.q]) 9000000000000 (model61.caps 1)
    (model61.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_2 : ExcludedOn (model61.B 2 ++ [step61.q]) 9000000000000 (model61.caps 2)
    (model61.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6480000000000, 9000000000000], [540000000000,
      -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4125000000000], [549000000000])
      (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4665000000000], [945000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan61Owner2Part0)))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded61_4 : ExcludedOn (model61.B 4 ++ [step61.q]) 9000000000000 (model61.caps 4)
    (model61.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_5 : ExcludedOn (model61.B 5 ++ [step61.q]) 9000000000000 (model61.caps 5)
    (model61.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_6 : ExcludedOn (model61.B 6 ++ [step61.q]) 9000000000000 (model61.caps 6)
    (model61.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_7 : ExcludedOn (model61.B 7 ++ [step61.q]) 9000000000000 (model61.caps 7)
    (model61.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_8 : ExcludedOn (model61.B 8 ++ [step61.q]) 9000000000000 (model61.caps 8)
    (model61.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded61_9 : ExcludedOn (model61.B 9 ++ [step61.q]) 9000000000000 (model61.caps 9)
    (model61.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked61 : StepValid model61 9000000000000 step61 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded61_0
    · exact excluded61_1
    · exact excluded61_2
    · exact (hj rfl).elim
    · exact excluded61_4
    · exact excluded61_5
    · exact excluded61_6
    · exact excluded61_7
    · exact excluded61_8
    · exact excluded61_9
theorem next61 : model61.insert step61 = model62 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded62_0 : ExcludedOn (model62.B 0 ++ [step62.q]) 9000000000000 (model62.caps 0)
    (model62.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 15) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_1 : ExcludedOn (model62.B 1 ++ [step62.q]) 9000000000000 (model62.caps 1)
    (model62.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_2 : ExcludedOn (model62.B 2 ++ [step62.q]) 9000000000000 (model62.caps 2)
    (model62.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_3 : ExcludedOn (model62.B 3 ++ [step62.q]) 9000000000000 (model62.caps 3)
    (model62.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3855000000000], [645000000000]) (some (3, 0, 1))
      (some (4, 0, 1)) (.next ([1590000000000], [285000000000]) (some (4, 0, 1)) (some (4, 0, 1))
      (.next ([4500000000000], [2940000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next
      ([2520000000000], [1980000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([1980000000000],
      [2235000000000]) (some (4, 0, 1)) (some (4, 0, 1)) (.next ([1560000000000], [3585000000000])
      (some (4, 0, 1)) (some (4, 0, 2)) (.next ([1980000000000, 9000000000000], [5460000000000])
      (some (4, 0, 2)) (some (4, 5, 2)) (.next ([1275000000000], [5460000000000]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([0, 9000000000000], [2520000000000, -9000000000000]) (some (4, 5, 2))
      (some (4, 5, 2)) (.next ([0], [5460000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next
      ([-645000000000], [4500000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-285000000000],
      [1875000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-2940000000000], [7440000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1980000000000], [4500000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-2235000000000], [4215000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-3585000000000], [5145000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5460000000000, 0], [7440000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-5460000000000], [6735000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2520000000000,
      9000000000000], [2520000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some (0, 1, 3))
      (some (0, 1, 3)) (some (0, 1, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded62_5 : ExcludedOn (model62.B 5 ++ [step62.q]) 9000000000000 (model62.caps 5)
    (model62.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_6 : ExcludedOn (model62.B 6 ++ [step62.q]) 9000000000000 (model62.caps 6)
    (model62.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_7 : ExcludedOn (model62.B 7 ++ [step62.q]) 9000000000000 (model62.caps 7)
    (model62.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_8 : ExcludedOn (model62.B 8 ++ [step62.q]) 9000000000000 (model62.caps 8)
    (model62.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded62_9 : ExcludedOn (model62.B 9 ++ [step62.q]) 9000000000000 (model62.caps 9)
    (model62.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked62 : StepValid model62 9000000000000 step62 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded62_0
    · exact excluded62_1
    · exact excluded62_2
    · exact excluded62_3
    · exact (hj rfl).elim
    · exact excluded62_5
    · exact excluded62_6
    · exact excluded62_7
    · exact excluded62_8
    · exact excluded62_9
theorem next62 : model62.insert step62 = model63 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded63_1 : ExcludedOn (model63.B 1 ++ [step63.q]) 9000000000000 (model63.caps 1)
    (model63.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_2 : ExcludedOn (model63.B 2 ++ [step63.q]) 9000000000000 (model63.caps 2)
    (model63.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [549000000000]) (some (0, 5, 3))
      (some (0, 5, 3)) fan63Owner2Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_3 : ExcludedOn (model63.B 3 ++ [step63.q]) 9000000000000 (model63.caps 3)
    (model63.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4500000000000], [2940000000000]) (some (3, 0,
      5)) (some (4, 0, 5)) fan63Owner3Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_4 : ExcludedOn (model63.B 4 ++ [step63.q]) 9000000000000 (model63.caps 4)
    (model63.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7500000000000], [990000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan63Owner4Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded63_5 : ExcludedOn (model63.B 5 ++ [step63.q]) 9000000000000 (model63.caps 5)
    (model63.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_6 : ExcludedOn (model63.B 6 ++ [step63.q]) 9000000000000 (model63.caps 6)
    (model63.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_7 : ExcludedOn (model63.B 7 ++ [step63.q]) 9000000000000 (model63.caps 7)
    (model63.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_8 : ExcludedOn (model63.B 8 ++ [step63.q]) 9000000000000 (model63.caps 8)
    (model63.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded63_9 : ExcludedOn (model63.B 9 ++ [step63.q]) 9000000000000 (model63.caps 9)
    (model63.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked63 : StepValid model63 9000000000000 step63 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded63_1
    · exact excluded63_2
    · exact excluded63_3
    · exact excluded63_4
    · exact excluded63_5
    · exact excluded63_6
    · exact excluded63_7
    · exact excluded63_8
    · exact excluded63_9
theorem next63 : model63.insert step63 = model64 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext220000230000
end ConwaySoifer.Simplified.Certificates

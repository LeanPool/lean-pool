/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint310000320000
import Mathlib.Tactic.FinCases

/-!
# Sint 310000 320000 5

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
namespace Sint310000320000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner0Part0 : FanWitness := (.next ([-435000000000], [750000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([-1680000000000], [2895000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([-1935000000000], [3330000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-1185000000000], [1935000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-525000000000],
    [825000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-4305000000000], [6735000000000])
    (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-1185000000000], [1830000000000]) (some (10, 5, 8))
    (some (10, 5, 8)) (.next ([-855000000000], [1320000000000]) (some (10, 5, 8)) (some (10, 5, 8))
    (.next ([-4452000000000], [6702000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next
    ([-4605000000000], [6210000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-492000000000],
    [645000000000]) (some (10, 5, 8)) (some (10, 5, 8)) (.next ([-5625000000000], [7200000000000])
    (some (10, 5, 8)) (some (10, 5, 9)) (.next ([-5772000000000], [7167000000000]) (some (10, 5, 9))
    (some (10, 5, 9)) (.next ([-5955000000000], [6885000000000]) (some (10, 5, 9)) (some (10, 5, 9))
    (.next ([-5925000000000], [6675000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-7455000000000], [8385000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-6102000000000], [6852000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-1500000000000], [1650000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-7602000000000], [8352000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-6270000000000], [6555000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-6270000000000], [6450000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-6255000000000], [6360000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-6417000000000], [6522000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.next
    ([-7755000000000], [7860000000000]) (some (10, 5, 9)) (some (10, 5, 9)) (.terminal (some (10, 5,
    9)) (some (10, 5, 9)) (some (10, 5, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner0Part1 : FanWitness := (.next ([0], [2040000000000]) (some (0, 10, 7)) (some (0, 10,
    7)) (.next ([-105000000000], [2145000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([-540000000000], [6570000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-465000000000],
    [5625000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-180000000000], [2145000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-465000000000], [5520000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) (.next ([-645000000000], [6570000000000]) (some (0, 10, 7)) (some (0, 10, 7))
    (.next ([-645000000000], [5772000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([-645000000000], [5667000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-285000000000],
    [2250000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-33000000000], [180000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-330000000000], [1725000000000]) (some (0, 10, 7))
    (some (0, 10, 8)) (.next ([-1290000000000], [5925000000000]) (some (0, 10, 8)) (some (0, 10, 8))
    (.next ([-1290000000000], [5820000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next
    ([-435000000000], [1830000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-645000000000],
    [1830000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-645000000000], [1395000000000])
    (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-1500000000000], [3150000000000]) (some (0, 10, 8))
    (some (0, 10, 8)) (.next ([-315000000000], [645000000000]) (some (0, 10, 8)) (some (10, 10, 8))
    (.next ([-645000000000], [1290000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next
    ([-330000000000], [645000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next ([-750000000000],
    [1395000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next ([-1575000000000],
    [2895000000000]) (some (10, 10, 8)) (some (10, 10, 8)) (.next ([-1830000000000],
    [3225000000000]) (some (10, 10, 8)) (some (10, 10, 8)) fan40Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner0Part2 : FanWitness := (.next ([315000000000], [435000000000]) (some (9, 10, 7)) (some
    (9, 10, 7)) (.next ([1215000000000], [1680000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
    ([1395000000000], [1935000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([750000000000],
    [1185000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([300000000000], [525000000000])
    (some (9, 10, 7)) (some (9, 10, 7)) (.next ([2430000000000], [4305000000000]) (some (9, 10, 7))
    (some (9, 10, 7)) (.next ([645000000000], [1185000000000]) (some (9, 10, 7)) (some (9, 10, 7))
    (.next ([465000000000], [855000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
    ([2250000000000], [4452000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([1605000000000],
    [4605000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([153000000000], [492000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([1575000000000], [5625000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) (.next ([1395000000000], [5772000000000]) (some (0, 10, 7)) (some (0, 10, 7))
    (.next ([930000000000], [5955000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([750000000000], [5925000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([930000000000],
    [7455000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([750000000000], [6102000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([150000000000], [1500000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) (.next ([750000000000], [7602000000000]) (some (0, 10, 7)) (some (0, 10, 7))
    (.next ([285000000000], [6270000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([180000000000], [6270000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([105000000000],
    [6255000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([105000000000], [6417000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([105000000000], [7755000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) fan40Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner4Part0 : FanWitness := (.next ([-570000000000], [1695000000000]) (some (0, 9, 8))
    (some (0, 9, 8)) (.next ([-765000000000], [2100000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    (.next ([-1710000000000], [4290000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next
    ([-2025000000000], [4875000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-2895000000000],
    [6498000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-510000000000], [1095000000000])
    (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-705000000000], [1500000000000]) (some (0, 9, 8))
    (some (0, 9, 8)) (.next ([-195000000000], [405000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    (.next ([-2625000000000], [5415000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next
    ([-1455000000000], [2850000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-1290000000000],
    [2280000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-1545000000000], [2730000000000])
    (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-2895000000000], [4710000000000]) (some (0, 9, 8))
    (some (0, 9, 8)) (.next ([-3720000000000], [6000000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    (.next ([-4125000000000], [6210000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next
    ([-6420000000000], [9000000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-1500000000000],
    [2085000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-4875000000000], [6453000000000])
    (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-885000000000], [1155000000000]) (some (0, 9, 8))
    (some (0, 9, 8)) (.next ([-4875000000000], [6270000000000]) (some (0, 9, 8)) (some (0, 9, 8))
    (.next ([-2295000000000], [2790000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next
    ([-5415000000000], [6393000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-2700000000000],
    [3000000000000]) (some (0, 9, 8)) (some (0, 9, 8)) (.next ([-690000000000], [750000000000])
    (some (0, 9, 8)) (some (0, 9, 8)) (.terminal (some (0, 9, 8)) (some (0, 9, 8)) (some (0, 9,
    8)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner4Part1 : FanWitness := (.next ([270000000000], [885000000000]) (some (8, 1, 9)) (some
    (8, 1, 9)) (.next ([1395000000000], [4875000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
    ([495000000000], [2295000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([978000000000],
    [5415000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([300000000000], [2700000000000])
    (some (8, 1, 9)) (some (8, 1, 9)) (.next ([60000000000], [690000000000]) (some (8, 1, 9)) (some
    (8, 1, 9)) (.next ([0], [2895000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
    ([-117000000000], [6000000000000]) (some (0, 1, 9)) (some (0, 1, 9)) (.next ([-45000000000],
    [2025000000000]) (some (0, 1, 9)) (some (0, 1, 9)) (.next ([-105000000000], [2625000000000])
    (some (0, 1, 9)) (some (0, 2, 9)) (.next ([-315000000000], [6420000000000]) (some (0, 2, 9))
    (some (0, 2, 9)) (.next ([-210000000000], [3795000000000]) (some (0, 2, 9)) (some (0, 2, 9))
    (.next ([-165000000000], [2850000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next
    ([-270000000000], [4395000000000]) (some (0, 2, 9)) (some (0, 2, 9)) (.next ([-522000000000],
    [6210000000000]) (some (0, 2, 9)) (some (0, 9, 9)) (.next ([-60000000000], [600000000000]) (some
    (0, 9, 9)) (some (0, 9, 9)) (.next ([-165000000000], [1560000000000]) (some (0, 9, 9)) (some (0,
    9, 9)) (.next ([-615000000000], [3720000000000]) (some (0, 9, 9)) (some (0, 9, 9)) (.next
    ([-810000000000], [4125000000000]) (some (0, 9, 9)) (some (0, 9, 9)) (.next ([-1272000000000],
    [6270000000000]) (some (0, 9, 9)) (some (0, 9, 9)) (.next ([-1107000000000], [4710000000000])
    (some (0, 9, 9)) (some (0, 9, 9)) (.next ([-705000000000], [2790000000000]) (some (0, 9, 9))
    (some (0, 9, 9)) (.next ([-1500000000000], [4875000000000]) (some (0, 9, 9)) (some (0, 9, 9))
    (.next ([-2817000000000], [9000000000000]) (some (0, 9, 9)) (some (0, 9, 9))
    fan40Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner4Part2 : FanWitness := (.next ([3315000000000], [810000000000]) (some (8, 1, 9)) (some
    (8, 1, 9)) (.next ([4998000000000], [1272000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
    ([3603000000000], [1107000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([2085000000000],
    [705000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([3375000000000], [1500000000000])
    (some (8, 1, 9)) (some (8, 1, 9)) (.next ([6183000000000], [2817000000000]) (some (8, 1, 9))
    (some (8, 1, 9)) (.next ([1125000000000], [570000000000]) (some (8, 1, 9)) (some (8, 1, 9))
    (.next ([1335000000000], [765000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
    ([2580000000000], [1710000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([2850000000000],
    [2025000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([3603000000000], [2895000000000])
    (some (8, 1, 9)) (some (8, 1, 9)) (.next ([585000000000], [510000000000]) (some (8, 1, 9)) (some
    (8, 1, 9)) (.next ([795000000000], [705000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
    ([210000000000], [195000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([2790000000000],
    [2625000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([1395000000000], [1455000000000])
    (some (8, 1, 9)) (some (8, 1, 9)) (.next ([990000000000], [1290000000000]) (some (8, 1, 9))
    (some (8, 1, 9)) (.next ([1185000000000], [1545000000000]) (some (8, 1, 9)) (some (8, 1, 9))
    (.next ([1815000000000], [2895000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
    ([2280000000000], [3720000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([2085000000000],
    [4125000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([2580000000000], [6420000000000])
    (some (8, 1, 9)) (some (8, 1, 9)) (.next ([585000000000], [1500000000000]) (some (8, 1, 9))
    (some (8, 1, 9)) (.next ([1578000000000], [4875000000000]) (some (8, 1, 9)) (some (8, 1, 9))
    fan40Owner4Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan40Owner6Part0 : FanWitness := (.next ([2295000000000], [495000000000]) (some (5, 1, 3)) (some
    (5, 1, 3)) (.next ([6420000000000], [2580000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([4125000000000], [2085000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2295000000000],
    [1890000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2100000000000, 9000000000000],
    [2025000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2790000000000,
    9000000000000], [2790000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
    ([3630000000000, -9000000000000], [5370000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
    3)) (.next ([1335000000000, -9000000000000], [3480000000000, 9000000000000]) (some (5, 1, 3))
    (some (5, 1, 3)) (.next ([1335000000000, -9000000000000], [4875000000000, 9000000000000]) (some
    (5, 1, 3)) (some (5, 1, 3)) (.next ([705000000000, 9000000000000], [3420000000000,
    -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([210000000000, 9000000000000],
    [6210000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0], [1395000000000])
    (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-690000000000], [4815000000000]) (some (5, 1, 3))
    (some (5, 2, 3)) (.next ([-495000000000], [2790000000000]) (some (5, 2, 3)) (some (5, 2, 3))
    (.next ([-2580000000000], [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next
    ([-2085000000000], [6210000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1890000000000],
    [4185000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2025000000000, 9000000000000],
    [4125000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-2790000000000, -9000000000000],
    [5580000000000, 18000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-5370000000000,
    -9000000000000], [9000000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-3480000000000,
    -9000000000000], [4815000000000]) (some (5, 2, 3)) (some (5, 2, 5)) (.next ([-4875000000000,
    -9000000000000], [6210000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-3420000000000,
    9000000000000], [4125000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([-6210000000000,
    9000000000000], [6420000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.terminal (some (1, 2, 5))
    (some (1, 2, 5)) (some (1, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part0 : FanWitness := (.next ([-1575000000000], [2895000000000]) (some (0, 10, 8))
    (some (0, 10, 8)) (.next ([-1725000000000], [3105000000000]) (some (0, 10, 8)) (some (0, 10, 8))
    (.next ([-435000000000], [750000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next
    ([-1680000000000], [2895000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next
    ([-1830000000000], [3105000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-525000000000],
    [825000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-4305000000000], [6735000000000])
    (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-855000000000], [1320000000000]) (some (0, 10, 8))
    (some (0, 10, 8)) (.next ([-4452000000000], [6702000000000]) (some (0, 10, 8)) (some (1, 10, 8))
    (.next ([-2475000000000], [3420000000000]) (some (1, 10, 8)) (some (1, 10, 8)) (.next
    ([-4605000000000], [6210000000000]) (some (1, 10, 8)) (some (1, 10, 8)) (.next ([-492000000000],
    [645000000000]) (some (1, 10, 8)) (some (1, 10, 8)) (.next ([-5625000000000], [7200000000000])
    (some (1, 10, 8)) (some (1, 10, 9)) (.next ([-3975000000000], [5070000000000]) (some (1, 10, 9))
    (some (1, 10, 9)) (.next ([-5772000000000], [7167000000000]) (some (1, 10, 9)) (some (1, 10, 9))
    (.next ([-3120000000000], [3750000000000]) (some (1, 10, 9)) (some (1, 10, 9)) (.next
    ([-5955000000000], [6885000000000]) (some (1, 10, 9)) (some (10, 10, 9)) (.next
    ([-5925000000000], [6675000000000]) (some (10, 10, 9)) (some (10, 10, 9)) (.next
    ([-6102000000000], [6852000000000]) (some (10, 10, 9)) (some (10, 10, 9)) (.next
    ([-1500000000000], [1650000000000]) (some (10, 10, 9)) (some (10, 10, 9)) (.next
    ([-6270000000000], [6555000000000]) (some (10, 10, 9)) (some (10, 10, 9)) (.next
    ([-6270000000000], [6450000000000]) (some (10, 10, 9)) (some (10, 10, 9)) (.next
    ([-6255000000000], [6360000000000]) (some (10, 10, 9)) (some (10, 10, 9)) (.next
    ([-6417000000000], [6522000000000]) (some (10, 10, 9)) (some (10, 10, 9)) (.terminal (some (10,
    10, 9)) (some (10, 10, 9)) (some (10, 10, 9)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part1 : FanWitness := (.next ([-105000000000], [2145000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) (.next ([-540000000000], [6570000000000]) (some (0, 10, 7)) (some (0, 10, 7))
    (.next ([-465000000000], [5625000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([-180000000000], [2145000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-465000000000],
    [5520000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-645000000000], [6570000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-645000000000], [5772000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) (.next ([-645000000000], [5667000000000]) (some (0, 10, 7)) (some (0, 10, 7))
    (.next ([-285000000000], [2250000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([-1545000000000], [9375000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([-1725000000000], [9522000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-33000000000],
    [180000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([-330000000000], [1725000000000])
    (some (0, 10, 7)) (some (0, 10, 8)) (.next ([-1290000000000], [5925000000000]) (some (0, 10, 8))
    (some (0, 10, 8)) (.next ([-1290000000000], [5820000000000]) (some (0, 10, 8)) (some (0, 10, 8))
    (.next ([-435000000000], [1830000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next
    ([-2370000000000], [9675000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next
    ([-1080000000000], [3855000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next
    ([-1080000000000], [3750000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-645000000000],
    [1395000000000]) (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-315000000000], [645000000000])
    (some (0, 10, 8)) (some (0, 10, 8)) (.next ([-645000000000], [1290000000000]) (some (0, 10, 8))
    (some (0, 10, 8)) (.next ([-330000000000], [645000000000]) (some (0, 10, 8)) (some (0, 10, 8))
    (.next ([-750000000000], [1395000000000]) (some (0, 10, 8)) (some (0, 10, 8))
    fan42Owner0Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part2 : FanWitness := (.next ([1380000000000], [1725000000000]) (some (9, 10, 7))
    (some (9, 10, 7)) (.next ([315000000000], [435000000000]) (some (9, 10, 7)) (some (9, 10, 7))
    (.next ([1215000000000], [1680000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
    ([1275000000000], [1830000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([300000000000],
    [525000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([2430000000000], [4305000000000])
    (some (9, 10, 7)) (some (9, 10, 7)) (.next ([465000000000], [855000000000]) (some (9, 10, 7))
    (some (9, 10, 7)) (.next ([2250000000000], [4452000000000]) (some (9, 10, 7)) (some (9, 10, 7))
    (.next ([945000000000], [2475000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
    ([1605000000000], [4605000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([153000000000],
    [492000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([1575000000000], [5625000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([1095000000000], [3975000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) (.next ([1395000000000], [5772000000000]) (some (0, 10, 7)) (some (0, 10, 7))
    (.next ([630000000000], [3120000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([930000000000], [5955000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([750000000000],
    [5925000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([750000000000], [6102000000000])
    (some (0, 10, 7)) (some (0, 10, 7)) (.next ([150000000000], [1500000000000]) (some (0, 10, 7))
    (some (0, 10, 7)) (.next ([285000000000], [6270000000000]) (some (0, 10, 7)) (some (0, 10, 7))
    (.next ([180000000000], [6270000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next
    ([105000000000], [6255000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([105000000000],
    [6417000000000]) (some (0, 10, 7)) (some (0, 10, 7)) (.next ([0], [2040000000000]) (some (0, 10,
    7)) (some (0, 10, 7)) fan42Owner0Part1))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner0Part3 : FanWitness := (.next ([6030000000000], [540000000000]) (some (9, 10, 10))
    (some (9, 10, 10)) (.next ([5160000000000], [465000000000]) (some (9, 10, 10)) (some (9, 10,
    10)) (.next ([1965000000000], [180000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next
    ([5055000000000], [465000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next ([5925000000000],
    [645000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next ([5127000000000], [645000000000])
    (some (9, 10, 10)) (some (9, 10, 10)) (.next ([5022000000000], [645000000000]) (some (9, 10,
    10)) (some (9, 10, 10)) (.next ([1965000000000], [285000000000]) (some (9, 10, 10)) (some (9,
    10, 10)) (.next ([7830000000000], [1545000000000]) (some (9, 10, 10)) (some (9, 10, 10)) (.next
    ([7797000000000], [1725000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([147000000000],
    [33000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([1395000000000], [330000000000])
    (some (9, 10, 7)) (some (9, 10, 7)) (.next ([4635000000000], [1290000000000]) (some (9, 10, 7))
    (some (9, 10, 7)) (.next ([4530000000000], [1290000000000]) (some (9, 10, 7)) (some (9, 10, 7))
    (.next ([1395000000000], [435000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
    ([7305000000000], [2370000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([2775000000000],
    [1080000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([2670000000000], [1080000000000])
    (some (9, 10, 7)) (some (9, 10, 7)) (.next ([750000000000], [645000000000]) (some (9, 10, 7))
    (some (9, 10, 7)) (.next ([330000000000], [315000000000]) (some (9, 10, 7)) (some (9, 10, 7))
    (.next ([645000000000], [645000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
    ([315000000000], [330000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([645000000000],
    [750000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([1320000000000], [1575000000000])
    (some (9, 10, 7)) (some (9, 10, 7)) fan42Owner0Part2))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan42Owner5Part0 : FanWitness := (.next ([4185000000000, -9000000000000], [315000000000,
    9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([2997000000000], [525000000000]) (some
    (4, 1, 3)) (some (4, 1, 3)) (.next ([1920000000000], [555000000000]) (some (4, 1, 3)) (some (4,
    1, 5)) (.next ([3000000000000], [978000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([4380000000000], [2040000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([4380000000000, 0],
    [2790000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([3630000000000,
    -9000000000000], [2790000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([3402000000000], [3978000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2442000000000],
    [3000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2475000000000], [4500000000000])
    (some (0, 1, 5)) (some (0, 1, 5)) (.next ([210000000000, -9000000000000], [978000000000]) (some
    (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [4380000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([-120000000000], [6975000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-315000000000, -9000000000000], [4500000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-525000000000], [3522000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-555000000000],
    [2475000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-978000000000], [3978000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-2040000000000], [6420000000000]) (some (0, 2, 4))
    (some (0, 2, 4)) (.next ([-2790000000000, -9000000000000], [7170000000000, 9000000000000]) (some
    (0, 2, 4)) (some (0, 2, 4)) (.next ([-2790000000000, -9000000000000], [6420000000000]) (some (0,
    2, 4)) (some (0, 2, 4)) (.next ([-3978000000000], [7380000000000]) (some (0, 2, 4)) (some (0, 2,
    4)) (.next ([-3000000000000], [5442000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-4500000000000], [6975000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-978000000000,
    0], [1188000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
    4)) (some (0, 3, 4)) (some (0, 3, 4)))))))))))))))))))))))))))

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2040000000000], [105000000000]) (some (9, 10,
      5)) (some (9, 10, 6)) (.next ([6030000000000], [540000000000]) (some (9, 10, 6)) (some (9, 10,
      6)) (.next ([5160000000000], [465000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next
      ([1965000000000], [180000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([5055000000000],
      [465000000000]) (some (9, 10, 6)) (some (9, 10, 6)) (.next ([5925000000000], [645000000000])
      (some (9, 10, 6)) (some (9, 10, 7)) (.next ([5127000000000], [645000000000]) (some (9, 10, 7))
      (some (9, 10, 7)) (.next ([5022000000000], [645000000000]) (some (9, 10, 7)) (some (9, 10, 7))
      (.next ([1965000000000], [285000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
      ([147000000000], [33000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([1395000000000],
      [330000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([4635000000000], [1290000000000])
      (some (9, 10, 7)) (some (9, 10, 7)) (.next ([4530000000000], [1290000000000]) (some (9, 10,
      7)) (some (9, 10, 7)) (.next ([1395000000000], [435000000000]) (some (9, 10, 7)) (some (9, 10,
      7)) (.next ([1185000000000], [645000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
      ([750000000000], [645000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([1650000000000],
      [1500000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next ([330000000000], [315000000000])
      (some (9, 10, 7)) (some (9, 10, 7)) (.next ([645000000000], [645000000000]) (some (9, 10, 7))
      (some (9, 10, 7)) (.next ([315000000000], [330000000000]) (some (9, 10, 7)) (some (9, 10, 7))
      (.next ([645000000000], [750000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
      ([1320000000000], [1575000000000]) (some (9, 10, 7)) (some (9, 10, 7)) (.next
      ([1395000000000], [1830000000000]) (some (9, 10, 7)) (some (9, 10, 7))
      fan40Owner0Part2))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5883000000000], [117000000000]) (some (8, 0, 9))
      (some (8, 1, 9)) (.next ([1980000000000], [45000000000]) (some (8, 1, 9)) (some (8, 1, 9))
      (.next ([2520000000000], [105000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
      ([6105000000000], [315000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([3585000000000],
      [210000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([2685000000000], [165000000000])
      (some (8, 1, 9)) (some (8, 1, 9)) (.next ([4125000000000], [270000000000]) (some (8, 1, 9))
      (some (8, 1, 9)) (.next ([5688000000000], [522000000000]) (some (8, 1, 9)) (some (8, 1, 9))
      (.next ([540000000000], [60000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next
      ([1395000000000], [165000000000]) (some (8, 1, 9)) (some (8, 1, 9)) (.next ([3105000000000],
      [615000000000]) (some (8, 1, 9)) (some (8, 1, 9)) fan40Owner4Part2)))))))))))) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [690000000000]) (some (5, 1, 2))
      (some (5, 1, 3)) fan40Owner6Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_9 : ExcludedOn (model40.B 9 ++ [step40.q]) 9000000000000 (model40.caps 9)
    (model40.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded40_4
    · exact (hj rfl).elim
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_0 : ExcludedOn (model41.B 0 ++ [step41.q]) 9000000000000 (model41.caps 0)
    (model41.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6420000000000], [1020000000000]) (some (4, 0,
      3)) (some (4, 5, 3)) (.next ([3000000000000], [978000000000]) (some (4, 5, 3)) (some (4, 5,
      3)) (.next ([4380000000000], [2040000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([1770000000000, 9000000000000], [1020000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([4380000000000, 0], [2790000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([3630000000000, -9000000000000], [2790000000000, 9000000000000]) (some (0, 5, 3)) (some (0,
      5, 3)) (.next ([1980000000000], [1998000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
      ([3402000000000], [3978000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2442000000000],
      [3000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([210000000000, -9000000000000],
      [978000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([0], [4380000000000]) (some (0, 5,
      4)) (some (0, 5, 4)) (.next ([-1020000000000], [7440000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-978000000000], [3978000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2040000000000], [6420000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1020000000000,
      0], [2790000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2790000000000,
      -9000000000000], [7170000000000, 9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-2790000000000, -9000000000000], [6420000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-1998000000000], [3978000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3978000000000], [7380000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3000000000000], [5442000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-978000000000,
      0], [1188000000000, -9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 3, 4)) (some (0, 3, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_7 : ExcludedOn (model41.B 7 ++ [step41.q]) 9000000000000 (model41.caps 7)
    (model41.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_8 : ExcludedOn (model41.B 8 ++ [step41.q]) 9000000000000 (model41.caps 8)
    (model41.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded41_3
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact (hj rfl).elim
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded42_0 : ExcludedOn (model42.B 0 ++ [step42.q]) 9000000000000 (model42.caps 0)
    (model42.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2040000000000], [105000000000]) (some (9, 10,
      10)) (some (9, 10, 10)) fan42Owner0Part3))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_1 : ExcludedOn (model42.B 1 ++ [step42.q]) 9000000000000 (model42.caps 1)
    (model42.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_2 : ExcludedOn (model42.B 2 ++ [step42.q]) 9000000000000 (model42.caps 2)
    (model42.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_3 : ExcludedOn (model42.B 3 ++ [step42.q]) 9000000000000 (model42.caps 3)
    (model42.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_4 : ExcludedOn (model42.B 4 ++ [step42.q]) 9000000000000 (model42.caps 4)
    (model42.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_5 : ExcludedOn (model42.B 5 ++ [step42.q]) 9000000000000 (model42.caps 5)
    (model42.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6855000000000], [120000000000]) (some (4, 0, 3))
      (some (4, 1, 3)) fan42Owner5Part0)) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded42_7 : ExcludedOn (model42.B 7 ++ [step42.q]) 9000000000000 (model42.caps 7)
    (model42.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_8 : ExcludedOn (model42.B 8 ++ [step42.q]) 9000000000000 (model42.caps 8)
    (model42.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded42_9 : ExcludedOn (model42.B 9 ++ [step42.q]) 9000000000000 (model42.caps 9)
    (model42.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded42_3
    · exact excluded42_4
    · exact excluded42_5
    · exact (hj rfl).elim
    · exact excluded42_7
    · exact excluded42_8
    · exact excluded42_9
theorem next42 : model42.insert step42 = model43 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded43_0 : ExcludedOn (model43.B 0 ++ [step43.q]) 9000000000000 (model43.caps 0)
    (model43.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_1 : ExcludedOn (model43.B 1 ++ [step43.q]) 9000000000000 (model43.caps 1)
    (model43.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_2 : ExcludedOn (model43.B 2 ++ [step43.q]) 9000000000000 (model43.caps 2)
    (model43.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_3 : ExcludedOn (model43.B 3 ++ [step43.q]) 9000000000000 (model43.caps 3)
    (model43.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_4 : ExcludedOn (model43.B 4 ++ [step43.q]) 9000000000000 (model43.caps 4)
    (model43.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_5 : ExcludedOn (model43.B 5 ++ [step43.q]) 9000000000000 (model43.caps 5)
    (model43.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3000000000000], [978000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) (.next ([4380000000000], [2040000000000]) (some (4, 1, 5)) (some (4, 1, 5))
      (.next ([4380000000000, 0], [2790000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([3630000000000, -9000000000000], [2790000000000, 9000000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([4380000000000], [3645000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([3402000000000], [3978000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([2442000000000], [3000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([2775000000000],
      [3645000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([333000000000], [645000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([210000000000, -9000000000000], [978000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([0], [4380000000000]) (some (0, 1, 4)) (some (0, 1,
      4)) (.next ([-978000000000], [3978000000000]) (some (0, 1, 4)) (some (0, 5, 4)) (.next
      ([-2040000000000], [6420000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2790000000000,
      -9000000000000], [7170000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2790000000000, -9000000000000], [6420000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3645000000000], [8025000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3978000000000], [7380000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3000000000000], [5442000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3645000000000], [6420000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-645000000000],
      [978000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-978000000000, 0], [1188000000000,
      -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5, 4)) (some (0, 5,
      4)) (some (0, 5, 4))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded43_7 : ExcludedOn (model43.B 7 ++ [step43.q]) 9000000000000 (model43.caps 7)
    (model43.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_8 : ExcludedOn (model43.B 8 ++ [step43.q]) 9000000000000 (model43.caps 8)
    (model43.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded43_9 : ExcludedOn (model43.B 9 ++ [step43.q]) 9000000000000 (model43.caps 9)
    (model43.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5280000000000], [75000000000]) (some (3, 0, 1))
      (some (3, 1, 2)) (.next ([2625000000000], [1020000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([4260000000000], [3720000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([3645000000000], [5355000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([0],
      [7980000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-75000000000], [5355000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1020000000000], [3645000000000]) (some (0, 1, 2))
      (some (0, 1, 3)) (.next ([-3720000000000], [7980000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5355000000000], [9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem checked43 : StepValid model43 9000000000000 step43 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded43_0
    · exact excluded43_1
    · exact excluded43_2
    · exact excluded43_3
    · exact excluded43_4
    · exact excluded43_5
    · exact (hj rfl).elim
    · exact excluded43_7
    · exact excluded43_8
    · exact excluded43_9
theorem next43 : model43.insert step43 = model44 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint310000320000
end ConwaySoifer.Simplified.Certificates

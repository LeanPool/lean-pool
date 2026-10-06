/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext170000180000
import Mathlib.Tactic.FinCases

/-!
# Sext 170000 180000 2

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
namespace Sext170000180000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan16Owner4Part0 : FanWitness := (.next ([1530000000000, 9000000000000], [5121000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([1125000000000], [3825000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([765000000000], [4125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([9000000000], [2871000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [5121000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-171000000000], [3996000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-231000000000], [4356000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-180000000000], [1125000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-240000000000], [1485000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-60000000000],
    [360000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1350000000000, 9000000000000],
    [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2871000000000], [8991000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2295000000000, 9000000000000], [4950000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2880000000000], [6120000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-2340000000000, 9000000000000], [4590000000000, -9000000000000]) (some
    (0, 1, 6)) (some (0, 1, 6)) (.next ([-2595000000000, 9000000000000], [4890000000000]) (some (0,
    1, 6)) (some (0, 1, 6)) (.next ([-2700000000000], [4995000000000]) (some (0, 1, 6)) (some (0, 1,
    6)) (.next ([-2880000000000], [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2640000000000], [4635000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3870000000000],
    [6120000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-5121000000000], [6651000000000,
    9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3825000000000], [4950000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4125000000000], [4890000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-2871000000000], [2880000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.terminal (some (0, 1, 6)) (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan17Owner4Part0 : FanWitness := (.next ([1530000000000, 9000000000000], [5121000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([1125000000000], [3825000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([765000000000], [4125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([9000000000], [2871000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [5121000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-171000000000], [3996000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-231000000000], [4356000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-996000000000], [9231000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-765000000000], [4875000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-825000000000],
    [5235000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1005000000000], [6360000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-180000000000], [1125000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-240000000000], [1485000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-60000000000], [360000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-1350000000000, 9000000000000], [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2580000000000, 9000000000000], [6705000000000, -9000000000000]) (some (0, 1, 6)) (some (0, 1,
    6)) (.next ([-2295000000000, 9000000000000], [4950000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-4110000000000], [8235000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2595000000000, 9000000000000], [4890000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-2880000000000], [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-5121000000000],
    [6651000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-3825000000000],
    [4950000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-4125000000000], [4890000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2871000000000], [2880000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.terminal (some (0, 1, 6)) (some (0, 2, 6)) (some (0, 2,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner0Part0 : FanWitness := (.next ([1875000000000], [7500000000000]) (some (0, 6, 2))
    (some (0, 6, 3)) (.next ([990000000000], [6615000000000]) (some (0, 6, 3)) (some (0, 6, 3))
    (.next ([990000000000], [7875000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next
    ([615000000000], [7365000000000]) (some (0, 6, 3)) (some (0, 6, 3)) (.next ([510000000000],
    [6120000000000]) (some (0, 6, 3)) (some (6, 6, 3)) (.next ([450000000000], [6000000000000])
    (some (6, 6, 3)) (some (6, 6, 3)) (.next ([0], [1260000000000]) (some (6, 6, 3)) (some (6, 6,
    4)) (.next ([-60000000000], [6885000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next
    ([-135000000000], [1395000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([-870000000000],
    [8865000000000]) (some (6, 6, 4)) (some (6, 6, 4)) (.next ([-1050000000000], [8925000000000])
    (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-885000000000], [7380000000000]) (some (6, 2, 4))
    (some (6, 2, 4)) (.next ([-945000000000], [7260000000000]) (some (6, 2, 4)) (some (6, 2, 4))
    (.next ([-1260000000000], [7005000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next
    ([-1320000000000], [6885000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-375000000000],
    [750000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-510000000000], [885000000000]) (some
    (6, 2, 4)) (some (6, 2, 4)) (.next ([-120000000000], [180000000000]) (some (6, 2, 4)) (some (6,
    2, 5)) (.next ([-7500000000000], [9375000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next
    ([-6615000000000], [7605000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-7875000000000],
    [8865000000000]) (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-7365000000000], [7980000000000])
    (some (6, 2, 5)) (some (6, 2, 5)) (.next ([-6120000000000], [6630000000000]) (some (6, 2, 5))
    (some (6, 2, 5)) (.next ([-6000000000000], [6450000000000]) (some (6, 2, 5)) (some (6, 2, 5))
    (.terminal (some (6, 2, 5)) (some (6, 2, 5)) (some (6, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan18Owner4Part0 : FanWitness := (.next ([1125000000000], [3825000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([765000000000], [4125000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([1020000000000, 9000000000000], [7500000000000]) (some (5, 6, 4)) (some (5, 6, 4))
    (.next ([9000000000], [2871000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0],
    [5121000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-171000000000], [3996000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-231000000000], [4356000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-510000000000], [7500000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-180000000000], [1125000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-240000000000], [1485000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-60000000000],
    [360000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-510000000000], [2379000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1350000000000, 9000000000000], [5130000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-2610000000000], [6225000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-2550000000000], [5865000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2295000000000, 9000000000000], [4950000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-2370000000000], [4740000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2595000000000, 9000000000000], [4890000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-2880000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 5)) (.next ([-5121000000000],
    [6651000000000, 9000000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-3825000000000],
    [4950000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-4125000000000], [4890000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-7500000000000], [8520000000000, 9000000000000])
    (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2871000000000], [2880000000000]) (some (0, 6, 5))
    (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 5)) (some (0, 6,
    5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner3Part0 : FanWitness := (.next ([1530000000000, 9000000000000], [1530000000000,
    9000000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([2295000000000, 9000000000000],
    [2595000000000, -9000000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([1350000000000,
    -9000000000000], [2250000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next ([2430000000000,
    9000000000000], [6960000000000, -9000000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
    ([765000000000], [4125000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([510000000000,
    9000000000000], [5010000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([135000000000],
    [4365000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [1530000000000, 9000000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-120000000000], [3225000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-630000000000, -9000000000000], [8490000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-240000000000], [2115000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-720000000000, 9000000000000], [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-765000000000, -9000000000000], [4125000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1020000000000], [3480000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4))
    (.next ([-1980000000000], [6240000000000]) (some (0, 6, 4)) (some (1, 6, 4)) (.next
    ([-3090000000000], [7470000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2250000000000],
    [5130000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-1530000000000, -9000000000000],
    [3060000000000, 18000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2595000000000,
    9000000000000], [4890000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2250000000000],
    [3600000000000, -9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-6960000000000,
    9000000000000], [9390000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4125000000000],
    [4890000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-5010000000000, 0], [5520000000000,
    9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4365000000000], [4500000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.terminal (some (1, 6, 4)) (some (1, 6, 4)) (some (1, 6,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan19Owner4Part0 : FanWitness := (.next ([1530000000000, 9000000000000], [5121000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([1920000000000, 9000000000000], [6570000000000,
    -9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([765000000000], [4125000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([390000000000], [8100000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([9000000000], [2871000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([0], [5121000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([-171000000000],
    [3996000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-231000000000], [4356000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-375000000000], [3975000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-180000000000], [1125000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-240000000000], [1485000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-60000000000], [360000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-735000000000],
    [4275000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1350000000000, 9000000000000],
    [5130000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-1860000000000], [5220000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2295000000000, 9000000000000], [4950000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2595000000000, 9000000000000], [4890000000000])
    (some (0, 1, 6)) (some (0, 1, 6)) (.next ([-2880000000000], [5130000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-4731000000000], [8100000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-5121000000000], [6651000000000, 9000000000000]) (some (0, 1, 6)) (some (0, 6, 6))
    (.next ([-6570000000000, 9000000000000], [8490000000000]) (some (0, 6, 6)) (some (0, 6, 6))
    (.next ([-4125000000000], [4890000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-8100000000000], [8490000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2871000000000],
    [2880000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.terminal (some (0, 6, 5)) (some (0, 6, 5))
    (some (0, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan20Owner3Part0 : FanWitness := (.next ([2880000000000], [2250000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([4890000000000], [4350000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some (6, 1, 3)) (some
    (6, 1, 3)) (.next ([2295000000000, 9000000000000], [2595000000000, -9000000000000]) (some (6, 1,
    3)) (some (6, 1, 3)) (.next ([1350000000000, -9000000000000], [2250000000000]) (some (6, 1, 3))
    (some (6, 1, 4)) (.next ([1530000000000, 9000000000000], [3585000000000, -9000000000000]) (some
    (6, 1, 4)) (some (6, 1, 4)) (.next ([765000000000], [4125000000000]) (some (6, 1, 4)) (some (6,
    1, 4)) (.next ([510000000000, 9000000000000], [5010000000000]) (some (6, 1, 4)) (some (6, 1, 4))
    (.next ([0], [1530000000000, 9000000000000]) (some (6, 1, 4)) (some (6, 2, 4)) (.next
    ([-120000000000], [3225000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-240000000000],
    [2115000000000]) (some (6, 2, 4)) (some (6, 2, 4)) (.next ([-720000000000, 9000000000000],
    [5130000000000]) (some (6, 2, 4)) (some (6, 3, 4)) (.next ([-1125000000000], [6135000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-765000000000, -9000000000000], [4125000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-1020000000000], [3480000000000, -9000000000000])
    (some (6, 3, 4)) (some (6, 3, 4)) (.next ([-2235000000000], [7365000000000]) (some (6, 3, 4))
    (some (6, 3, 4)) (.next ([-2250000000000], [5130000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-4350000000000], [9240000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) (some (6, 3, 4)) (some (6,
    3, 4)) (.next ([-2595000000000, 9000000000000], [4890000000000]) (some (6, 3, 4)) (some (6, 3,
    4)) (.next ([-2250000000000], [3600000000000, -9000000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-3585000000000, 9000000000000], [5115000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.next ([-4125000000000], [4890000000000]) (some (6, 3, 4)) (some (6, 3, 4)) (.next
    ([-5010000000000, 0], [5520000000000, 9000000000000]) (some (6, 3, 4)) (some (6, 3, 4))
    (.terminal (some (6, 3, 4)) (some (6, 3, 4)) (some (6, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan21Owner3Part0 : FanWitness := (.next ([1350000000000, -9000000000000], [2250000000000]) (some
    (5, 6, 4)) (some (5, 6, 4)) (.next ([2775000000000, -9000000000000], [4875000000000]) (some (5,
    6, 4)) (some (5, 6, 4)) (.next ([1425000000000], [2625000000000]) (some (5, 6, 4)) (some (5, 6,
    4)) (.next ([765000000000], [4125000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([510000000000, 9000000000000], [5010000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([315000000000], [3855000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([0], [1530000000000,
    9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([-120000000000], [3225000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-240000000000], [2115000000000]) (some (0, 6, 4))
    (some (0, 6, 4)) (.next ([-720000000000, 9000000000000], [5130000000000]) (some (0, 6, 4)) (some
    (0, 6, 4)) (.next ([-750000000000], [4290000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-765000000000, -9000000000000], [4125000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1020000000000], [3480000000000, -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-3345000000000, 9000000000000], [9180000000000]) (some (0, 6, 4)) (some (1, 6, 4)) (.next
    ([-2250000000000], [5130000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-1530000000000,
    -9000000000000], [3060000000000, 18000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-2595000000000, 9000000000000], [4890000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next
    ([-4875000000000], [9180000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2250000000000],
    [3600000000000, -9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4875000000000],
    [7650000000000, -9000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2625000000000],
    [4050000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-4125000000000], [4890000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-5010000000000, 0], [5520000000000, 9000000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-3855000000000], [4170000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.terminal (some (1, 6, 4)) (some (6, 6, 4)) (some (6, 6,
    4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan22Owner3Part0 : FanWitness := (.next ([1530000000000, 9000000000000], [1530000000000,
    9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2295000000000, 9000000000000],
    [2595000000000, -9000000000000]) (some (5, 6, 3)) (some (5, 6, 3)) (.next ([4410000000000],
    [5031000000000]) (some (5, 6, 3)) (some (5, 6, 4)) (.next ([1350000000000, -9000000000000],
    [2250000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([2880000000000, -9000000000000],
    [5031000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next ([1530000000000], [2781000000000])
    (some (5, 6, 4)) (some (5, 6, 4)) (.next ([765000000000], [4125000000000]) (some (5, 6, 4))
    (some (5, 6, 4)) (.next ([510000000000, 9000000000000], [5010000000000]) (some (5, 6, 4)) (some
    (5, 6, 4)) (.next ([0], [1530000000000, 9000000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
    ([-120000000000], [3225000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-240000000000],
    [2115000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-720000000000, 9000000000000],
    [5130000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-765000000000, -9000000000000],
    [4125000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1020000000000], [3480000000000,
    -9000000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-3501000000000, 9000000000000],
    [9441000000000]) (some (0, 6, 4)) (some (1, 6, 4)) (.next ([-2250000000000], [5130000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-1530000000000, -9000000000000], [3060000000000,
    18000000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2595000000000, 9000000000000],
    [4890000000000]) (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-5031000000000], [9441000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2250000000000], [3600000000000, -9000000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-5031000000000], [7911000000000, -9000000000000])
    (some (1, 6, 4)) (some (1, 6, 4)) (.next ([-2781000000000], [4311000000000]) (some (1, 6, 4))
    (some (1, 6, 4)) (.next ([-4125000000000], [4890000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.next ([-5010000000000, 0], [5520000000000, 9000000000000]) (some (1, 6, 4)) (some (1, 6, 4))
    (.terminal (some (1, 6, 4)) (some (6, 6, 4)) (some (1, 6, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan23Owner3Part0 : FanWitness := (.next ([2460000000000, -9000000000000], [1020000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([2880000000000], [2250000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some (5, 1, 6))
    (some (5, 1, 6)) (.next ([2295000000000, 9000000000000], [2595000000000, -9000000000000]) (some
    (5, 1, 6)) (some (5, 1, 6)) (.next ([4215000000000], [5010000000000]) (some (5, 1, 6)) (some (5,
    1, 6)) (.next ([2985000000000], [5130000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
    ([1110000000000], [4890000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([765000000000],
    [4125000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([510000000000, 9000000000000],
    [5010000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0], [1530000000000, 9000000000000])
    (some (5, 1, 6)) (some (5, 2, 6)) (.next ([-120000000000], [3225000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-240000000000], [2115000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-720000000000, 9000000000000], [5130000000000]) (some (0, 2, 6)) (some (0, 3, 6))
    (.next ([-765000000000, -9000000000000], [4125000000000]) (some (0, 3, 6)) (some (0, 3, 6))
    (.next ([-1530000000000, -9000000000000], [6765000000000, 9000000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([-1020000000000], [3480000000000, -9000000000000]) (some (0, 3, 6)) (some (0,
    3, 6)) (.next ([-2250000000000], [5130000000000]) (some (0, 3, 6)) (some (1, 3, 6)) (.next
    ([-1530000000000, -9000000000000], [3060000000000, 18000000000000]) (some (1, 3, 6)) (some (1,
    3, 6)) (.next ([-2595000000000, 9000000000000], [4890000000000]) (some (1, 3, 6)) (some (1, 3,
    6)) (.next ([-5010000000000], [9225000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next
    ([-5130000000000], [8115000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-4890000000000],
    [6000000000000]) (some (1, 3, 6)) (some (1, 3, 6)) (.next ([-4125000000000], [4890000000000])
    (some (1, 3, 6)) (some (1, 6, 6)) (.next ([-5010000000000, 0], [5520000000000, 9000000000000])
    (some (1, 6, 6)) (some (1, 6, 6)) (.terminal (some (1, 6, 6)) (some (1, 6, 4)) (some (1, 6,
    6)))))))))))))))))))))))))))

theorem excluded16_0 : ExcludedOn (model16.B 0 ++ [step16.q]) 9000000000000 (model16.caps 0)
    (model16.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_1 : ExcludedOn (model16.B 1 ++ [step16.q]) 9000000000000 (model16.caps 1)
    (model16.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_2 : ExcludedOn (model16.B 2 ++ [step16.q]) 9000000000000 (model16.caps 2)
    (model16.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_4 : ExcludedOn (model16.B 4 ++ [step16.q]) 9000000000000 (model16.caps 4)
    (model16.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [171000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([4125000000000], [231000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([945000000000], [180000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([1245000000000], [240000000000]) (some (6, 1, 2)) (some (6, 1, 3)) (.next ([300000000000],
      [60000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([3780000000000, 9000000000000],
      [1350000000000, -9000000000000]) (some (6, 1, 3)) (some (6, 1, 4)) (.next ([6120000000000],
      [2871000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2655000000000, 9000000000000],
      [2295000000000, -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([3240000000000],
      [2880000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2250000000000], [2340000000000,
      -9000000000000]) (some (6, 1, 4)) (some (6, 1, 4)) (.next ([2295000000000, 9000000000000],
      [2595000000000, -9000000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([2295000000000],
      [2700000000000]) (some (5, 1, 4)) (some (5, 1, 4)) (.next ([2250000000000], [2880000000000])
      (some (5, 1, 4)) (some (5, 1, 4)) (.next ([1995000000000], [2640000000000]) (some (5, 1, 4))
      (some (5, 1, 4)) (.next ([2250000000000], [3870000000000]) (some (5, 1, 4)) (some (5, 1, 6))
      fan16Owner4Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded16_5 : ExcludedOn (model16.B 5 ++ [step16.q]) 9000000000000 (model16.caps 5)
    (model16.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_6 : ExcludedOn (model16.B 6 ++ [step16.q]) 9000000000000 (model16.caps 6)
    (model16.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_7 : ExcludedOn (model16.B 7 ++ [step16.q]) 9000000000000 (model16.caps 7)
    (model16.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_8 : ExcludedOn (model16.B 8 ++ [step16.q]) 9000000000000 (model16.caps 8)
    (model16.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded16_9 : ExcludedOn (model16.B 9 ++ [step16.q]) 9000000000000 (model16.caps 9)
    (model16.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked16 : StepValid model16 9000000000000 step16 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded16_0
    · exact excluded16_1
    · exact excluded16_2
    · exact (hj rfl).elim
    · exact excluded16_4
    · exact excluded16_5
    · exact excluded16_6
    · exact excluded16_7
    · exact excluded16_8
    · exact excluded16_9
theorem next16 : model16.insert step16 = model17 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded17_0 : ExcludedOn (model17.B 0 ++ [step17.q]) 9000000000000 (model17.caps 0)
    (model17.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_1 : ExcludedOn (model17.B 1 ++ [step17.q]) 9000000000000 (model17.caps 1)
    (model17.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_2 : ExcludedOn (model17.B 2 ++ [step17.q]) 9000000000000 (model17.caps 2)
    (model17.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6405000000000, 9000000000000], [3360000000000,
      -9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1530000000000, 9000000000000],
      [1530000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4875000000000],
      [4890000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([3345000000000, -9000000000000],
      [4890000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([0, 0], [1530000000000,
      9000000000000]) (some (0, 3, 1)) (some (3, 3, 1)) (.next ([-3360000000000, 9000000000000],
      [9765000000000, 0]) (some (3, 3, 1)) (some (3, 3, 2)) (.next ([-1530000000000,
      -9000000000000], [3060000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4890000000000], [9765000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4890000000000,
      0], [8235000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_4 : ExcludedOn (model17.B 4 ++ [step17.q]) 9000000000000 (model17.caps 4)
    (model17.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [171000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([4125000000000], [231000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([8235000000000], [996000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([4110000000000], [765000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([4410000000000],
      [825000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next ([5355000000000], [1005000000000])
      (some (6, 1, 2)) (some (6, 1, 2)) (.next ([945000000000], [180000000000]) (some (6, 1, 2))
      (some (6, 1, 6)) (.next ([1245000000000], [240000000000]) (some (6, 1, 6)) (some (6, 1, 6))
      (.next ([300000000000], [60000000000]) (some (6, 1, 6)) (some (6, 1, 6)) (.next
      ([3780000000000, 9000000000000], [1350000000000, -9000000000000]) (some (6, 1, 6)) (some (6,
      1, 6)) (.next ([4125000000000], [2580000000000, -9000000000000]) (some (6, 1, 6)) (some (6, 1,
      6)) (.next ([2655000000000, 9000000000000], [2295000000000, -9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([4125000000000], [4110000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([2295000000000, 9000000000000], [2595000000000, -9000000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2250000000000], [2880000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan17Owner4Part0)))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded17_5 : ExcludedOn (model17.B 5 ++ [step17.q]) 9000000000000 (model17.caps 5)
    (model17.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_6 : ExcludedOn (model17.B 6 ++ [step17.q]) 9000000000000 (model17.caps 6)
    (model17.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_7 : ExcludedOn (model17.B 7 ++ [step17.q]) 9000000000000 (model17.caps 7)
    (model17.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_8 : ExcludedOn (model17.B 8 ++ [step17.q]) 9000000000000 (model17.caps 8)
    (model17.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded17_9 : ExcludedOn (model17.B 9 ++ [step17.q]) 9000000000000 (model17.caps 9)
    (model17.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked17 : StepValid model17 9000000000000 step17 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded17_0
    · exact excluded17_1
    · exact excluded17_2
    · exact (hj rfl).elim
    · exact excluded17_4
    · exact excluded17_5
    · exact excluded17_6
    · exact excluded17_7
    · exact excluded17_8
    · exact excluded17_9
theorem next17 : model17.insert step17 = model18 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded18_0 : ExcludedOn (model18.B 0 ++ [step18.q]) 9000000000000 (model18.caps 0)
    (model18.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6825000000000], [60000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([1260000000000], [135000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([7995000000000], [870000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([7875000000000], [1050000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([6495000000000],
      [885000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([6315000000000], [945000000000])
      (some (5, 6, 2)) (some (5, 6, 2)) (.next ([5745000000000], [1260000000000]) (some (5, 6, 2))
      (some (5, 6, 2)) (.next ([5565000000000], [1320000000000]) (some (5, 6, 2)) (some (5, 6, 2))
      (.next ([375000000000], [375000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next
      ([375000000000], [510000000000]) (some (5, 6, 2)) (some (5, 6, 2)) (.next ([60000000000],
      [120000000000]) (some (0, 6, 2)) (some (0, 6, 2)) fan18Owner0Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_1 : ExcludedOn (model18.B 1 ++ [step18.q]) 9000000000000 (model18.caps 1)
    (model18.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_2 : ExcludedOn (model18.B 2 ++ [step18.q]) 9000000000000 (model18.caps 2)
    (model18.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_3 : ExcludedOn (model18.B 3 ++ [step18.q]) 9000000000000 (model18.caps 3)
    (model18.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_4 : ExcludedOn (model18.B 4 ++ [step18.q]) 9000000000000 (model18.caps 4)
    (model18.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [171000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([4125000000000], [231000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([6990000000000], [510000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([945000000000], [180000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1245000000000],
      [240000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([300000000000], [60000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) (.next ([1869000000000], [510000000000]) (some (5, 1, 6)) (some
      (5, 1, 6)) (.next ([3780000000000, 9000000000000], [1350000000000, -9000000000000]) (some (5,
      1, 6)) (some (5, 6, 6)) (.next ([3615000000000], [2610000000000]) (some (5, 6, 6)) (some (5,
      6, 6)) (.next ([3315000000000], [2550000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([2655000000000, 9000000000000], [2295000000000, -9000000000000]) (some (5, 6, 4)) (some (5,
      6, 4)) (.next ([2370000000000], [2370000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([2295000000000, 9000000000000], [2595000000000, -9000000000000]) (some (5, 6, 4)) (some (5,
      6, 4)) (.next ([2250000000000], [2880000000000]) (some (5, 6, 4)) (some (5, 6, 4)) (.next
      ([1530000000000, 9000000000000], [5121000000000]) (some (5, 6, 4)) (some (5, 6, 4))
      fan18Owner4Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded18_6 : ExcludedOn (model18.B 6 ++ [step18.q]) 9000000000000 (model18.caps 6)
    (model18.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_7 : ExcludedOn (model18.B 7 ++ [step18.q]) 9000000000000 (model18.caps 7)
    (model18.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_8 : ExcludedOn (model18.B 8 ++ [step18.q]) 9000000000000 (model18.caps 8)
    (model18.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded18_9 : ExcludedOn (model18.B 9 ++ [step18.q]) 9000000000000 (model18.caps 9)
    (model18.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked18 : StepValid model18 9000000000000 step18 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded18_0
    · exact excluded18_1
    · exact excluded18_2
    · exact excluded18_3
    · exact excluded18_4
    · exact (hj rfl).elim
    · exact excluded18_6
    · exact excluded18_7
    · exact excluded18_8
    · exact excluded18_9
theorem next18 : model18.insert step18 = model19 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded19_1 : ExcludedOn (model19.B 1 ++ [step19.q]) 9000000000000 (model19.caps 1)
    (model19.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_2 : ExcludedOn (model19.B 2 ++ [step19.q]) 9000000000000 (model19.caps 2)
    (model19.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_3 : ExcludedOn (model19.B 3 ++ [step19.q]) 9000000000000 (model19.caps 3)
    (model19.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3105000000000], [120000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([7860000000000, -9000000000000], [630000000000, 9000000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) (.next ([1875000000000], [240000000000]) (some (5, 1, 6)) (some
      (5, 1, 6)) (.next ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (5,
      1, 6)) (some (5, 1, 6)) (.next ([3360000000000, -9000000000000], [765000000000,
      9000000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2460000000000, -9000000000000],
      [1020000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4260000000000], [1980000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([4380000000000], [3090000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([2880000000000], [2250000000000]) (some (5, 1, 6)) (some (5, 6, 6))
      fan19Owner3Part0)))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_4 : ExcludedOn (model19.B 4 ++ [step19.q]) 9000000000000 (model19.caps 4)
    (model19.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000], [171000000000]) (some (5, 0, 6))
      (some (5, 1, 6)) (.next ([4125000000000], [231000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([3600000000000], [375000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next
      ([945000000000], [180000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1245000000000],
      [240000000000]) (some (5, 1, 6)) (some (5, 1, 6)) (.next ([300000000000], [60000000000]) (some
      (5, 1, 6)) (some (5, 1, 6)) (.next ([3540000000000], [735000000000]) (some (5, 1, 6)) (some
      (5, 1, 6)) (.next ([3780000000000, 9000000000000], [1350000000000, -9000000000000]) (some (5,
      1, 6)) (some (5, 1, 6)) (.next ([3360000000000], [1860000000000]) (some (5, 1, 6)) (some (5,
      1, 6)) (.next ([2655000000000, 9000000000000], [2295000000000, -9000000000000]) (some (5, 1,
      6)) (some (5, 1, 6)) (.next ([2295000000000, 9000000000000], [2595000000000, -9000000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([2250000000000], [2880000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) (.next ([3369000000000], [4731000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      fan19Owner4Part0)))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_5 : ExcludedOn (model19.B 5 ++ [step19.q]) 9000000000000 (model19.caps 5)
    (model19.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6000000000000], [246000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) (.next ([8100000000000], [510000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([246000000000], [99000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([2010000000000], [5835000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([510000000000],
      [1500000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1764000000000], [5736000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1854000000000], [6510000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([1755000000000], [6855000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([1530000000000, 9000000000000], [6345000000000, 0]) (some (5, 1, 2)) (some (5, 1, 5))
      (.next ([1284000000000, 9000000000000], [6246000000000, 0]) (some (5, 1, 5)) (some (5, 1, 5))
      (.next ([1020000000000, 9000000000000], [7080000000000, -9000000000000]) (some (5, 1, 5))
      (some (5, 1, 5)) (.next ([0, 0], [1530000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
      5)) (.next ([-246000000000], [6246000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
      ([-510000000000], [8610000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-99000000000],
      [345000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5835000000000], [7845000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1500000000000], [2010000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([-5736000000000], [7500000000000]) (some (0, 2, 5)) (some (0, 2, 5))
      (.next ([-6510000000000], [8364000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-6855000000000], [8610000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6345000000000,
      0], [7875000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-6246000000000,
      0], [7530000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-7080000000000,
      9000000000000], [8100000000000, 0]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
      5)) (some (0, 2, 5)) (some (0, 2, 5))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded19_6 : ExcludedOn (model19.B 6 ++ [step19.q]) 9000000000000 (model19.caps 6)
    (model19.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_7 : ExcludedOn (model19.B 7 ++ [step19.q]) 9000000000000 (model19.caps 7)
    (model19.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_8 : ExcludedOn (model19.B 8 ++ [step19.q]) 9000000000000 (model19.caps 8)
    (model19.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded19_9 : ExcludedOn (model19.B 9 ++ [step19.q]) 9000000000000 (model19.caps 9)
    (model19.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked19 : StepValid model19 9000000000000 step19 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded19_1
    · exact excluded19_2
    · exact excluded19_3
    · exact excluded19_4
    · exact excluded19_5
    · exact excluded19_6
    · exact excluded19_7
    · exact excluded19_8
    · exact excluded19_9
theorem next19 : model19.insert step19 = model20 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded20_0 : ExcludedOn (model20.B 0 ++ [step20.q]) 9000000000000 (model20.caps 0)
    (model20.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_1 : ExcludedOn (model20.B 1 ++ [step20.q]) 9000000000000 (model20.caps 1)
    (model20.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_2 : ExcludedOn (model20.B 2 ++ [step20.q]) 9000000000000 (model20.caps 2)
    (model20.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_3 : ExcludedOn (model20.B 3 ++ [step20.q]) 9000000000000 (model20.caps 3)
    (model20.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3105000000000], [120000000000]) (some (4, 6, 3))
      (some (6, 6, 3)) (.next ([1875000000000], [240000000000]) (some (6, 6, 3)) (some (6, 6, 3))
      (.next ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (6, 6, 3)) (some
      (6, 6, 3)) (.next ([5010000000000], [1125000000000]) (some (6, 6, 3)) (some (6, 6, 3)) (.next
      ([3360000000000, -9000000000000], [765000000000, 9000000000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([2460000000000, -9000000000000], [1020000000000]) (some (6, 1, 3)) (some (6, 1,
      3)) (.next ([5130000000000], [2235000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      fan20Owner3Part0))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded20_4 : ExcludedOn (model20.B 4 ++ [step20.q]) 9000000000000 (model20.caps 4)
    (model20.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_5 : ExcludedOn (model20.B 5 ++ [step20.q]) 9000000000000 (model20.caps 5)
    (model20.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_6 : ExcludedOn (model20.B 6 ++ [step20.q]) 9000000000000 (model20.caps 6)
    (model20.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_7 : ExcludedOn (model20.B 7 ++ [step20.q]) 9000000000000 (model20.caps 7)
    (model20.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded20_9 : ExcludedOn (model20.B 9 ++ [step20.q]) 9000000000000 (model20.caps 9)
    (model20.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked20 : StepValid model20 9000000000000 step20 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded20_0
    · exact excluded20_1
    · exact excluded20_2
    · exact excluded20_3
    · exact excluded20_4
    · exact excluded20_5
    · exact excluded20_6
    · exact excluded20_7
    · exact (hj rfl).elim
    · exact excluded20_9
theorem next20 : model20.insert step20 = model21 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded21_0 : ExcludedOn (model21.B 0 ++ [step21.q]) 9000000000000 (model21.caps 0)
    (model21.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_1 : ExcludedOn (model21.B 1 ++ [step21.q]) 9000000000000 (model21.caps 1)
    (model21.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_2 : ExcludedOn (model21.B 2 ++ [step21.q]) 9000000000000 (model21.caps 2)
    (model21.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_3 : ExcludedOn (model21.B 3 ++ [step21.q]) 9000000000000 (model21.caps 3)
    (model21.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3105000000000], [120000000000]) (some (4, 6, 6))
      (some (5, 6, 6)) (.next ([1875000000000], [240000000000]) (some (5, 6, 6)) (some (5, 6, 6))
      (.next ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (5, 6, 6)) (some
      (5, 6, 6)) (.next ([3540000000000], [750000000000]) (some (5, 6, 6)) (some (5, 6, 6)) (.next
      ([3360000000000, -9000000000000], [765000000000, 9000000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([2460000000000, -9000000000000], [1020000000000]) (some (5, 6, 3)) (some (5, 6,
      3)) (.next ([5835000000000, 9000000000000], [3345000000000, -9000000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) (.next ([2880000000000], [2250000000000]) (some (5, 6, 3)) (some (5, 6, 3))
      (.next ([1530000000000, 9000000000000], [1530000000000, 9000000000000]) (some (5, 6, 3)) (some
      (5, 6, 3)) (.next ([2295000000000, 9000000000000], [2595000000000, -9000000000000]) (some (5,
      6, 3)) (some (5, 6, 3)) (.next ([4305000000000], [4875000000000]) (some (5, 6, 3)) (some (5,
      6, 4)) fan21Owner3Part0)))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded21_5 : ExcludedOn (model21.B 5 ++ [step21.q]) 9000000000000 (model21.caps 5)
    (model21.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_6 : ExcludedOn (model21.B 6 ++ [step21.q]) 9000000000000 (model21.caps 6)
    (model21.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_7 : ExcludedOn (model21.B 7 ++ [step21.q]) 9000000000000 (model21.caps 7)
    (model21.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_8 : ExcludedOn (model21.B 8 ++ [step21.q]) 9000000000000 (model21.caps 8)
    (model21.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded21_9 : ExcludedOn (model21.B 9 ++ [step21.q]) 9000000000000 (model21.caps 9)
    (model21.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked21 : StepValid model21 9000000000000 step21 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded21_0
    · exact excluded21_1
    · exact excluded21_2
    · exact excluded21_3
    · exact (hj rfl).elim
    · exact excluded21_5
    · exact excluded21_6
    · exact excluded21_7
    · exact excluded21_8
    · exact excluded21_9
theorem next21 : model21.insert step21 = model22 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded22_0 : ExcludedOn (model22.B 0 ++ [step22.q]) 9000000000000 (model22.caps 0)
    (model22.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_1 : ExcludedOn (model22.B 1 ++ [step22.q]) 9000000000000 (model22.caps 1)
    (model22.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_2 : ExcludedOn (model22.B 2 ++ [step22.q]) 9000000000000 (model22.caps 2)
    (model22.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_3 : ExcludedOn (model22.B 3 ++ [step22.q]) 9000000000000 (model22.caps 3)
    (model22.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3105000000000], [120000000000]) (some (4, 6, 6))
      (some (5, 6, 6)) (.next ([1875000000000], [240000000000]) (some (5, 6, 6)) (some (5, 6, 6))
      (.next ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (5, 6, 6)) (some
      (5, 6, 6)) (.next ([3360000000000, -9000000000000], [765000000000, 9000000000000]) (some (5,
      6, 6)) (some (5, 6, 6)) (.next ([2460000000000, -9000000000000], [1020000000000]) (some (5, 6,
      6)) (some (5, 6, 3)) (.next ([5940000000000, 9000000000000], [3501000000000, -9000000000000])
      (some (5, 6, 3)) (some (5, 6, 3)) (.next ([2880000000000], [2250000000000]) (some (5, 6, 3))
      (some (5, 6, 3)) fan22Owner3Part0))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded22_5 : ExcludedOn (model22.B 5 ++ [step22.q]) 9000000000000 (model22.caps 5)
    (model22.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_6 : ExcludedOn (model22.B 6 ++ [step22.q]) 9000000000000 (model22.caps 6)
    (model22.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_7 : ExcludedOn (model22.B 7 ++ [step22.q]) 9000000000000 (model22.caps 7)
    (model22.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_8 : ExcludedOn (model22.B 8 ++ [step22.q]) 9000000000000 (model22.caps 8)
    (model22.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded22_9 : ExcludedOn (model22.B 9 ++ [step22.q]) 9000000000000 (model22.caps 9)
    (model22.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked22 : StepValid model22 9000000000000 step22 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded22_0
    · exact excluded22_1
    · exact excluded22_2
    · exact excluded22_3
    · exact (hj rfl).elim
    · exact excluded22_5
    · exact excluded22_6
    · exact excluded22_7
    · exact excluded22_8
    · exact excluded22_9
theorem next22 : model22.insert step22 = model23 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded23_0 : ExcludedOn (model23.B 0 ++ [step23.q]) 9000000000000 (model23.caps 0)
    (model23.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_1 : ExcludedOn (model23.B 1 ++ [step23.q]) 9000000000000 (model23.caps 1)
    (model23.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_3 : ExcludedOn (model23.B 3 ++ [step23.q]) 9000000000000 (model23.caps 3)
    (model23.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3105000000000], [120000000000]) (some (4, 1, 6))
      (some (5, 1, 6)) (.next ([1875000000000], [240000000000]) (some (5, 1, 6)) (some (5, 1, 6))
      (.next ([4410000000000, 9000000000000], [720000000000, -9000000000000]) (some (5, 1, 6)) (some
      (5, 1, 6)) (.next ([3360000000000, -9000000000000], [765000000000, 9000000000000]) (some (5,
      1, 6)) (some (5, 1, 6)) (.next ([5235000000000], [1530000000000, 9000000000000]) (some (5, 1,
      6)) (some (5, 1, 6)) fan23Owner3Part0))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded23_4 : ExcludedOn (model23.B 4 ++ [step23.q]) 9000000000000 (model23.caps 4)
    (model23.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_5 : ExcludedOn (model23.B 5 ++ [step23.q]) 9000000000000 (model23.caps 5)
    (model23.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_6 : ExcludedOn (model23.B 6 ++ [step23.q]) 9000000000000 (model23.caps 6)
    (model23.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_7 : ExcludedOn (model23.B 7 ++ [step23.q]) 9000000000000 (model23.caps 7)
    (model23.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_8 : ExcludedOn (model23.B 8 ++ [step23.q]) 9000000000000 (model23.caps 8)
    (model23.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded23_9 : ExcludedOn (model23.B 9 ++ [step23.q]) 9000000000000 (model23.caps 9)
    (model23.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked23 : StepValid model23 9000000000000 step23 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded23_0
    · exact excluded23_1
    · exact (hj rfl).elim
    · exact excluded23_3
    · exact excluded23_4
    · exact excluded23_5
    · exact excluded23_6
    · exact excluded23_7
    · exact excluded23_8
    · exact excluded23_9
theorem next23 : model23.insert step23 = model24 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext170000180000
end ConwaySoifer.Simplified.Certificates

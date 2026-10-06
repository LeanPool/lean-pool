/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext330000340000
import Mathlib.Tactic.FinCases

/-!
# Sext 330000 340000 3

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
namespace Sext330000340000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner4Part0 : FanWitness := (.next ([0], [3405000000000]) (some (6, 7, 3)) (some (6, 7, 3))
    (.next ([-30000000000], [5970000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next
    ([-1155000000000], [6501000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-915000000000],
    [4290000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-1545000000000], [5835000000000])
    (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-1920000000000], [6598875000000]) (some (0, 7, 3))
    (some (0, 7, 3)) (.next ([-2460000000000], [8400000000000]) (some (0, 7, 3)) (some (0, 7, 3))
    (.next ([-915000000000], [2565000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next
    ([-3585000000000], [8931000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-2565000000000],
    [5940000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-4350000000000], [9028875000000])
    (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-3405000000000], [6780000000000]) (some (0, 7, 3))
    (some (0, 7, 3)) (.next ([-594000000000], [1125000000000]) (some (0, 7, 3)) (some (0, 7, 3))
    (.next ([-3096000000000], [5346000000000]) (some (0, 7, 3)) (some (0, 7, 4)) (.next
    ([-5835000000000], [9210000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-2040000000000],
    [3096000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-1261125000000], [1890000000000])
    (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-3193875000000], [4678875000000]) (some (0, 7, 4))
    (some (0, 7, 4)) (.next ([-2565000000000], [3375000000000]) (some (0, 7, 4)) (some (0, 7, 4))
    (.next ([-3405000000000], [4290000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-667125000000], [765000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-1971000000000],
    [2250000000000]) (some (0, 7, 4)) (some (0, 7, 5)) (.next ([-1303875000000], [1485000000000])
    (some (0, 7, 5)) (some (0, 7, 5)) (.next ([-2805000000000], [3193875000000]) (some (0, 7, 5))
    (some (0, 7, 6)) (.terminal (some (0, 7, 6)) (some (0, 7, 6)) (some (0, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner4Part0 : FanWitness := (.next ([-1155000000000], [6501000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-915000000000], [4290000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-1080000000000], [4020000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-1920000000000], [6598875000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1674000000000],
    [5145000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-915000000000], [2565000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-2341125000000], [5910000000000]) (some (0, 1, 3))
    (some (0, 1, 3)) (.next ([-3030000000000], [7020000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-2565000000000], [5940000000000]) (some (0, 1, 3)) (some (0, 7, 3)) (.next
    ([-3645000000000], [7395000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-3405000000000],
    [6780000000000]) (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-594000000000], [1125000000000])
    (some (0, 7, 3)) (some (0, 7, 3)) (.next ([-3096000000000], [5346000000000]) (some (0, 7, 3))
    (some (0, 7, 4)) (.next ([-2040000000000], [3096000000000]) (some (0, 7, 4)) (some (0, 7, 4))
    (.next ([-1261125000000], [1890000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next
    ([-3193875000000], [4678875000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-2565000000000],
    [3375000000000]) (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-3405000000000], [4290000000000])
    (some (0, 7, 4)) (some (0, 7, 4)) (.next ([-667125000000], [765000000000]) (some (0, 7, 4))
    (some (0, 7, 4)) (.next ([-1971000000000], [2250000000000]) (some (0, 7, 4)) (some (0, 7, 5))
    (.next ([-1303875000000], [1485000000000]) (some (0, 7, 5)) (some (0, 7, 5)) (.next
    ([-2805000000000], [3193875000000]) (some (0, 7, 5)) (some (0, 7, 6)) (.next ([-2730000000000],
    [3105000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-7020000000000], [7395000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.terminal (some (0, 7, 6)) (some (0, 7, 6)) (some (0, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner4Part1 : FanWitness := (.next ([2940000000000], [1080000000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([4678875000000], [1920000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([3471000000000], [1674000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([1650000000000], [915000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3568875000000],
    [2341125000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3990000000000], [3030000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3375000000000], [2565000000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([3750000000000], [3645000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([3375000000000], [3405000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([531000000000], [594000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2250000000000],
    [3096000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1056000000000], [2040000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([628875000000], [1261125000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([1485000000000], [3193875000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([810000000000], [2565000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([885000000000], [3405000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([97875000000],
    [667125000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([279000000000], [1971000000000]) (some
    (6, 1, 7)) (some (6, 1, 7)) (.next ([181125000000], [1303875000000]) (some (6, 1, 7)) (some (6,
    1, 7)) (.next ([388875000000], [2805000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([375000000000], [2730000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([375000000000],
    [7020000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([0], [3405000000000]) (some (6, 1,
    7)) (some (6, 1, 7)) (.next ([-30000000000], [5970000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    fan26Owner4Part0))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner2Part0 : FanWitness := (.next ([2115000000000], [135000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([5220000000000, 9000000000000], [990000000000, -9000000000000]) (some (0, 5,
    3)) (some (0, 5, 3)) (.next ([3240000000000, -9000000000000], [720000000000, 9000000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([5700000000000, 9000000000000], [3300000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2595000000000], [2445000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2970000000000, 9000000000000], [2970000000000,
    9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2250000000000], [3960000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([2730000000000], [6270000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([990000000000, -9000000000000], [2835000000000, 9000000000000]) (some
    (0, 5, 3)) (some (0, 5, 3)) (.next ([480000000000], [2310000000000]) (some (0, 5, 3)) (some (0,
    5, 3)) (.next ([135000000000], [3825000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([0,
    0], [2970000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-240000000000,
    -9000000000000], [6270000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-135000000000],
    [2250000000000]) (some (0, 5, 4)) (some (5, 5, 4)) (.next ([-990000000000, 9000000000000],
    [6210000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-720000000000, -9000000000000],
    [3960000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-3300000000000, 9000000000000],
    [9000000000000, 0]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-2445000000000], [5040000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2970000000000, -9000000000000], [5940000000000,
    18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3960000000000], [6210000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-6270000000000], [9000000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-2835000000000, -9000000000000], [3825000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-2310000000000], [2790000000000]) (some (5, 3, 4)) (some (5, 3, 4))
    (.next ([-3825000000000], [3960000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.terminal (some
    (5, 3, 4)) (some (5, 3, 0)) (some (5, 3, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part0 : FanWitness := (.next ([-165000000000], [3060000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-1155000000000], [6501000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-915000000000], [4290000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-1920000000000], [6598875000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-2730000000000],
    [9000000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-915000000000], [2565000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-2565000000000], [5940000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-3405000000000], [6780000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-594000000000], [1125000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next
    ([-3096000000000], [5346000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-2730000000000],
    [4710000000000]) (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-2040000000000], [3096000000000])
    (some (0, 1, 7)) (some (0, 1, 7)) (.next ([-1261125000000], [1890000000000]) (some (0, 1, 7))
    (some (0, 1, 7)) (.next ([-6135000000000], [9000000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    (.next ([-3193875000000], [4678875000000]) (some (0, 1, 7)) (some (0, 7, 7)) (.next
    ([-2565000000000], [3375000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-3405000000000],
    [4290000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-667125000000], [765000000000])
    (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-1971000000000], [2250000000000]) (some (0, 7, 7))
    (some (0, 7, 7)) (.next ([-1303875000000], [1485000000000]) (some (0, 7, 7)) (some (0, 7, 7))
    (.next ([-2805000000000], [3193875000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next
    ([-5625000000000], [6270000000000]) (some (0, 7, 7)) (some (0, 7, 7)) (.next ([-4321125000000],
    [4785000000000]) (some (0, 7, 6)) (some (0, 7, 6)) (.next ([-3654000000000], [4020000000000])
    (some (0, 7, 6)) (some (0, 7, 6)) (.terminal (some (0, 7, 6)) (some (0, 7, 6)) (some (0, 7,
    6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan28Owner4Part1 : FanWitness := (.next ([3375000000000], [915000000000]) (some (6, 1, 7)) (some
    (6, 1, 7)) (.next ([4678875000000], [1920000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([6270000000000], [2730000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1650000000000],
    [915000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3375000000000], [2565000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([3375000000000], [3405000000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([531000000000], [594000000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([2250000000000], [3096000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([1980000000000], [2730000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([1056000000000],
    [2040000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([628875000000], [1261125000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([2865000000000], [6135000000000]) (some (6, 1, 7))
    (some (6, 1, 7)) (.next ([1485000000000], [3193875000000]) (some (6, 1, 7)) (some (6, 1, 7))
    (.next ([810000000000], [2565000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([885000000000], [3405000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([97875000000],
    [667125000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([279000000000], [1971000000000]) (some
    (6, 1, 7)) (some (6, 1, 7)) (.next ([181125000000], [1303875000000]) (some (6, 1, 7)) (some (6,
    1, 7)) (.next ([388875000000], [2805000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next
    ([645000000000], [5625000000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([463875000000],
    [4321125000000]) (some (6, 1, 7)) (some (6, 1, 7)) (.next ([366000000000], [3654000000000])
    (some (6, 1, 7)) (some (6, 1, 7)) (.next ([0], [3405000000000]) (some (6, 1, 7)) (some (6, 1,
    7)) (.next ([-30000000000], [5970000000000]) (some (0, 1, 7)) (some (0, 1, 7))
    fan28Owner4Part0))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (283) (528) (52800) (.witnessedFan (.next ([2115000000000],
      [135000000000]) (some (0, 1, 3)) (some (5, 1, 3)) (.next ([5220000000000, 9000000000000],
      [990000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3240000000000,
      -9000000000000], [720000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([3105000000000, 9000000000000], [855000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([3825000000000], [1275000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([2970000000000, 9000000000000], [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([2970000000000, 9000000000000], [5235000000000, 0]) (some (5, 1, 3)) (some (5, 1,
      3)) (.next ([990000000000, -9000000000000], [2835000000000, 9000000000000]) (some (5, 1, 3))
      (some (5, 1, 3)) (.next ([975000000000], [2985000000000]) (some (5, 1, 3)) (some (5, 1, 3))
      (.next ([135000000000], [3825000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0],
      [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([-135000000000],
      [2250000000000]) (some (5, 1, 3)) (some (5, 1, 4)) (.next ([-990000000000, 9000000000000],
      [6210000000000, 0]) (some (5, 1, 4)) (some (5, 2, 4)) (.next ([-720000000000, -9000000000000],
      [3960000000000]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-855000000000, 9000000000000],
      [3960000000000, 0]) (some (5, 2, 4)) (some (5, 2, 4)) (.next ([-1275000000000],
      [5100000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next ([-2970000000000, -9000000000000],
      [5940000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-5235000000000,
      0], [8205000000000, 9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2835000000000,
      -9000000000000], [3825000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2985000000000],
      [3960000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3825000000000], [3960000000000])
      (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some (1, 3, 4)) (some (1, 3, 0)) (some (1, 3,
      4))))))))))))))))))))))))) (.witnessedFan (.next ([2115000000000], [135000000000]) (some (0,
      1, 3)) (some (5, 1, 3)) (.next ([5220000000000, 9000000000000], [990000000000,
      -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3105000000000, 9000000000000],
      [855000000000, -9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([3825000000000],
      [1275000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2970000000000, 9000000000000],
      [2970000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2970000000000,
      9000000000000], [5235000000000, 0]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([2250000000000],
      [3960000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([975000000000], [2985000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([990000000000, -9000000000000], [2835000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([135000000000], [3825000000000])
      (some (5, 1, 3)) (some (5, 1, 3)) (.next ([0, 0], [2970000000000, 9000000000000]) (some (5, 1,
      3)) (some (5, 1, 3)) (.next ([-135000000000], [2250000000000]) (some (5, 1, 3)) (some (5, 1,
      4)) (.next ([-990000000000, 9000000000000], [6210000000000, 0]) (some (5, 1, 4)) (some (5, 2,
      4)) (.next ([-855000000000, 9000000000000], [3960000000000, 0]) (some (5, 2, 4)) (some (5, 2,
      4)) (.next ([-1275000000000], [5100000000000]) (some (5, 2, 4)) (some (5, 3, 4)) (.next
      ([-2970000000000, -9000000000000], [5940000000000, 18000000000000]) (some (5, 3, 4)) (some (5,
      3, 4)) (.next ([-5235000000000, 0], [8205000000000, 9000000000000]) (some (5, 3, 4)) (some (5,
      3, 4)) (.next ([-3960000000000], [6210000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next
      ([-2985000000000], [3960000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-2835000000000,
      -9000000000000], [3825000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.next ([-3825000000000],
      [3960000000000]) (some (1, 3, 4)) (some (1, 3, 4)) (.terminal (some (1, 3, 4)) (some (1, 3,
      0)) (some (1, 3, 4)))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_9 : ExcludedOn (model24.B 9 ++ [step24.q]) 9000000000000 (model24.caps 9)
    (model24.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked24 : StepValid model24 9000000000000 step24 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded24_0
    · exact excluded24_1
    · exact excluded24_2
    · exact (hj rfl).elim
    · exact excluded24_4
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5940000000000], [30000000000]) (some (6, 0, 7))
      (some (6, 7, 7)) (.next ([5346000000000], [1155000000000]) (some (6, 7, 7)) (some (6, 7, 7))
      (.next ([3375000000000], [915000000000]) (some (6, 7, 7)) (some (6, 7, 7)) (.next
      ([4290000000000], [1545000000000]) (some (6, 7, 7)) (some (6, 7, 7)) (.next ([4678875000000],
      [1920000000000]) (some (6, 7, 2)) (some (6, 7, 2)) (.next ([5940000000000], [2460000000000])
      (some (6, 7, 2)) (some (6, 7, 2)) (.next ([1650000000000], [915000000000]) (some (6, 7, 2))
      (some (6, 7, 2)) (.next ([5346000000000], [3585000000000]) (some (6, 7, 2)) (some (6, 7, 3))
      (.next ([3375000000000], [2565000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
      ([4678875000000], [4350000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([3375000000000],
      [3405000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([531000000000], [594000000000])
      (some (6, 7, 3)) (some (6, 7, 3)) (.next ([2250000000000], [3096000000000]) (some (6, 7, 3))
      (some (6, 7, 3)) (.next ([3375000000000], [5835000000000]) (some (6, 7, 3)) (some (6, 7, 3))
      (.next ([1056000000000], [2040000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
      ([628875000000], [1261125000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([1485000000000],
      [3193875000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([810000000000], [2565000000000])
      (some (6, 7, 3)) (some (6, 7, 3)) (.next ([885000000000], [3405000000000]) (some (6, 7, 3))
      (some (6, 7, 3)) (.next ([97875000000], [667125000000]) (some (6, 7, 3)) (some (6, 7, 3))
      (.next ([279000000000], [1971000000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next
      ([181125000000], [1303875000000]) (some (6, 7, 3)) (some (6, 7, 3)) (.next ([388875000000],
      [2805000000000]) (some (6, 7, 3)) (some (6, 7, 3)) fan25Owner4Part0))))))))))))))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_9 : ExcludedOn (model25.B 9 ++ [step25.q]) 9000000000000 (model25.caps 9)
    (model25.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked25 : StepValid model25 9000000000000 step25 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded25_0
    · exact excluded25_1
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact (hj rfl).elim
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5205000000000], [2190000000000]) (some (2, 0,
      4)) (some (3, 0, 4)) (.next ([1980000000000], [1155000000000]) (some (3, 0, 4)) (some (3, 4,
      4)) (.next ([5745000000000], [3630000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next
      ([3765000000000], [2475000000000]) (some (3, 4, 1)) (some (3, 4, 1)) (.next ([3765000000000],
      [4170000000000]) (some (3, 4, 1)) (some (3, 4, 2)) (.next ([2070000000000], [4170000000000])
      (some (3, 4, 2)) (some (3, 4, 2)) (.next ([1980000000000], [7395000000000]) (some (3, 4, 2))
      (some (3, 4, 2)) (.next ([0], [4170000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([-2190000000000], [7395000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-1155000000000], [3135000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-3630000000000], [9375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-2475000000000], [6240000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4170000000000], [7935000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4170000000000], [6240000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-7395000000000], [9375000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4,
      2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5940000000000], [30000000000]) (some (6, 0, 7))
      (some (6, 1, 7)) (.next ([5346000000000], [1155000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([3375000000000], [915000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      fan26Owner4Part1))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [795000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([7020000000000], [1605000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([3165000000000], [4545000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2370000000000], [4545000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2475000000000],
      [5355000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2475000000000], [6150000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1560000000000], [5460000000000]) (some (4, 1, 2))
      (some (4, 1, 4)) (.next ([0], [3165000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-795000000000], [4545000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-1605000000000],
      [8625000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4545000000000], [7710000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4545000000000], [6915000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-5355000000000], [7830000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-6150000000000], [8625000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-5460000000000], [7020000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked26 : StepValid model26 9000000000000 step26 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded26_1
    · exact excluded26_2
    · exact excluded26_3
    · exact excluded26_4
    · exact excluded26_5
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3750000000000], [2190000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([2970000000000, 9000000000000], [2970000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([3750000000000], [5160000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([780000000000, -9000000000000], [8130000000000,
      9000000000000]) (some (0, 3, 2)) none (.next ([0, 0], [2970000000000, 9000000000000]) none
      none (.next ([-2190000000000, 9000000000000], [5940000000000, -9000000000000]) none none
      (.next ([-2970000000000, -9000000000000], [5940000000000, 18000000000000]) (some (3, 1, 0))
      (some (3, 1, 0)) (.next ([-5160000000000], [8910000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.next ([-8130000000000, -9000000000000], [8910000000000, 0]) (some (3, 1, 0)) (some (3, 1,
      0)) (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8415000000000], [675000000000]) (some (4, 0, 4))
      (some (4, 1, 4)) (.next ([3750000000000], [795000000000]) (some (0, 1, 4)) (some (0, 1, 4))
      (.next ([5250000000000], [3840000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([3165000000000], [4545000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([2370000000000],
      [4545000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next ([1500000000000], [3045000000000])
      (some (0, 1, 4)) (some (0, 1, 4)) (.next ([705000000000], [3840000000000]) (some (0, 1, 4))
      (some (0, 1, 4)) (.next ([0], [3165000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-675000000000], [9090000000000]) (some (0, 1, 4)) (some (0, 2, 4)) (.next ([-795000000000],
      [4545000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3840000000000], [9090000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-4545000000000], [7710000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-4545000000000], [6915000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-3045000000000], [4545000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-3840000000000], [4545000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.terminal (some (0, 2,
      4)) (some (0, 4, 4)) (some (0, 4, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3060000000000, 9000000000000], [780000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3750000000000], [2190000000000,
      -9000000000000]) (some (2, 0, 2)) (some (2, 0, 2)) (.next ([2970000000000, 9000000000000],
      [6030000000000, -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([90000000000],
      [3750000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2970000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-780000000000, 9000000000000],
      [3840000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2190000000000, 9000000000000],
      [5940000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6030000000000,
      9000000000000], [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3750000000000], [3840000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
    · exact excluded27_4
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact excluded27_8
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6030000000000, -9000000000000], [240000000000,
      9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) fan28Owner2Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3765000000000], [2475000000000]) (some (2, 0,
      4)) (some (3, 0, 4)) (.next ([3765000000000], [2505000000000]) (some (3, 0, 4)) (some (3, 0,
      4)) (.next ([3765000000000], [4170000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([2100000000000], [4170000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2070000000000],
      [4170000000000]) (some (3, 0, 2)) (some (3, 4, 2)) (.next ([0], [4170000000000]) (some (3, 4,
      2)) (some (3, 4, 2)) (.next ([-2475000000000], [6240000000000]) (some (0, 4, 2)) (some (0, 4,
      2)) (.next ([-2505000000000], [6270000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4170000000000], [7935000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4170000000000], [6270000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([-4170000000000], [6240000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.terminal (some (0, 4,
      2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5940000000000], [30000000000]) (some (6, 0, 7))
      (some (6, 1, 7)) (.next ([2895000000000], [165000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      (.next ([5346000000000], [1155000000000]) (some (6, 1, 7)) (some (6, 1, 7))
      fan28Owner4Part1))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_9 : ExcludedOn (model28.B 9 ++ [step28.q]) 9000000000000 (model28.caps 9)
    (model28.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked28 : StepValid model28 9000000000000 step28 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded28_1
    · exact excluded28_2
    · exact excluded28_3
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext330000340000
end ConwaySoifer.Simplified.Certificates

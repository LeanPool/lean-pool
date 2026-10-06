/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint120000130000
import Mathlib.Tactic.FinCases

/-!
# Sint 120000 130000 3

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
namespace Sint120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan25Owner0Part0 : FanWitness := (.next ([6870000000000], [3210000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (0,
    2, 6)) (some (0, 2, 6)) (.next ([1603200000000, 2610000000000], [8023200000000, 2610000000000])
    (some (0, 2, 6)) (some (0, 3, 6)) (.next ([976800000000, -2610000000000], [7396800000000,
    -2610000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([976800000000, -2610000000000],
    [8336400000000, 5220000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([663600000000,
    -5220000000000], [8023200000000, 2610000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([251400000000, 5220000000000], [5446800000000, -2610000000000]) (some (0, 3, 6)) (some (0, 6,
    6)) (.next ([0, 0], [939600000000, 7830000000000]) (some (0, 6, 6)) (some (0, 6, 6)) (.next
    ([-61800000000, 2610000000000], [6073200000000, 2610000000000]) (some (0, 6, 6)) (some (0, 6,
    6)) (.next ([-453600000000, 5220000000000], [5266800000000, -2610000000000]) (some (0, 6, 6))
    (some (0, 6, 6)) (.next ([-688200000000, -2610000000000], [6386400000000, 5220000000000]) (some
    (0, 6, 6)) (some (1, 6, 6)) (.next ([-766800000000, 2610000000000], [5893200000000,
    2610000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-1001400000000, -5220000000000],
    [6073200000000, 2610000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-180000000000],
    [885000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-1393200000000, -2610000000000],
    [6206400000000, 5220000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-2325000000000],
    [9375000000000]) (some (1, 6, 6)) (some (1, 6, 6)) (.next ([-1706400000000, -5220000000000],
    [5893200000000, 2610000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-3210000000000],
    [10080000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-313200000000, -2610000000000],
    [626400000000, 5220000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-8023200000000,
    -2610000000000], [9626400000000, 5220000000000]) (some (1, 6, 5)) (some (2, 6, 5)) (.next
    ([-7396800000000, 2610000000000], [8373600000000, -5220000000000]) (some (2, 6, 5)) (some (2, 6,
    5)) (.next ([-8336400000000, -5220000000000], [9313200000000, 2610000000000]) (some (2, 6, 5))
    (some (2, 6, 5)) (.next ([-8023200000000, -2610000000000], [8686800000000, -2610000000000])
    (some (2, 6, 5)) (some (2, 6, 5)) (.next ([-5446800000000, 2610000000000], [5698200000000,
    2610000000000]) (some (2, 6, 5)) (some (2, 6, 5)) (.terminal (some (2, 6, 5)) (some (2, 6, 5))
    (some (2, 6, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan27Owner5Part0 : FanWitness := (.next ([3825000000000], [855000000000]) (some (5, 1, 2)) (some
    (5, 1, 2)) (.next ([3825000000000], [1080000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
    ([3240000000000], [1080000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3015000000000],
    [1080000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2745000000000, -9000000000000],
    [1935000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2745000000000,
    -9000000000000], [2160000000000, 9000000000000]) (some (5, 1, 2)) (some (5, 1, 3)) (.next
    ([2745000000000], [5175000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([660000000000],
    [2085000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next ([1155000000000], [3825000000000])
    (some (0, 1, 3)) (some (0, 1, 3)) (.next ([1665000000000, -9000000000000], [6255000000000,
    9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([930000000000], [3825000000000]) (some
    (0, 1, 3)) (some (0, 1, 3)) (.next ([0], [5835000000000]) (some (0, 1, 3)) (some (0, 1, 3))
    (.next ([-1080000000000, -9000000000000], [6915000000000, 9000000000000]) (some (0, 1, 3)) (some
    (0, 2, 4)) (.next ([-855000000000], [4680000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
    ([-1080000000000], [4905000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1080000000000],
    [4320000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1080000000000], [4095000000000])
    (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-1935000000000, -9000000000000], [4680000000000])
    (some (0, 2, 4)) (some (0, 2, 5)) (.next ([-2160000000000, -9000000000000], [4905000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5175000000000], [7920000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-2085000000000], [2745000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-3825000000000], [4980000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-6255000000000, -9000000000000], [7920000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-3825000000000], [4755000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2,
    5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan31Owner6Part0 : FanWitness := (.next ([1875000000000], [540000000000]) (some (0, 5, 4)) (some
    (0, 5, 4)) (.next ([870000000000], [255000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([750000000000, 0], [330000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([5760000000000], [3240000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([4680000000000,
    -9000000000000], [3240000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([5760000000000],
    [4320000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([1080000000000,
    9000000000000], [1080000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([3600000000000], [3990000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([3345000000000],
    [5115000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([750000000000], [1410000000000])
    (some (0, 5, 4)) (some (5, 5, 4)) (.next ([540000000000, 9000000000000], [1335000000000,
    -9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([0, 0], [1080000000000,
    9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-330000000000, -9000000000000],
    [2490000000000, 9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-540000000000],
    [2415000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-255000000000], [1125000000000])
    (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-330000000000, 9000000000000], [1080000000000,
    -9000000000000]) (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-3240000000000], [9000000000000])
    (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-3240000000000, 0], [7920000000000, -9000000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-4320000000000, -9000000000000], [10080000000000,
    9000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1080000000000, -9000000000000],
    [2160000000000, 18000000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-3990000000000],
    [7590000000000]) (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-5115000000000], [8460000000000])
    (some (5, 3, 4)) (some (5, 3, 4)) (.next ([-1410000000000], [2160000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.next ([-1335000000000, 9000000000000], [1875000000000]) (some (5, 3, 4))
    (some (5, 3, 4)) (.terminal (some (5, 3, 4)) (some (5, 3, 0)) (some (5, 3,
    4)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2160000000000], [330000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 4)) (.next ([6060000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([1875000000000], [540000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([870000000000], [255000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([6600000000000], [2415000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([5730000000000], [2160000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([750000000000], [1410000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([540000000000, 9000000000000], [1335000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-330000000000, -9000000000000], [2490000000000, 9000000000000]) (some (0, 5, 4)) (some (0,
      5, 4)) (.next ([-1080000000000, -9000000000000], [7140000000000]) (some (0, 5, 4)) (some (0,
      5, 4)) (.next ([-540000000000], [2415000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-255000000000], [1125000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-2415000000000],
      [9015000000000]) (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-2160000000000], [7890000000000])
      (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-1080000000000, -9000000000000], [2160000000000,
      18000000000000]) (some (1, 5, 4)) (some (5, 5, 4)) (.next ([-1410000000000], [2160000000000])
      (some (5, 5, 4)) (some (5, 5, 4)) (.next ([-1335000000000, 9000000000000], [1875000000000])
      (some (5, 5, 4)) (some (5, 5, 4)) (.terminal (some (5, 5, 4)) (some (5, 3, 0)) (some (5, 5,
      0))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact excluded24_3
    · exact excluded24_4
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact (hj rfl).elim
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6011400000000, 5220000000000], [61800000000,
      -2610000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([4813200000000, 2610000000000],
      [453600000000, -5220000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([5698200000000,
      2610000000000], [688200000000, 2610000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
      ([5126400000000, 5220000000000], [766800000000, -2610000000000]) (some (5, 2, 6)) (some (5, 2,
      6)) (.next ([5071800000000, -2610000000000], [1001400000000, 5220000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) (.next ([705000000000], [180000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      (.next ([4813200000000, 2610000000000], [1393200000000, 2610000000000]) (some (0, 2, 6)) (some
      (0, 2, 6)) (.next ([7050000000000], [2325000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
      ([4186800000000, -2610000000000], [1706400000000, 5220000000000]) (some (0, 2, 6)) (some (0,
      2, 6)) fan25Owner0Part0)))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (829) (1716) (171600) (.split (0) (169) (829) (171600)
      (.witnessedFan (.next ([2160000000000], [330000000000, 9000000000000]) (some (5, 1, 3)) (some
      (5, 1, 5)) (.next ([1875000000000], [540000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
      ([870000000000], [255000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([750000000000, 0],
      [330000000000, -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([1080000000000,
      9000000000000], [1080000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next
      ([750000000000], [1410000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([795000000000,
      -9000000000000], [1620000000000, 9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([2415000000000], [5835000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([540000000000,
      9000000000000], [1335000000000, -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([2160000000000], [6960000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([1080000000000,
      9000000000000], [7710000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-330000000000,
      -9000000000000], [2490000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next
      ([-540000000000], [2415000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-255000000000],
      [1125000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-330000000000, 9000000000000],
      [1080000000000, -9000000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.next ([-1080000000000,
      -9000000000000], [2160000000000, 18000000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-1410000000000], [2160000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1620000000000,
      -9000000000000], [2415000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-5835000000000],
      [8250000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1335000000000, 9000000000000],
      [1875000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-6960000000000], [9120000000000])
      (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-7710000000000, 0], [8790000000000, 9000000000000])
      (some (1, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3, 5)) (some (1, 3, 5)) (some (1, 3,
      5))))))))))))))))))))))))))) (.witnessedFan (.next ([2160000000000], [330000000000,
      9000000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next ([1875000000000], [540000000000])
      (some (5, 1, 5)) (some (5, 1, 5)) (.next ([870000000000], [255000000000]) (some (5, 1, 5))
      (some (5, 1, 5)) (.next ([750000000000, 0], [330000000000, -9000000000000]) (some (5, 1, 5))
      (some (5, 1, 5)) (.next ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some
      (5, 1, 5)) (some (5, 2, 5)) (.next ([750000000000], [1410000000000]) (some (5, 2, 5)) (some
      (5, 2, 5)) (.next ([795000000000, -9000000000000], [1620000000000, 9000000000000]) (some (5,
      2, 5)) (some (5, 2, 5)) (.next ([540000000000, 9000000000000], [1335000000000,
      -9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([2415000000000], [5835000000000])
      (some (5, 2, 5)) (some (5, 2, 5)) (.next ([2160000000000], [6960000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([1080000000000, 9000000000000], [7710000000000]) (some (0, 2, 5))
      (some (0, 2, 5)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
      5)) (.next ([-330000000000, -9000000000000], [2490000000000, 9000000000000]) (some (0, 2, 5))
      (some (0, 3, 5)) (.next ([-540000000000], [2415000000000]) (some (0, 3, 5)) (some (0, 3, 5))
      (.next ([-255000000000], [1125000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-330000000000, 9000000000000], [1080000000000, -9000000000000]) (some (0, 3, 5)) (some (1,
      3, 5)) (.next ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (1, 3,
      5)) (some (1, 3, 5)) (.next ([-1410000000000], [2160000000000]) (some (1, 3, 5)) (some (1, 3,
      5)) (.next ([-1620000000000, -9000000000000], [2415000000000]) (some (1, 3, 5)) (some (1, 3,
      5)) (.next ([-1335000000000, 9000000000000], [1875000000000]) (some (1, 3, 5)) (some (1, 3,
      5)) (.next ([-5835000000000], [8250000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-6960000000000], [9120000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-7710000000000,
      0], [8790000000000, 9000000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3,
      5)) (some (1, 3, 5)) (some (1, 3, 5)))))))))))))))))))))))))))) (.split (20725) (41977)
      (42900) (4290000) (.witnessedFan (.next ([2160000000000], [330000000000, 9000000000000]) (some
      (5, 1, 3)) (some (5, 1, 5)) (.next ([1875000000000], [540000000000]) (some (5, 1, 5)) (some
      (5, 1, 5)) (.next ([870000000000], [255000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
      ([750000000000, 0], [330000000000, -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
      ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 2,
      5)) (.next ([750000000000], [1410000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next
      ([540000000000, 9000000000000], [1335000000000, -9000000000000]) (some (5, 2, 5)) (some (5, 2,
      5)) (.next ([795000000000, -9000000000000], [1620000000000, 9000000000000]) (some (5, 2, 5))
      (some (5, 2, 5)) (.next ([2415000000000], [5835000000000]) (some (5, 2, 5)) (some (5, 2, 5))
      (.next ([2160000000000], [6960000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([1080000000000, 9000000000000], [7710000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([0, 0], [1080000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
      ([-330000000000, -9000000000000], [2490000000000, 9000000000000]) (some (0, 2, 5)) (some (0,
      3, 5)) (.next ([-540000000000], [2415000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next
      ([-255000000000], [1125000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-330000000000,
      9000000000000], [1080000000000, -9000000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.next
      ([-1080000000000, -9000000000000], [2160000000000, 18000000000000]) (some (1, 3, 5)) (some (1,
      3, 5)) (.next ([-1410000000000], [2160000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-1335000000000, 9000000000000], [1875000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-1620000000000, -9000000000000], [2415000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-5835000000000], [8250000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next
      ([-6960000000000], [9120000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-7710000000000,
      0], [8790000000000, 9000000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.terminal (some (1, 3,
      5)) (some (1, 3, 5)) (some (1, 3, 5))))))))))))))))))))))))))) (.witnessedFan (.next
      ([2160000000000], [330000000000, 9000000000000]) (some (5, 1, 3)) (some (5, 1, 5)) (.next
      ([1875000000000], [540000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([870000000000],
      [255000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([750000000000, 0], [330000000000,
      -9000000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next ([1080000000000, 9000000000000],
      [1080000000000, 9000000000000]) (some (5, 1, 5)) (some (5, 2, 5)) (.next ([750000000000],
      [1410000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([540000000000, 9000000000000],
      [1335000000000, -9000000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([2415000000000],
      [5835000000000]) (some (5, 2, 5)) (some (5, 2, 5)) (.next ([795000000000, -9000000000000],
      [1620000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([2160000000000],
      [6960000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([1080000000000, 9000000000000],
      [7710000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-330000000000, -9000000000000],
      [2490000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 3, 5)) (.next ([-540000000000],
      [2415000000000]) (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-255000000000], [1125000000000])
      (some (0, 3, 5)) (some (0, 3, 5)) (.next ([-330000000000, 9000000000000], [1080000000000,
      -9000000000000]) (some (0, 3, 5)) (some (1, 3, 5)) (.next ([-1080000000000, -9000000000000],
      [2160000000000, 18000000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1410000000000],
      [2160000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1335000000000, 9000000000000],
      [1875000000000]) (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-5835000000000], [8250000000000])
      (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-1620000000000, -9000000000000], [2415000000000])
      (some (1, 3, 5)) (some (1, 3, 5)) (.next ([-6960000000000], [9120000000000]) (some (1, 3, 5))
      (some (1, 3, 5)) (.next ([-7710000000000, 0], [8790000000000, 9000000000000]) (some (1, 3, 5))
      (some (1, 3, 5)) (.terminal (some (1, 3, 5)) (some (1, 3, 5)) (some (1, 3,
      5))))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded25_2
    · exact excluded25_3
    · exact excluded25_4
    · exact excluded25_5
    · exact excluded25_6
    · exact excluded25_7
    · exact excluded25_8
    · exact excluded25_9
theorem next25 : model25.insert step25 = model26 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [540000000000]) (some (4, 0, 3))
      (some (4, 5, 3)) (.next ([5835000000000, 0], [1080000000000, 9000000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([3405000000000], [720000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([5835000000000], [3165000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([2295000000000, -9000000000000], [1620000000000, 9000000000000]) (some (4, 5, 3)) (some (4,
      5, 3)) (.next ([2325000000000, -9000000000000], [1800000000000, 9000000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([1920000000000], [3375000000000]) (some (4, 5, 3)) (some (4, 5,
      3)) (.next ([1710000000000], [3405000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([30000000000], [180000000000]) (some (4, 5, 3)) (some (4, 5, 4)) (.next ([240000000000],
      [3885000000000]) (some (4, 5, 4)) (some (4, 5, 4)) (.next ([210000000000], [3705000000000])
      (some (4, 5, 4)) (some (4, 5, 4)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (4, 5,
      4)) (some (4, 5, 4)) (.next ([-540000000000], [3915000000000]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-1080000000000, -9000000000000], [6915000000000, 9000000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-720000000000], [4125000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3165000000000], [9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-1620000000000, -9000000000000], [3915000000000, 0]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-1800000000000, -9000000000000], [4125000000000, 0]) (some (0, 5, 4)) (some (0, 5,
      4)) (.next ([-3375000000000], [5295000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-3405000000000], [5115000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-180000000000],
      [210000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3885000000000], [4125000000000])
      (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3705000000000], [3915000000000]) (some (0, 3, 4))
      (some (0, 3, 4)) (.terminal (some (0, 3, 4)) (some (0, 3, 4)) (some (0, 3,
      4))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked26 : StepValid model26 9000000000000 step26 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded26_0
    · exact excluded26_1
    · exact excluded26_2
    · exact excluded26_3
    · exact excluded26_4
    · exact (hj rfl).elim
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_2 : ExcludedOn (model27.B 2 ++ [step27.q]) 9000000000000 (model27.caps 2)
    (model27.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5835000000000, 0], [1080000000000,
      9000000000000]) (some (5, 0, 2)) (some (5, 1, 2)) fan27Owner5Part0)) (den := 9000000000000)
      (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded27_0
    · exact excluded27_1
    · exact excluded27_2
    · exact excluded27_3
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6465000000000], [3615000000000]) (some (3, 3,
      1)) (some (3, 3, 2)) (.next ([1290000000000, 0], [1080000000000, 9000000000000]) (some (3, 1,
      2)) (some (3, 1, 2)) (.next ([5175000000000], [4905000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([4095000000000, -9000000000000], [4905000000000, 0]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3615000000000], [10080000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-1080000000000, -9000000000000], [2370000000000, 9000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-4905000000000], [10080000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-4905000000000, 0], [9000000000000, -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 3)) (some (3, 1, 3))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_2 : ExcludedOn (model28.B 2 ++ [step28.q]) 9000000000000 (model28.caps 2)
    (model28.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3825000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7920000000000, -9000000000000],
      [1080000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4095000000000,
      -9000000000000], [4905000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1080000000000], [3825000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [3825000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1080000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-4905000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3825000000000],
      [4905000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([420000000000, -9000000000000], [0,
      9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([2895000000000], [930000000000])
      (some (3, 0, 4)) (some (3, 1, 4)) (.next ([1080000000000], [420000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([3825000000000], [4095000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([2745000000000, -9000000000000], [5175000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([2325000000000], [5175000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([0], [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([0,
      -9000000000000], [420000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-930000000000],
      [3825000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-420000000000], [1500000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-4095000000000], [7920000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5175000000000, -9000000000000], [7920000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-5175000000000], [7500000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2625000000000, -9000000000000], [0,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([7920000000000, -9000000000000],
      [1080000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5295000000000,
      -9000000000000], [3705000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next
      ([1080000000000], [2625000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, -9000000000000],
      [2625000000000]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-1080000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-3705000000000, 0],
      [9000000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2625000000000],
      [3705000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1,
      0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([420000000000, -9000000000000], [0,
      9000000000000]) (some (2, 0, 4)) (some (3, 0, 4)) (.next ([1080000000000], [420000000000])
      (some (3, 0, 4)) (some (3, 1, 4)) (.next ([1695000000000], [930000000000]) (some (3, 1, 4))
      (some (3, 1, 4)) (.next ([2625000000000], [5295000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([1545000000000, -9000000000000], [6375000000000, 9000000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([1125000000000], [6375000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([0], [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 4, 2)) (.next ([0,
      -9000000000000], [420000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-420000000000],
      [1500000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-930000000000], [2625000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-5295000000000], [7920000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6375000000000, -9000000000000], [7920000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-6375000000000], [7500000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_6 : ExcludedOn (model29.B 6 ++ [step29.q]) 9000000000000 (model29.caps 6)
    (model29.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_8 : ExcludedOn (model29.B 8 ++ [step29.q]) 9000000000000 (model29.caps 8)
    (model29.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded29_9 : ExcludedOn (model29.B 9 ++ [step29.q]) 9000000000000 (model29.caps 9)
    (model29.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked29 : StepValid model29 9000000000000 step29 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
    · exact excluded29_4
    · exact excluded29_5
    · exact excluded29_6
    · exact excluded29_7
    · exact excluded29_8
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8130000000000], [585000000000]) none none (.next
      ([6840000000000], [1875000000000]) none none (.next ([5760000000000, -9000000000000],
      [1875000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([1290000000000, 0],
      [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-585000000000],
      [8715000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1875000000000], [8715000000000])
      (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1875000000000, 0], [7635000000000,
      -9000000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next ([-1080000000000, -9000000000000],
      [2370000000000, 9000000000000]) (some (3, 1, 0)) (some (3, 1, 3)) (.terminal (some (3, 1, 3))
      none none))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7920000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1875000000000], [285000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5760000000000, -9000000000000], [1875000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([795000000000, -9000000000000], [1365000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1080000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-285000000000],
      [2160000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1875000000000, 0],
      [7635000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-1365000000000,
      -9000000000000], [2160000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2160000000000], [135000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([6990000000000], [1080000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 1, 4)) (.next ([6570000000000], [1500000000000]) (some (3, 1, 4)) (some (3, 1, 4))
      (.next ([1080000000000], [420000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([2160000000000], [7125000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([1080000000000,
      -9000000000000], [8205000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next
      ([660000000000], [8205000000000]) (some (3, 1, 4)) (some (3, 1, 4)) (.next ([0],
      [1080000000000, 9000000000000]) (some (3, 1, 4)) (some (3, 4, 4)) (.next ([-135000000000],
      [2295000000000]) (some (0, 4, 4)) (some (0, 4, 4)) (.next ([-1080000000000, -9000000000000],
      [8070000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1500000000000],
      [8070000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-420000000000], [1500000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-7125000000000], [9285000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8205000000000, -9000000000000], [9285000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.next ([-8205000000000], [8865000000000]) (some (0, 4, 2)) (some (0, 4, 2))
      (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_8 : ExcludedOn (model30.B 8 ++ [step30.q]) 9000000000000 (model30.caps 8)
    (model30.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded30_9 : ExcludedOn (model30.B 9 ++ [step30.q]) 9000000000000 (model30.caps 9)
    (model30.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked30 : StepValid model30 9000000000000 step30 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded30_1
    · exact excluded30_2
    · exact excluded30_3
    · exact excluded30_4
    · exact excluded30_5
    · exact excluded30_6
    · exact excluded30_7
    · exact excluded30_8
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_4 : ExcludedOn (model31.B 4 ++ [step31.q]) 9000000000000 (model31.caps 4)
    (model31.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2160000000000], [330000000000, 9000000000000])
      (some (0, 5, 3)) (some (0, 5, 4)) fan31Owner6Part0)) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded31_7 : ExcludedOn (model31.B 7 ++ [step31.q]) 9000000000000 (model31.caps 7)
    (model31.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded31_8 : ExcludedOn (model31.B 8 ++ [step31.q]) 9000000000000 (model31.caps 8)
    (model31.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked31 : StepValid model31 9000000000000 step31 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded31_0
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact excluded31_4
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact (hj rfl).elim
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint120000130000
end ConwaySoifer.Simplified.Certificates

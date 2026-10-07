/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint120000130000
import Mathlib.Tactic.FinCases

/-!
# Sint 120000 130000 4

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
def fan34Owner4Part0 : FanWitness := (.next ([7170000000000, -9000000000000], [1110000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([5835000000000, 0], [1080000000000,
    9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([3405000000000], [720000000000]) (some
    (4, 1, 5)) (some (4, 1, 5)) (.next ([4425000000000], [1110000000000]) (some (4, 1, 5)) (some (4,
    1, 5)) (.next ([1380000000000], [420000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([5805000000000], [2445000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([2325000000000,
    -9000000000000], [1800000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next
    ([3090000000000], [3825000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1710000000000],
    [3405000000000]) (some (4, 1, 5)) (some (4, 1, 5)) (.next ([1080000000000], [2745000000000])
    (some (4, 1, 5)) (some (4, 1, 5)) (.next ([690000000000], [4155000000000]) (some (4, 1, 5))
    (some (4, 1, 5)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (4, 1, 5)) (some (4, 1,
    5)) (.next ([-30000000000], [8280000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([-1110000000000, -9000000000000], [8280000000000, 0]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-1080000000000, -9000000000000], [6915000000000, 9000000000000]) (some (0, 2, 5)) (some (0, 2,
    5)) (.next ([-720000000000], [4125000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1110000000000], [5535000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-420000000000],
    [1800000000000]) (some (0, 2, 5)) (some (0, 5, 5)) (.next ([-2445000000000], [8250000000000])
    (some (0, 5, 5)) (some (0, 5, 5)) (.next ([-1800000000000, -9000000000000], [4125000000000, 0])
    (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-3825000000000], [6915000000000]) (some (0, 5, 4))
    (some (0, 5, 4)) (.next ([-3405000000000], [5115000000000]) (some (0, 5, 4)) (some (0, 5, 4))
    (.next ([-2745000000000], [3825000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
    ([-4155000000000], [4845000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
    4)) (some (0, 5, 4)) (some (0, 5, 4)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan34Owner5Part0 : FanWitness := (.next ([5835000000000, 0], [1080000000000, 9000000000000])
    (some (5, 1, 2)) (some (5, 1, 2)) (.next ([3825000000000], [855000000000]) (some (5, 1, 2))
    (some (5, 1, 2)) (.next ([7200000000000, -9000000000000], [1830000000000, 9000000000000]) (some
    (5, 1, 2)) (some (5, 1, 2)) (.next ([3825000000000], [1080000000000]) (some (5, 1, 2)) (some (5,
    1, 5)) (.next ([5085000000000], [3195000000000]) (some (5, 1, 5)) (some (5, 1, 5)) (.next
    ([2745000000000, -9000000000000], [1935000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1,
    5)) (.next ([2745000000000, -9000000000000], [2160000000000, 9000000000000]) (some (0, 1, 5))
    (some (0, 1, 5)) (.next ([1155000000000], [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5))
    (.next ([930000000000], [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
    ([330000000000], [4125000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([105000000000],
    [4350000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0], [5835000000000]) (some (0, 1,
    5)) (some (0, 1, 5)) (.next ([-750000000000], [9030000000000]) (some (0, 1, 5)) (some (0, 2, 5))
    (.next ([-1080000000000, -9000000000000], [6915000000000, 9000000000000]) (some (0, 2, 5)) (some
    (0, 2, 5)) (.next ([-855000000000], [4680000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1830000000000, -9000000000000], [9030000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next
    ([-1080000000000], [4905000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3195000000000],
    [8280000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1935000000000, -9000000000000],
    [4680000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2160000000000, -9000000000000],
    [4905000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3825000000000], [4980000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3825000000000], [4755000000000]) (some (0, 2, 5))
    (some (0, 2, 5)) (.next ([-4125000000000], [4455000000000]) (some (0, 2, 5)) (some (0, 2, 5))
    (.next ([-4350000000000], [4455000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some
    (0, 2, 5)) (some (0, 2, 5)) (some (0, 2, 5)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan35Owner6Part0 : FanWitness := (.next ([3930000000000], [750000000000]) (some (5, 0, 3)) (some
    (5, 0, 3)) (.next ([4155000000000], [855000000000]) (some (5, 0, 3)) (some (5, 0, 3)) (.next
    ([2850000000000, -9000000000000], [750000000000]) (some (4, 0, 3)) (some (4, 0, 3)) (.next
    ([3825000000000], [1080000000000]) (some (4, 0, 3)) (some (4, 0, 5)) (.next ([2745000000000,
    -9000000000000], [2160000000000, 9000000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (4, 0, 5)) (some (4, 0,
    5)) (.next ([855000000000], [3240000000000]) (some (4, 0, 5)) (some (4, 0, 5)) (.next
    ([585000000000, 0], [4095000000000, -9000000000000]) (some (0, 0, 5)) (some (0, 0, 5)) (.next
    ([585000000000], [5175000000000]) (some (0, 0, 5)) (some (0, 1, 5)) (.next ([330000000000,
    9000000000000], [4680000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0, 9000000000000],
    [3825000000000, -9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0, 0],
    [1080000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-495000000000,
    -9000000000000], [6255000000000, 9000000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
    ([-750000000000], [4680000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-855000000000],
    [5010000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-750000000000], [3600000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1080000000000], [4905000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-2160000000000, -9000000000000], [4905000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-1080000000000, -9000000000000], [2160000000000,
    18000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3240000000000], [4095000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4095000000000, 9000000000000], [4680000000000,
    -9000000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-5175000000000], [5760000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-4680000000000, 0], [5010000000000, 9000000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.next ([-3825000000000, 9000000000000], [3825000000000])
    (some (0, 2, 5)) (some (0, 2, 5)) (.terminal (some (0, 2, 5)) (some (0, 2, 5)) (some (0, 2,
    5)))))))))))))))))))))))))))

theorem excluded32_0 : ExcludedOn (model32.B 0 ++ [step32.q]) 9000000000000 (model32.caps 0)
    (model32.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded32_5 : ExcludedOn (model32.B 5 ++ [step32.q]) 9000000000000 (model32.caps 5)
    (model32.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3240000000000], [585000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) (.next ([5835000000000, 0], [1080000000000, 9000000000000]) (some (0, 1, 5))
      (some (0, 1, 5)) (.next ([3825000000000], [855000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([2160000000000, -9000000000000], [585000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([5250000000000], [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([2745000000000, -9000000000000], [2160000000000, 9000000000000]) (some (0, 1, 5)) (some (0,
      1, 5)) (.next ([1155000000000], [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next
      ([930000000000], [3825000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([0],
      [5835000000000]) (some (0, 1, 5)) (some (0, 1, 5)) (.next ([-585000000000], [3825000000000])
      (some (0, 1, 3)) (some (0, 2, 4)) (.next ([-1080000000000, -9000000000000], [6915000000000,
      9000000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-855000000000], [4680000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-585000000000, 0], [2745000000000, -9000000000000])
      (some (0, 2, 4)) (some (0, 2, 4)) (.next ([-3825000000000], [9075000000000]) (some (0, 2, 4))
      (some (0, 5, 4)) (.next ([-2160000000000, -9000000000000], [4905000000000]) (some (0, 5, 4))
      (some (0, 5, 4)) (.next ([-3825000000000], [4980000000000]) (some (0, 5, 4)) (some (0, 5, 4))
      (.next ([-3825000000000], [4755000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some
      (0, 5, 0)) (some (0, 5, 0)) (some (0, 5, 0))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.witnessedFan (.next ([3900000000000], [1860000000000]) (some (3, 0,
      1)) (some (3, 1, 2)) (.next ([3825000000000], [5760000000000]) (some (3, 1, 2)) (some (3, 1,
      2)) (.next ([1965000000000], [5760000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([0],
      [5760000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([-1860000000000], [5760000000000])
      (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-5760000000000], [9585000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([-5760000000000], [7725000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.terminal (some (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
    · exact excluded32_5
    · exact (hj rfl).elim
    · exact excluded32_7
    · exact excluded32_8
    · exact excluded32_9
theorem next32 : model32.insert step32 = model33 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded33_0 : ExcludedOn (model33.B 0 ++ [step33.q]) 9000000000000 (model33.caps 0)
    (model33.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_1 : ExcludedOn (model33.B 1 ++ [step33.q]) 9000000000000 (model33.caps 1)
    (model33.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4905000000000], [3885000000000]) (some (0, 3,
      1)) (some (0, 3, 2)) (.next ([1290000000000, 0], [1080000000000, 9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([4905000000000], [5175000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([3825000000000, -9000000000000], [6255000000000, 9000000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([0, 0], [1080000000000, 9000000000000]) (some (0, 3, 2)) (some (3, 3,
      2)) (.next ([-3885000000000], [8790000000000]) (some (3, 3, 0)) (some (3, 3, 0)) (.next
      ([-1080000000000, -9000000000000], [2370000000000, 9000000000000]) (some (3, 1, 0)) (some (3,
      1, 0)) (.next ([-5175000000000], [10080000000000]) (some (3, 1, 0)) (some (3, 1, 0)) (.next
      ([-6255000000000, -9000000000000], [10080000000000, 0]) (some (3, 1, 0)) (some (3, 1, 0))
      (.terminal (some (3, 1, 0)) (some (3, 1, 0)) (some (3, 1, 0))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded33_5 : ExcludedOn (model33.B 5 ++ [step33.q]) 9000000000000 (model33.caps 5)
    (model33.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded33_1
    · exact excluded33_2
    · exact excluded33_3
    · exact excluded33_4
    · exact excluded33_5
    · exact (hj rfl).elim
    · exact excluded33_7
    · exact excluded33_8
    · exact excluded33_9
theorem next33 : model33.insert step33 = model34 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded34_1 : ExcludedOn (model34.B 1 ++ [step34.q]) 9000000000000 (model34.caps 1)
    (model34.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_2 : ExcludedOn (model34.B 2 ++ [step34.q]) 9000000000000 (model34.caps 2)
    (model34.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded34_3 : ExcludedOn (model34.B 3 ++ [step34.q]) 9000000000000 (model34.caps 3)
    (model34.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7470000000000], [360000000000]) (some (2, 0, 4))
      (some (3, 0, 4)) (.next ([6990000000000], [1080000000000, 9000000000000]) (some (3, 0, 4))
      (some (3, 4, 4)) (.next ([6570000000000], [1500000000000]) (some (3, 4, 4)) (some (3, 4, 2))
      (.next ([1080000000000], [420000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next
      ([720000000000], [8250000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([0],
      [1080000000000, 9000000000000]) (some (3, 4, 2)) (some (3, 4, 2)) (.next ([-360000000000],
      [7830000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1080000000000, -9000000000000],
      [8070000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-1500000000000],
      [8070000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-420000000000], [1500000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([-8250000000000], [8970000000000]) (some (0, 4, 2))
      (some (0, 4, 2)) (.terminal (some (0, 4, 2)) (some (0, 4, 2)) (some (0, 4, 2)))))))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_4 : ExcludedOn (model34.B 4 ++ [step34.q]) 9000000000000 (model34.caps 4)
    (model34.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8250000000000], [30000000000]) (some (4, 0, 5))
      (some (4, 1, 5)) fan34Owner4Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_5 : ExcludedOn (model34.B 5 ++ [step34.q]) 9000000000000 (model34.caps 5)
    (model34.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([8280000000000], [750000000000]) (some (5, 0, 2))
      (some (5, 1, 2)) fan34Owner5Part0)) (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded34_6 : ExcludedOn (model34.B 6 ++ [step34.q]) 9000000000000 (model34.caps 6)
    (model34.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_2 : ExcludedOn (model35.B 2 ++ [step35.q]) 9000000000000 (model35.caps 2)
    (model35.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_3 : ExcludedOn (model35.B 3 ++ [step35.q]) 9000000000000 (model35.caps 3)
    (model35.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_4 : ExcludedOn (model35.B 4 ++ [step35.q]) 9000000000000 (model35.caps 4)
    (model35.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_5 : ExcludedOn (model35.B 5 ++ [step35.q]) 9000000000000 (model35.caps 5)
    (model35.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded35_6 : ExcludedOn (model35.B 6 ++ [step35.q]) 9000000000000 (model35.caps 6)
    (model35.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5760000000000], [495000000000, 9000000000000])
      (some (5, 0, 2)) (some (5, 0, 3)) fan35Owner6Part0)) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100
      (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded35_2
    · exact excluded35_3
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
  apply ExclusionHint.sound (.witnessedFan (.next ([6600000000000], [150000000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([5070000000000, 0], [330000000000, 9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([5310000000000], [1440000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([4230000000000, -9000000000000], [1440000000000, 0]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([1290000000000, 0], [1080000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([3630000000000], [6000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([750000000000], [3030000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([750000000000],
      [4320000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0], [1080000000000,
      9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-150000000000], [6750000000000])
      (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-330000000000, -9000000000000], [5400000000000,
      9000000000000]) (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-1440000000000], [6750000000000])
      (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-1440000000000, 0], [5670000000000,
      -9000000000000]) (some (4, 1, 0)) (some (4, 1, 0)) (.next ([-1080000000000, -9000000000000],
      [2370000000000, 9000000000000]) (some (4, 1, 0)) (some (4, 1, 4)) (.next ([-6000000000000],
      [9630000000000]) (some (4, 1, 4)) none (.next ([-3030000000000], [3780000000000]) none none
      (.next ([-4320000000000], [5070000000000]) (some (1, 1, 4)) (some (1, 2, 4)) (.terminal (some
      (1, 2, 4)) (some (1, 2, 4)) (some (1, 2, 4))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded36_2 : ExcludedOn (model36.B 2 ++ [step36.q]) 9000000000000 (model36.caps 2)
    (model36.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7920000000000, -9000000000000], [1080000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([4230000000000, -9000000000000],
      [1440000000000, 0]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1440000000000],
      [2250000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([360000000000, -9000000000000],
      [3330000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1080000000000,
      -9000000000000], [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next
      ([-1440000000000, 0], [5670000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-2250000000000], [3690000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([-3330000000000, -9000000000000], [3690000000000]) (some (0, 1, 2)) (some (0, 1, 2))
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_5 : ExcludedOn (model36.B 5 ++ [step36.q]) 9000000000000 (model36.caps 5)
    (model36.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded36_6 : ExcludedOn (model36.B 6 ++ [step36.q]) 9000000000000 (model36.caps 6)
    (model36.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

end Sint120000130000
end ConwaySoifer.Simplified.Certificates

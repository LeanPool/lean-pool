/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown120000130000
import Mathlib.Tactic.FinCases

/-!
# Aown 120000 130000 3

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
namespace Aown120000130000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan24Owner4Part0 : FanWitness := (.next ([5280000000000], [720000000000]) (some (3, 1, 2)) (some
    (3, 1, 2)) (.next ([3210000000000], [540000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
    ([2130000000000, -9000000000000], [540000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
    ([4200000000000, -9000000000000], [1800000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 5,
    2)) (.next ([5970000000000], [3000000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next
    ([1080000000000, 9000000000000], [1080000000000, 9000000000000]) (some (3, 5, 2)) (some (3, 5,
    2)) (.next ([1530000000000], [3930000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next
    ([750000000000], [4680000000000, -9000000000000]) (some (3, 5, 2)) (some (3, 5, 2)) (.next
    ([750000000000], [5760000000000]) (some (3, 5, 2)) (some (4, 5, 2)) (.next ([510000000000],
    [4530000000000]) (some (4, 5, 2)) (some (4, 5, 2)) (.next ([360000000000, 9000000000000],
    [4920000000000, -9000000000000]) (some (4, 5, 2)) (some (4, 5, 3)) (.next ([0, 0],
    [1080000000000, 9000000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([-330000000000,
    -9000000000000], [6840000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-720000000000], [6000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-540000000000],
    [3750000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-540000000000, 0], [2670000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1800000000000, -9000000000000],
    [6000000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3000000000000], [8970000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-1080000000000, -9000000000000], [2160000000000,
    18000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-3930000000000], [5460000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([-4680000000000, 9000000000000], [5430000000000,
    -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5760000000000], [6510000000000])
    (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-4530000000000], [5040000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.next ([-4920000000000, 9000000000000], [5280000000000]) (some (0, 2, 3))
    (some (0, 2, 3)) (.terminal (some (0, 2, 3)) (some (0, 2, 3)) (some (0, 2,
    3)))))))))))))))))))))))))))

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
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_3 : ExcludedOn (model24.B 3 ++ [step24.q]) 9000000000000 (model24.caps 3)
    (model24.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6510000000000, 0], [330000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) fan24Owner4Part0)) (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact excluded24_3
    · exact excluded24_4
    · exact (hj rfl).elim
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [225000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([8640000000000], [615000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([7335000000000], [735000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([4320000000000], [1305000000000]) (some (0, 4, 3)) (some (4, 4, 3))
      (.next ([4890000000000, 0], [2670000000000, -9000000000000]) (some (4, 4, 3)) (some (4, 4, 3))
      (.next ([4890000000000], [3750000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1080000000000, 9000000000000], [5505000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([120000000000], [1185000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-225000000000,
      9000000000000], [5625000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-615000000000],
      [9255000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-735000000000], [8070000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-1305000000000], [5625000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-2670000000000, 9000000000000], [7560000000000, -9000000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-3750000000000], [8640000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-5505000000000, 0], [6585000000000, 9000000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-1185000000000], [1305000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 0)) (some (4, 2, 0)) (some (4, 2, 0))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_2 : ExcludedOn (model26.B 2 ++ [step26.q]) 9000000000000 (model26.caps 2)
    (model26.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5400000000000, 9000000000000], [225000000000,
      -9000000000000]) (some (0, 4, 2)) (some (0, 4, 3)) (.next ([4320000000000], [1305000000000])
      (some (0, 4, 3)) (some (0, 4, 3)) (.next ([5580000000000], [4425000000000]) (some (0, 4, 3))
      (some (0, 4, 3)) (.next ([4275000000000], [4545000000000]) (some (0, 4, 3)) (some (0, 4, 3))
      (.next ([1080000000000, 0], [3420000000000, -9000000000000]) (some (0, 4, 3)) (some (4, 4, 3))
      (.next ([1080000000000], [4500000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([1080000000000, 9000000000000], [5505000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([120000000000], [1185000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([0, 0],
      [1080000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next ([-225000000000,
      9000000000000], [5625000000000]) (some (4, 1, 3)) (some (4, 2, 3)) (.next ([-1305000000000],
      [5625000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4425000000000], [10005000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4545000000000], [8820000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-3420000000000, 9000000000000], [4500000000000, -9000000000000])
      (some (4, 2, 3)) (some (4, 2, 3)) (.next ([-4500000000000], [5580000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-5505000000000, 0], [6585000000000, 9000000000000]) (some (4, 2, 3))
      (some (4, 2, 3)) (.next ([-1185000000000], [1305000000000]) (some (4, 2, 3)) (some (4, 2, 3))
      (.terminal (some (4, 2, 0)) (some (4, 2, 0)) (some (4, 2, 0))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([1875000000000], [360000000000]) (some (4, 0, 1))
      (some (4, 1, 2)) (.next ([795000000000, -9000000000000], [360000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([4500000000000, 0], [4500000000000, -9000000000000]) (some (4, 1, 2))
      (some (4, 1, 3)) (.next ([4500000000000], [5580000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([720000000000, 9000000000000], [1155000000000, -9000000000000]) (some (4, 1, 3)) (some
      (4, 1, 3)) (.next ([3420000000000, -9000000000000], [5580000000000]) (some (4, 1, 3)) (some
      (4, 1, 3)) (.next ([2625000000000], [5220000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([0, 0], [1080000000000, 9000000000000]) (some (4, 1, 3)) (some (4, 1, 4)) (.next
      ([-360000000000], [2235000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-360000000000],
      [1155000000000, -9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next ([-4500000000000,
      9000000000000], [9000000000000, -9000000000000]) (some (4, 1, 4)) (some (4, 1, 4)) (.next
      ([-5580000000000], [10080000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-1155000000000, 9000000000000], [1875000000000, 0]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5580000000000], [9000000000000, -9000000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.next
      ([-5220000000000], [7845000000000]) (some (0, 1, 4)) (some (0, 1, 4)) (.terminal (some (0, 1,
      4)) (some (0, 1, 4)) (some (0, 1, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

end Aown120000130000
end ConwaySoifer.Simplified.Certificates

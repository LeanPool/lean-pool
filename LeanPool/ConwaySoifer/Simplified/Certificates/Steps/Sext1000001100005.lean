/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext100000110000
import Mathlib.Tactic.FinCases

/-!
# Sext 100000 110000 5

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
namespace Sext100000110000

theorem excluded40_0 : ExcludedOn (model40.B 0 ++ [step40.q]) 9000000000000 (model40.caps 0)
    (model40.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_2 : ExcludedOn (model40.B 2 ++ [step40.q]) 9000000000000 (model40.caps 2)
    (model40.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4875000000000], [375000000000]) (some (0, 0, 5))
      (some (0, 1, 5)) (.next ([3975000000000], [375000000000]) (some (0, 1, 5)) (some (0, 1, 5))
      (.next ([5250000000000], [900000000000]) (some (0, 1, 5)) (some (0, 2, 5)) (.next
      ([3750000000000], [1125000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([3750000000000],
      [5250000000000]) (some (0, 2, 5)) (some (0, 2, 5)) (.next ([2850000000000], [5250000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([900000000000, 0], [1950000000000, -9000000000000])
      (some (0, 2, 5)) (some (0, 2, 5)) (.next ([900000000000], [2850000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([900000000000], [4875000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([900000000000, 9000000000000], [6150000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([0, 9000000000000], [6150000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0],
      [900000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-375000000000], [5250000000000])
      (some (0, 2, 3)) (some (0, 2, 4)) (.next ([-375000000000], [4350000000000]) (some (0, 2, 4))
      (some (0, 2, 4)) (.next ([-900000000000], [6150000000000]) (some (0, 2, 4)) (some (0, 2, 4))
      (.next ([-1125000000000], [4875000000000]) (some (0, 2, 4)) (some (0, 2, 4)) (.next
      ([-5250000000000], [9000000000000]) (some (0, 2, 4)) (some (0, 5, 4)) (.next
      ([-5250000000000], [8100000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-1950000000000,
      9000000000000], [2850000000000, -9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-2850000000000], [3750000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next
      ([-4875000000000], [5775000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6150000000000,
      0], [7050000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.next ([-6150000000000,
      0], [6150000000000, 9000000000000]) (some (0, 5, 4)) (some (0, 5, 4)) (.terminal (some (0, 5,
      4)) (some (0, 5, 0)) (some (0, 5, 4))))))))))))))))))))))))))) (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_3 : ExcludedOn (model40.B 3 ++ [step40.q]) 9000000000000 (model40.caps 3)
    (model40.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_4 : ExcludedOn (model40.B 4 ++ [step40.q]) 9000000000000 (model40.caps 4)
    (model40.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_5 : ExcludedOn (model40.B 5 ++ [step40.q]) 9000000000000 (model40.caps 5)
    (model40.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_6 : ExcludedOn (model40.B 6 ++ [step40.q]) 9000000000000 (model40.caps 6)
    (model40.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded40_7 : ExcludedOn (model40.B 7 ++ [step40.q]) 9000000000000 (model40.caps 7)
    (model40.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6150000000000], [2400000000000]) (some (0, 3,
      1)) (some (0, 3, 2)) (.next ([6150000000000], [3750000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([1350000000000], [1350000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next
      ([3450000000000], [3750000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0],
      [2700000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.next ([-2400000000000], [8550000000000])
      (some (3, 3, 2)) (some (3, 3, 2)) (.next ([-3750000000000], [9900000000000]) (some (3, 1, 2))
      (some (3, 1, 2)) (.next ([-1350000000000], [2700000000000]) (some (3, 1, 2)) (some (3, 1, 2))
      (.next ([-3750000000000], [7200000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some
      (3, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded40_8 : ExcludedOn (model40.B 8 ++ [step40.q]) 9000000000000 (model40.caps 8)
    (model40.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
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
    · exact (hj rfl).elim
    · exact excluded40_2
    · exact excluded40_3
    · exact excluded40_4
    · exact excluded40_5
    · exact excluded40_6
    · exact excluded40_7
    · exact excluded40_8
    · exact excluded40_9
theorem next40 : model40.insert step40 = model41 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded41_1 : ExcludedOn (model41.B 1 ++ [step41.q]) 9000000000000 (model41.caps 1)
    (model41.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_2 : ExcludedOn (model41.B 2 ++ [step41.q]) 9000000000000 (model41.caps 2)
    (model41.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_3 : ExcludedOn (model41.B 3 ++ [step41.q]) 9000000000000 (model41.caps 3)
    (model41.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_4 : ExcludedOn (model41.B 4 ++ [step41.q]) 9000000000000 (model41.caps 4)
    (model41.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_5 : ExcludedOn (model41.B 5 ++ [step41.q]) 9000000000000 (model41.caps 5)
    (model41.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded41_6 : ExcludedOn (model41.B 6 ++ [step41.q]) 9000000000000 (model41.caps 6)
    (model41.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3150000000000, 9000000000000], [600000000000,
      -9000000000000]) (some (2, 0, 1)) (some (2, 0, 2)) (.next ([2250000000000], [1500000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([1500000000000], [4350000000000, -9000000000000])
      (some (2, 0, 2)) (some (2, 0, 2)) (.next ([900000000000, 9000000000000], [8100000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [900000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-600000000000, 9000000000000],
      [3750000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-1500000000000], [3750000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4350000000000, 9000000000000], [5850000000000,
      -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-8100000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded41_1
    · exact excluded41_2
    · exact excluded41_3
    · exact excluded41_4
    · exact excluded41_5
    · exact excluded41_6
    · exact excluded41_7
    · exact excluded41_8
    · exact excluded41_9
theorem next41 : model41.insert step41 = model42 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext100000110000
end ConwaySoifer.Simplified.Certificates

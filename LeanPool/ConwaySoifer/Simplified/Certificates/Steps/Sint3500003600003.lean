/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint350000360000
import Mathlib.Tactic.FinCases

/-!
# Sint 350000 360000 3

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
namespace Sint350000360000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan26Owner4Part0 : FanWitness := (.next ([1350000000000], [1800000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([3525000000000], [4725000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([3150000000000, 9000000000000], [4725000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([1575000000000], [2925000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next
    ([1800000000000], [4500000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([225000000000],
    [1125000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([375000000000], [6075000000000])
    (some (6, 1, 3)) (some (6, 1, 3)) (.next ([225000000000], [4500000000000]) (some (6, 1, 3))
    (some (6, 1, 3)) (.next ([0, 9000000000000], [6075000000000]) (some (6, 1, 3)) (some (6, 1, 3))
    (.next ([0], [4725000000000]) (some (6, 1, 3)) (some (6, 1, 3)) (.next ([-975000000000],
    [6300000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next ([-975000000000], [4725000000000])
    (some (0, 1, 4)) (some (0, 1, 4)) (.next ([-1350000000000, 9000000000000], [4725000000000])
    (some (0, 1, 4)) (some (0, 1, 6)) (.next ([-1350000000000], [2700000000000]) (some (0, 1, 6))
    (some (0, 1, 6)) (.next ([-3150000000000], [6075000000000]) (some (0, 1, 6)) (some (0, 1, 6))
    (.next ([-1800000000000], [3150000000000]) (some (0, 1, 6)) (some (0, 1, 6)) (.next
    ([-4725000000000], [8250000000000]) (some (0, 1, 6)) (some (0, 2, 6)) (.next ([-4725000000000],
    [7875000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2925000000000],
    [4500000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4500000000000], [6300000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-1125000000000], [1350000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-6075000000000], [6450000000000]) (some (0, 2, 6)) (some (0, 3, 6))
    (.next ([-4500000000000], [4725000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([-6075000000000], [6075000000000, 9000000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.terminal
    (some (0, 3, 6)) (some (0, 3, 6)) (some (0, 3, 6)))))))))))))))))))))))))))

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 4 8) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4275000000000], [1770000000000]) (some (3, 0,
      2)) (some (3, 1, 2)) (.next ([4050000000000], [1995000000000]) (some (3, 1, 2)) (some (4, 1,
      2)) (.next ([4275000000000], [3750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([4050000000000], [3750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2295000000000],
      [3750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [4050000000000]) (some (4, 1,
      2)) (some (4, 1, 3)) (.next ([-1770000000000], [6045000000000]) (some (4, 1, 3)) (some (4, 2,
      3)) (.next ([-1995000000000], [6045000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3750000000000], [8025000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3750000000000], [7800000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.next
      ([-3750000000000], [6045000000000]) (some (4, 2, 3)) (some (4, 2, 3)) (.terminal (some (4, 2,
      3)) (some (0, 2, 3)) (some (4, 2, 3))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded25_5 : ExcludedOn (model25.B 5 ++ [step25.q]) 9000000000000 (model25.caps 5)
    (model25.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6075000000000], [600000000000]) (some (4, 0, 2))
      (some (4, 1, 2)) (.next ([4050000000000], [1995000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([4050000000000], [3750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([3150000000000], [2925000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([2295000000000],
      [3750000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([1125000000000], [2025000000000])
      (some (4, 1, 2)) (some (4, 1, 3)) (.next ([30000000000], [2895000000000]) (some (0, 1, 3))
      (some (0, 1, 3)) (.next ([0], [4050000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([-600000000000], [6675000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-1995000000000],
      [6045000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-3750000000000], [7800000000000])
      (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-2925000000000], [6075000000000]) (some (0, 2, 3))
      (some (0, 2, 3)) (.next ([-3750000000000], [6045000000000]) (some (0, 2, 3)) (some (0, 2, 3))
      (.next ([-2025000000000], [3150000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-2895000000000], [2925000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 4)) (some (0, 2, 4))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
    · exact (hj rfl).elim
    · exact excluded25_5
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
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3375000000000], [1425000000000]) (some (3, 5,
      3)) (some (4, 5, 3)) (.next ([1425000000000], [675000000000]) (some (4, 5, 3)) (some (4, 5,
      3)) (.next ([4275000000000], [2430000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([4350000000000], [3330000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4275000000000],
      [4575000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([4350000000000], [5475000000000])
      (some (4, 5, 3)) (some (4, 5, 3)) (.next ([2850000000000], [3900000000000]) (some (4, 5, 3))
      (some (4, 5, 3)) (.next ([2925000000000], [4800000000000]) (some (4, 5, 3)) (some (4, 5, 3))
      (.next ([900000000000], [3375000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next
      ([75000000000], [900000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([45000000000],
      [1425000000000]) (some (4, 5, 3)) (some (4, 5, 3)) (.next ([0], [3330000000000]) (some (4, 5,
      3)) (some (4, 5, 3)) (.next ([-1425000000000], [4800000000000]) (some (0, 5, 3)) (some (5, 5,
      3)) (.next ([-675000000000], [2100000000000]) (some (5, 5, 3)) (some (5, 5, 3)) (.next
      ([-2430000000000], [6705000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-3330000000000], [7680000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-4575000000000], [8850000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-5475000000000], [9825000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-3900000000000], [6750000000000]) (some (5, 1, 3)) (some (5, 1, 3)) (.next
      ([-4800000000000], [7725000000000]) (some (5, 1, 3)) (some (5, 2, 3)) (.next
      ([-3375000000000], [4275000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-900000000000],
      [975000000000]) (some (5, 2, 3)) (some (5, 2, 3)) (.next ([-1425000000000], [1470000000000])
      (some (5, 2, 3)) (some (5, 3, 3)) (.terminal (some (5, 3, 3)) (some (5, 3, 3)) (some (5, 3,
      3))))))))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5325000000000], [975000000000]) (some (6, 0, 3))
      (some (6, 1, 3)) (.next ([3750000000000], [975000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([3375000000000, 9000000000000], [1350000000000, -9000000000000]) (some (6, 1, 3))
      (some (6, 1, 3)) (.next ([1350000000000], [1350000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      (.next ([2925000000000], [3150000000000]) (some (6, 1, 3)) (some (6, 1, 3))
      fan26Owner4Part0))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5475000000000], [3525000000000]) (some (0, 0,
      3)) (some (0, 1, 3)) (.next ([4275000000000], [3300000000000]) (some (0, 1, 3)) (some (0, 1,
      3)) (.next ([1425000000000], [2100000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next
      ([750000000000], [4725000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0],
      [7575000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3525000000000], [9000000000000])
      (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-3300000000000], [7575000000000]) (some (0, 1, 2))
      (some (0, 1, 2)) (.next ([-2100000000000], [3525000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-4725000000000], [5475000000000]) (some (0, 1, 2)) (some (0, 3, 2)) (.terminal (some
      (0, 3, 2)) (some (0, 3, 0)) (some (0, 3, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
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

end Sint350000360000
end ConwaySoifer.Simplified.Certificates

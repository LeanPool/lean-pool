/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext230000240000
import Mathlib.Tactic.FinCases

/-!
# Sext 230000 240000 7

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
namespace Sext230000240000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan56Owner5Part0 : FanWitness := (.next ([2070000000000, 9000000000000], [5640000000000, 0])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1695000000000, 9000000000000], [5550000000000, 0])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([1296000000000, 9000000000000], [5274000000000, 0])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 9000000000000], [930000000000, -9000000000000])
    (some (5, 1, 6)) (some (5, 1, 6)) (.next ([0, 0], [2070000000000, 9000000000000]) (some (0, 1,
    6)) (some (0, 1, 6)) (.next ([-375000000000], [5550000000000]) (some (0, 1, 6)) (some (0, 2, 6))
    (.next ([-774000000000], [5274000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-1125000000000], [6300000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-90000000000],
    [465000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2055000000000, 9000000000000],
    [7230000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-366000000000], [1140000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-276000000000], [675000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-1395000000000], [3351000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-2070000000000], [3750000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-4125000000000], [7230000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4710000000000],
    [7710000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-2535000000000], [4125000000000])
    (some (0, 2, 6)) (some (0, 2, 6)) (.next ([-4620000000000], [7245000000000]) (some (0, 2, 6))
    (some (0, 2, 6)) (.next ([-4344000000000], [6570000000000]) (some (0, 2, 6)) (some (0, 2, 6))
    (.next ([-2070000000000], [3000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-5640000000000, 0], [7710000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-5550000000000, 0], [7245000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-5274000000000, 0], [6570000000000, 9000000000000]) (some (0, 2, 6)) (some (0, 2, 6)) (.next
    ([-930000000000, 9000000000000], [930000000000, 0]) (some (0, 2, 6)) (some (0, 2, 6)) (.terminal
    (some (0, 2, 6)) (some (0, 2, 6)) (some (0, 2, 6)))))))))))))))))))))))))))

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan57Owner1Part0 : FanWitness := (.next ([5820000000000, 9000000000000], [720000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4140000000000], [915000000000,
    -9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next ([6750000000000], [2445000000000])
    (some (0, 5, 3)) (some (0, 5, 3)) (.next ([4335000000000], [2400000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([4140000000000], [2985000000000]) (some (0, 5, 3)) (some (0, 5, 3))
    (.next ([3750000000000], [2790000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([2070000000000, 9000000000000], [2070000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([1680000000000, -9000000000000], [2790000000000, 0]) (some (0, 5, 3)) (some (0, 5,
    3)) (.next ([2070000000000, -9000000000000], [5055000000000, 9000000000000]) (some (0, 5, 3))
    (some (0, 5, 3)) (.next ([1695000000000, 9000000000000], [6585000000000]) (some (0, 5, 3)) (some
    (0, 5, 3)) (.next ([0], [2070000000000, 9000000000000]) (some (0, 5, 3)) (some (0, 5, 3)) (.next
    ([-45000000000], [2460000000000]) (some (0, 5, 3)) (some (0, 5, 4)) (.next ([-375000000000],
    [6585000000000]) (some (0, 5, 4)) (some (1, 5, 4)) (.next ([-375000000000, 0], [4515000000000,
    -9000000000000]) (some (1, 5, 4)) (some (1, 5, 4)) (.next ([-720000000000, 9000000000000],
    [6540000000000]) (some (1, 5, 0)) (some (1, 5, 0)) (.next ([-915000000000, 9000000000000],
    [5055000000000, -9000000000000]) (some (1, 5, 0)) (some (1, 5, 0)) (.next ([-2445000000000],
    [9195000000000]) (some (1, 2, 0)) (some (1, 2, 0)) (.next ([-2400000000000], [6735000000000])
    (some (1, 2, 0)) (some (1, 2, 0)) (.next ([-2985000000000], [7125000000000]) (some (1, 2, 0))
    (some (5, 2, 0)) (.next ([-2790000000000], [6540000000000]) (some (5, 2, 0)) (some (5, 2, 0))
    (.next ([-2070000000000, -9000000000000], [4140000000000, 18000000000000]) (some (5, 2, 0))
    (some (5, 2, 0)) (.next ([-2790000000000, 0], [4470000000000, -9000000000000]) (some (5, 2, 0))
    (some (5, 2, 0)) (.next ([-5055000000000, -9000000000000], [7125000000000, 0]) (some (5, 2, 0))
    (some (5, 2, 0)) (.next ([-6585000000000], [8280000000000, 9000000000000]) (some (5, 2, 0))
    (some (5, 2, 0)) (.terminal (some (5, 2, 0)) (some (5, 2, 0)) (some (5, 2,
    0)))))))))))))))))))))))))))

theorem excluded56_1 : ExcludedOn (model56.B 1 ++ [step56.q]) 9000000000000 (model56.caps 1)
    (model56.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
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
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_5 : ExcludedOn (model56.B 5 ++ [step56.q]) 9000000000000 (model56.caps 5)
    (model56.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5175000000000], [375000000000]) (some (6, 0, 2))
      (some (6, 1, 2)) (.next ([4500000000000], [774000000000]) (some (6, 1, 2)) (some (6, 1, 2))
      (.next ([5175000000000], [1125000000000]) (some (6, 1, 2)) (some (6, 1, 2)) (.next
      ([375000000000], [90000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([5175000000000,
      9000000000000], [2055000000000, -9000000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([774000000000], [366000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([399000000000],
      [276000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1956000000000], [1395000000000])
      (some (5, 1, 2)) (some (5, 1, 2)) (.next ([1680000000000], [2070000000000]) (some (5, 1, 2))
      (some (5, 1, 2)) (.next ([3105000000000], [4125000000000]) (some (5, 1, 2)) (some (5, 1, 2))
      (.next ([3000000000000], [4710000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next
      ([1590000000000], [2535000000000]) (some (5, 1, 2)) (some (5, 1, 2)) (.next ([2625000000000],
      [4620000000000]) (some (5, 1, 2)) (some (5, 1, 6)) (.next ([2226000000000], [4344000000000])
      (some (5, 1, 6)) (some (5, 1, 6)) (.next ([930000000000], [2070000000000]) (some (5, 1, 6))
      (some (5, 1, 6)) fan56Owner5Part0)))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded56_6 : ExcludedOn (model56.B 6 ++ [step56.q]) 9000000000000 (model56.caps 6)
    (model56.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4125000000000], [1770000000000]) (some (2, 0,
      1)) (some (2, 0, 2)) (.next ([5895000000000], [2805000000000, -9000000000000]) (some (2, 0,
      2)) (some (2, 0, 2)) (.next ([2070000000000, 9000000000000], [6930000000000, -9000000000000])
      (some (2, 0, 2)) (some (3, 0, 2)) (.next ([300000000000, 9000000000000], [3825000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2070000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-1770000000000], [5895000000000])
      (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2805000000000, 9000000000000], [8700000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-6930000000000, 9000000000000],
      [9000000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-3825000000000, 9000000000000],
      [4125000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded56_7 : ExcludedOn (model56.B 7 ++ [step56.q]) 9000000000000 (model56.caps 7)
    (model56.ord 7) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded56_1
    · exact excluded56_2
    · exact excluded56_3
    · exact excluded56_4
    · exact excluded56_5
    · exact excluded56_6
    · exact excluded56_7
    · exact excluded56_8
    · exact excluded56_9
theorem next56 : model56.insert step56 = model57 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded57_1 : ExcludedOn (model57.B 1 ++ [step57.q]) 9000000000000 (model57.caps 1)
    (model57.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2415000000000], [45000000000]) (some (0, 5, 2))
      (some (0, 5, 3)) (.next ([6210000000000], [375000000000]) (some (0, 5, 3)) (some (0, 5, 3))
      (.next ([4140000000000, -9000000000000], [375000000000, 0]) (some (0, 5, 3)) (some (0, 5, 3))
      fan57Owner1Part0)))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_2 : ExcludedOn (model57.B 2 ++ [step57.q]) 9000000000000 (model57.caps 2)
    (model57.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_3 : ExcludedOn (model57.B 3 ++ [step57.q]) 9000000000000 (model57.caps 3)
    (model57.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_4 : ExcludedOn (model57.B 4 ++ [step57.q]) 9000000000000 (model57.caps 4)
    (model57.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_5 : ExcludedOn (model57.B 5 ++ [step57.q]) 9000000000000 (model57.caps 5)
    (model57.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_6 : ExcludedOn (model57.B 6 ++ [step57.q]) 9000000000000 (model57.caps 6)
    (model57.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4140000000000], [915000000000, -9000000000000])
      (some (2, 0, 1)) (some (2, 0, 2)) (.next ([3945000000000, 9000000000000], [2070000000000,
      -9000000000000]) (some (2, 0, 2)) (some (3, 0, 2)) (.next ([1875000000000], [4140000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([2070000000000, 9000000000000], [6930000000000,
      -9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([0, 0], [2070000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next ([-915000000000, 9000000000000],
      [5055000000000, -9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([-2070000000000,
      9000000000000], [6015000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4140000000000],
      [6015000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-6930000000000, 9000000000000],
      [9000000000000, 0]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_7 : ExcludedOn (model57.B 7 ++ [step57.q]) 9000000000000 (model57.caps 7)
    (model57.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded57_8 : ExcludedOn (model57.B 8 ++ [step57.q]) 9000000000000 (model57.caps 8)
    (model57.ord 8) 0 1 100 := by
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
    · exact (hj rfl).elim
    · exact excluded57_1
    · exact excluded57_2
    · exact excluded57_3
    · exact excluded57_4
    · exact excluded57_5
    · exact excluded57_6
    · exact excluded57_7
    · exact excluded57_8
    · exact excluded57_9
theorem next57 : model57.insert step57 = model58 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext230000240000
end ConwaySoifer.Simplified.Certificates

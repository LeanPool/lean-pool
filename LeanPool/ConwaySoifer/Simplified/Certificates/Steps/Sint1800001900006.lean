/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint180000190000
import Mathlib.Tactic.FinCases

/-!
# Sint 180000 190000 6

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
namespace Sint180000190000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan48Owner6Part0 : FanWitness := (.next ([15000000000], [3585000000000]) (some (6, 3, 7)) (some
    (6, 3, 7)) (.next ([0], [15000000000]) (some (0, 3, 7)) (some (0, 3, 7)) (.next ([-15000000000],
    [4335000000000]) (some (0, 3, 7)) (some (0, 4, 7)) (.next ([-15000000000], [735000000000]) (some
    (0, 4, 7)) (some (0, 4, 7)) (.next ([-30000000000], [750000000000]) (some (0, 4, 7)) (some (1,
    4, 7)) (.next ([-495000000000, -9000000000000], [5760000000000, 9000000000000]) (some (1, 4, 7))
    (some (1, 4, 7)) (.next ([-540000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-1230000000000, -9000000000000], [6480000000000, 9000000000000]) (some (1, 4, 7)) (some
    (1, 4, 7)) (.next ([-1245000000000, -9000000000000], [6480000000000, 9000000000000]) (some (1,
    4, 7)) (some (1, 4, 7)) (.next ([-2625000000000], [7890000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-3360000000000], [8610000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-3375000000000], [8610000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-2160000000000,
    -9000000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-1620000000000,
    -9000000000000], [3240000000000, 18000000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-2520000000000, 9000000000000], [3645000000000, -9000000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-3750000000000, 0], [5370000000000, 9000000000000]) (some (1, 4, 7)) (some (1, 4,
    7)) (.next ([-3630000000000, 9000000000000], [4710000000000]) (some (1, 4, 7)) (some (1, 4, 7))
    (.next ([-4140000000000], [5265000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next
    ([-4290000000000], [5250000000000]) (some (1, 4, 7)) (some (1, 4, 7)) (.next ([-3240000000000,
    9000000000000], [3630000000000, -9000000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-3240000000000, 9000000000000], [3615000000000, -9000000000000]) (some (1, 4, 6)) (some (1, 4,
    6)) (.next ([-4860000000000], [5250000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next
    ([-4860000000000], [5235000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.next ([-3585000000000],
    [3600000000000]) (some (1, 4, 6)) (some (1, 4, 6)) (.terminal (some (1, 4, 6)) (some (1, 4, 6))
    (some (1, 4, 6)))))))))))))))))))))))))))

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4320000000000], [15000000000]) (some (6, 1, 4))
      (some (6, 2, 7)) (.next ([720000000000], [15000000000]) (some (6, 2, 7)) (some (6, 2, 7))
      (.next ([720000000000], [30000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([5265000000000], [495000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next
      ([4710000000000], [540000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([5250000000000],
      [1230000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([5235000000000],
      [1245000000000, 9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([5265000000000],
      [2625000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([5250000000000], [3360000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([5235000000000], [3375000000000]) (some (6, 2, 7))
      (some (6, 2, 7)) (.next ([3090000000000, -9000000000000], [2160000000000, 9000000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1620000000000, 9000000000000], [1620000000000,
      9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1125000000000, 0], [2520000000000,
      -9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1620000000000, 9000000000000],
      [3750000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1080000000000, 9000000000000],
      [3630000000000, -9000000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([1125000000000],
      [4140000000000]) (some (6, 2, 7)) (some (6, 2, 7)) (.next ([960000000000], [4290000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([390000000000, 0], [3240000000000, -9000000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([375000000000, 0], [3240000000000, -9000000000000])
      (some (6, 2, 7)) (some (6, 2, 7)) (.next ([390000000000], [4860000000000]) (some (6, 2, 7))
      (some (6, 3, 7)) (.next ([375000000000], [4860000000000]) (some (6, 3, 7)) (some (6, 3, 7))
      fan48Owner6Part0)))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_8 : ExcludedOn (model48.B 8 ++ [step48.q]) 9000000000000 (model48.caps 8)
    (model48.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact (hj rfl).elim
    · exact excluded48_2
    · exact excluded48_3
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact excluded48_8
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([4155000000000], [720000000000]) (some (4, 1, 1))
      (some (4, 1, 2)) (.next ([5250000000000, 0], [1620000000000, 9000000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([3855000000000], [2520000000000]) (some (4, 1, 2)) (some (4, 1, 2))
      (.next ([2355000000000], [2220000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2235000000000, -9000000000000], [2520000000000, 0]) (some (4, 1, 2)) (some (4, 1, 2)) (.next
      ([2730000000000], [6375000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([375000000000],
      [4155000000000]) (some (4, 1, 2)) (some (4, 1, 2)) (.next ([0], [5250000000000]) (some (4, 1,
      2)) (some (4, 1, 2)) (.next ([-720000000000], [4875000000000]) (some (4, 1, 2)) (some (4, 1,
      3)) (.next ([-1620000000000, -9000000000000], [6870000000000, 9000000000000]) (some (4, 1, 3))
      (some (4, 1, 3)) (.next ([-2520000000000], [6375000000000]) (some (4, 1, 3)) (some (4, 1, 3))
      (.next ([-2220000000000], [4575000000000]) (some (4, 1, 3)) (some (4, 1, 3)) (.next
      ([-2520000000000, 0], [4755000000000, -9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-6375000000000], [9105000000000]) (some (0, 1, 3)) (some (0, 1, 4)) (.next
      ([-4155000000000], [4530000000000]) (some (0, 1, 4)) none (.terminal none (some (1, 1, 4))
      none))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7380000000000, -9000000000000], [1620000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2520000000000], [2625000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2235000000000, -9000000000000], [2520000000000, 0])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([900000000000, -9000000000000], [4245000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([0, 0], [1620000000000,
      9000000000000]) (some (0, 1, 1)) (some (0, 1, 1)) (.next ([-1620000000000, -9000000000000],
      [9000000000000, 0]) (some (0, 1, 1)) (some (0, 1, 2)) (.next ([-2625000000000],
      [5145000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2520000000000, 0],
      [4755000000000, -9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4245000000000,
      -9000000000000], [5145000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_4 : ExcludedOn (model49.B 4 ++ [step49.q]) 9000000000000 (model49.caps 4)
    (model49.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 7) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded49_1
    · exact excluded49_2
    · exact excluded49_3
    · exact excluded49_4
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint180000190000
end ConwaySoifer.Simplified.Certificates

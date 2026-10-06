/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown290000300000
import Mathlib.Tactic.FinCases

/-!
# Aown 290000 300000 1

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
namespace Aown290000300000

/-- Shared exact orientation-fan tail for this local exclusion. -/
def fan12Owner0Part0 : FanWitness := (.next ([960000000000], [4470000000000]) (some (0, 3, 6)) (some
    (0, 3, 6)) (.next ([765000000000], [4665000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next
    ([765000000000], [5895000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([0], [195000000000])
    (some (0, 3, 6)) (some (0, 6, 6)) (.next ([-570000000000], [5835000000000]) (some (0, 6, 6))
    (some (0, 6, 6)) (.next ([-435000000000], [4140000000000]) (some (0, 6, 6)) (some (0, 6, 6))
    (.next ([-375000000000], [2745000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next
    ([-1395000000000], [7890000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1230000000000],
    [5730000000000]) (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-960000000000], [3750000000000])
    (some (0, 6, 4)) (some (0, 6, 4)) (.next ([-1680000000000], [6390000000000]) (some (0, 6, 4))
    (some (0, 6, 5)) (.next ([-1875000000000], [6390000000000]) (some (0, 6, 5)) (some (0, 6, 5))
    (.next ([-930000000000], [2190000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next
    ([-930000000000], [1995000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-555000000000],
    [1110000000000]) (some (0, 6, 5)) (some (0, 6, 5)) (.next ([-2940000000000], [5460000000000])
    (some (0, 6, 5)) (some (1, 6, 5)) (.next ([-750000000000], [1305000000000]) (some (1, 6, 5))
    (some (1, 6, 5)) (.next ([-6270000000000], [9405000000000]) (some (1, 6, 5)) (some (1, 6, 5))
    (.next ([-3360000000000], [4875000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next
    ([-6825000000000], [8850000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-6825000000000],
    [8655000000000]) (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-4470000000000], [5430000000000])
    (some (1, 6, 5)) (some (1, 6, 5)) (.next ([-4665000000000], [5430000000000]) (some (1, 6, 5))
    (some (1, 6, 5)) (.next ([-5895000000000], [6660000000000]) (some (1, 6, 5)) (some (1, 6, 5))
    (.terminal (some (1, 6, 5)) (some (1, 6, 5)) (some (1, 6, 5)))))))))))))))))))))))))))

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6390000000000, -9000000000000], [2610000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5448000000000, 0], [2610000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2265000000000, -9000000000000],
      [2820000000000, 9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1230000000000],
      [4218000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([1305000000000, -9000000000000],
      [4875000000000, 0]) (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1230000000000, 0],
      [5160000000000, -9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([1020000000000],
      [5085000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([363000000000], [4875000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [3840000000000, 9000000000000]) (some (0, 1,
      2)) (some (0, 1, 2)) (.next ([-2610000000000, -9000000000000], [9000000000000, 0]) (some (0,
      1, 2)) (some (0, 1, 2)) (.next ([-2610000000000, -9000000000000], [8058000000000,
      9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2820000000000, -9000000000000],
      [5085000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-4218000000000], [5448000000000])
      (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-4875000000000, 0], [6180000000000,
      -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5160000000000, 9000000000000],
      [6390000000000, -9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-5085000000000],
      [6105000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-4875000000000], [5238000000000])
      (some (3, 1, 2)) (some (3, 1, 2)) (.terminal (some (3, 1, 2)) (some (3, 1, 0)) (some (3, 1,
      2))))))))))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5085000000000, 0], [1515000000000,
      -9000000000000]) (some (1, 0, 3)) (some (2, 0, 3)) (.next ([5085000000000], [4125000000000])
      (some (2, 0, 3)) (some (2, 0, 3)) (.next ([2610000000000, 9000000000000], [2610000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([2475000000000, -9000000000000],
      [6735000000000, 9000000000000]) (some (2, 0, 3)) (some (2, 0, 3)) (.next ([0], [2610000000000,
      9000000000000]) (some (2, 0, 3)) (some (2, 3, 3)) (.next ([-1515000000000, 9000000000000],
      [6600000000000, -9000000000000]) (some (0, 3, 3)) (some (0, 3, 3)) (.next ([-4125000000000],
      [9210000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-2610000000000, -9000000000000],
      [5220000000000, 18000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([-6735000000000,
      -9000000000000], [9210000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.terminal (some (0, 3,
      1)) (some (0, 3, 1)) (some (0, 3, 1))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_6 : ExcludedOn (model8.B 6 ++ [step8.q]) 9000000000000 (model8.caps 6) (model8.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked8 : StepValid model8 9000000000000 step8 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact excluded8_6
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_1 : ExcludedOn (model9.B 1 ++ [step9.q]) 9000000000000 (model9.caps 1) (model9.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6015000000000, -9000000000000], [1170000000000,
      9000000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next ([2610000000000, 9000000000000],
      [2610000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 3)) (.next ([4050000000000,
      9000000000000], [4575000000000, -9000000000000]) (some (3, 1, 3)) (some (3, 1, 3)) (.next
      ([1440000000000], [7185000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0],
      [2610000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-1170000000000,
      -9000000000000], [7185000000000]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2610000000000,
      -9000000000000], [5220000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-4575000000000, 9000000000000], [8625000000000, 0]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-7185000000000], [8625000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 2, 3)) (some (0, 2, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([7185000000000], [375000000000]) (some (3, 0, 1))
      (some (3, 0, 2)) (.next ([2610000000000, 9000000000000], [5640000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([2235000000000, 9000000000000], [4950000000000, -9000000000000])
      (some (3, 0, 2)) (some (3, 0, 2)) (.next ([1545000000000], [6015000000000]) (some (3, 0, 2))
      (some (3, 0, 2)) (.next ([0, 0], [2610000000000, 9000000000000]) (some (3, 0, 2)) (some (3, 0,
      2)) (.next ([-375000000000], [7560000000000]) (some (3, 0, 2)) (some (3, 1, 2)) (.next
      ([-5640000000000, 0], [8250000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-4950000000000, 9000000000000], [7185000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-6015000000000], [7560000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1,
      2)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded9_1
    · exact excluded9_2
    · exact excluded9_3
    · exact excluded9_4
    · exact excluded9_5
    · exact excluded9_6
    · exact excluded9_7
    · exact excluded9_8
    · exact excluded9_9
theorem next9 : model9.insert step9 = model10 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded10_0 : ExcludedOn (model10.B 0 ++ [step10.q]) 9000000000000 (model10.caps 0)
    (model10.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_7 : ExcludedOn (model10.B 7 ++ [step10.q]) 9000000000000 (model10.caps 7)
    (model10.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3810000000000], [2220000000000]) (some (2, 0,
      1)) (some (4, 0, 2)) (.next ([2610000000000, 9000000000000], [2580000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([2970000000000, 0], [3420000000000, -9000000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([1200000000000, -9000000000000], [2610000000000,
      9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0], [6390000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2220000000000], [6030000000000])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-2580000000000, 9000000000000], [5190000000000, 0])
      (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-3420000000000, 9000000000000], [6390000000000,
      -9000000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-2610000000000, -9000000000000],
      [3810000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.terminal (some (0, 1, 2)) (some (0, 1,
      2)) (some (0, 1, 2))))))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded10_0
    · exact excluded10_1
    · exact (hj rfl).elim
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact excluded10_7
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3735000000000, 9000000000000], [1305000000000,
      -9000000000000]) none none (.next ([2430000000000, -9000000000000], [1485000000000,
      9000000000000]) none none (.next ([5040000000000], [3690000000000]) none none (.next
      ([2610000000000, 9000000000000], [2205000000000, -9000000000000]) none none (.next
      ([2610000000000, 9000000000000], [2610000000000, 9000000000000]) none none (.next ([0],
      [7425000000000, 9000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1305000000000,
      9000000000000], [5040000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-1485000000000,
      -9000000000000], [3915000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-3690000000000], [8730000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2205000000000,
      9000000000000], [4815000000000, 0]) (some (3, 1, 2)) (some (3, 1, 2)) (.next ([-2610000000000,
      -9000000000000], [5220000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.terminal
      (some (3, 1, 2)) none none))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6885000000000], [990000000000]) (some (0, 3, 1))
      (some (0, 3, 1)) (.next ([6390000000000, -9000000000000], [2610000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([5448000000000, 0], [2610000000000, 9000000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2430000000000, -9000000000000], [1485000000000,
      9000000000000]) (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2970000000000], [2478000000000])
      (some (0, 3, 1)) (some (0, 3, 1)) (.next ([2970000000000, 0], [3420000000000, -9000000000000])
      (some (0, 3, 1)) (some (0, 3, 2)) (.next ([1488000000000], [2427000000000]) (some (0, 3, 2))
      (some (0, 3, 2)) (.next ([1305000000000, -9000000000000], [6570000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0, 0], [5580000000000, 9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-990000000000], [7875000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-2610000000000, -9000000000000], [9000000000000, 0]) (some (0, 3, 2)) (some (0,
      3, 2)) (.next ([-2610000000000, -9000000000000], [8058000000000, 9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-1485000000000, -9000000000000], [3915000000000, 0]) (some (0,
      3, 2)) (some (0, 3, 2)) (.next ([-2478000000000], [5448000000000]) (some (0, 3, 2)) (some (0,
      3, 2)) (.next ([-3420000000000, 9000000000000], [6390000000000, -9000000000000]) (some (0, 3,
      2)) (some (0, 3, 2)) (.next ([-2427000000000], [3915000000000]) (some (0, 3, 2)) (some (0, 3,
      2)) (.next ([-6570000000000, -9000000000000], [7875000000000]) (some (0, 1, 2)) (some (0, 1,
      2)) (.terminal (some (0, 1, 2)) (some (3, 1, 0)) (some (3, 1, 2))))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded11_3 : ExcludedOn (model11.B 3 ++ [step11.q]) 9000000000000 (model11.caps 3)
    (model11.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked11 : StepValid model11 9000000000000 step11 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded11_1
    · exact excluded11_2
    · exact excluded11_3
    · exact excluded11_4
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_0 : ExcludedOn (model12.B 0 ++ [step12.q]) 9000000000000 (model12.caps 0)
    (model12.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5265000000000], [570000000000]) (some (5, 1, 6))
      (some (5, 2, 6)) (.next ([3705000000000], [435000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      (.next ([2370000000000], [375000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
      ([6495000000000], [1395000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([4500000000000],
      [1230000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([2790000000000], [960000000000])
      (some (5, 2, 6)) (some (5, 2, 6)) (.next ([4710000000000], [1680000000000]) (some (5, 2, 6))
      (some (5, 2, 6)) (.next ([4515000000000], [1875000000000]) (some (5, 2, 6)) (some (5, 2, 6))
      (.next ([1260000000000], [930000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next
      ([1065000000000], [930000000000]) (some (5, 2, 6)) (some (5, 2, 6)) (.next ([555000000000],
      [555000000000]) (some (5, 2, 6)) (some (5, 3, 6)) (.next ([2520000000000], [2940000000000])
      (some (5, 3, 6)) (some (5, 3, 6)) (.next ([555000000000], [750000000000]) (some (5, 3, 6))
      (some (5, 3, 6)) (.next ([3135000000000], [6270000000000]) (some (5, 3, 6)) (some (5, 3, 6))
      (.next ([1515000000000], [3360000000000]) (some (5, 3, 6)) (some (5, 3, 6)) (.next
      ([2025000000000], [6825000000000]) (some (0, 3, 6)) (some (0, 3, 6)) (.next ([1830000000000],
      [6825000000000]) (some (0, 3, 6)) (some (0, 3, 6)) fan12Owner0Part0)))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([3480000000000, 0], [1710000000000,
      9000000000000]) none none (.next ([2610000000000, 9000000000000], [2205000000000,
      -9000000000000]) (some (2, 3, 2)) (some (2, 3, 2)) (.next ([2610000000000, 9000000000000],
      [2610000000000, 9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([900000000000],
      [7395000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0], [7425000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 1, 2)) (.next ([-1710000000000, -9000000000000],
      [5190000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([-2205000000000,
      9000000000000], [4815000000000, 0]) (some (0, 1, 2)) (some (3, 1, 2)) (.next ([-2610000000000,
      -9000000000000], [5220000000000, 18000000000000]) (some (3, 1, 2)) (some (3, 1, 2)) (.next
      ([-7395000000000], [8295000000000]) (some (3, 1, 2)) none (.terminal none none none)))))))))))
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded12_0
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact excluded12_4
    · exact excluded12_5
    · exact (hj rfl).elim
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 6) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([2610000000000, 9000000000000], [2205000000000,
      -9000000000000]) none none (.next ([3000000000000, 0], [2610000000000, 9000000000000]) (some
      (0, 3, 2)) (some (0, 3, 2)) (.next ([2610000000000, 9000000000000], [2610000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([0], [7425000000000, 9000000000000])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2205000000000, 9000000000000], [4815000000000, 0])
      (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2610000000000, -9000000000000], [5610000000000,
      9000000000000]) (some (0, 3, 2)) (some (0, 3, 2)) (.next ([-2610000000000, -9000000000000],
      [5220000000000, 18000000000000]) (some (0, 3, 2)) (some (3, 3, 2)) (.terminal (some (3, 3, 2))
      none none))))))))) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  decide +kernel

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_5 : ExcludedOn (model13.B 5 ++ [step13.q]) 9000000000000 (model13.caps 5)
    (model13.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked13 : StepValid model13 9000000000000 step13 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded13_0
    · exact excluded13_1
    · exact excluded13_2
    · exact excluded13_3
    · exact excluded13_4
    · exact excluded13_5
    · exact (hj rfl).elim
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([6090000000000, 9000000000000], [3015000000000,
      -9000000000000]) (some (3, 0, 3)) (some (3, 1, 3)) (.next ([2610000000000, 9000000000000],
      [2610000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([3480000000000],
      [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([870000000000, -9000000000000],
      [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([0, 0], [2610000000000,
      9000000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.next ([-3015000000000, 9000000000000],
      [9105000000000, 0]) (some (0, 1, 3)) (some (0, 2, 3)) (.next ([-2610000000000,
      -9000000000000], [5220000000000, 18000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next
      ([-5625000000000], [9105000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-5625000000000,
      0], [6495000000000, -9000000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.terminal (some (0, 2,
      3)) (some (0, 3, 3)) (some (0, 3, 3))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan (.next ([5520000000000], [375000000000]) (some (3, 0, 1))
      (some (3, 0, 2)) (.next ([5520000000000], [900000000000]) (some (3, 0, 2)) (some (3, 0, 2))
      (.next ([4620000000000], [795000000000]) (some (3, 0, 2)) (some (3, 0, 2)) (.next
      ([2715000000000, 9000000000000], [2910000000000, -9000000000000]) (some (3, 0, 2)) (some (4,
      0, 2)) (.next ([420000000000], [480000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([2610000000000, 9000000000000], [6000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([1710000000000, 9000000000000], [6420000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next
      ([105000000000], [5520000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([0, 0],
      [2610000000000, 9000000000000]) (some (4, 0, 2)) (some (4, 0, 2)) (.next ([-375000000000],
      [5895000000000]) (some (4, 0, 2)) (some (4, 1, 2)) (.next ([-900000000000], [6420000000000])
      (some (4, 1, 2)) (some (4, 1, 2)) (.next ([-795000000000], [5415000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-2910000000000, 9000000000000], [5625000000000]) (some (4, 1, 2))
      (some (4, 1, 2)) (.next ([-480000000000], [900000000000]) (some (0, 1, 2)) (some (0, 1, 2))
      (.next ([-6000000000000, 0], [8610000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 3))
      (.next ([-6420000000000, 0], [8130000000000, 9000000000000]) (some (0, 1, 3)) (some (0, 1, 3))
      (.next ([-5520000000000], [5625000000000]) (some (0, 1, 3)) (some (0, 1, 3)) (.terminal (some
      (0, 1, 3)) (some (0, 1, 3)) (some (0, 1, 3))))))))))))))))))))) (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  decide +kernel

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  decide +kernel

theorem checked14 : StepValid model14 9000000000000 step14 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded14_1
    · exact excluded14_2
    · exact excluded14_3
    · exact excluded14_4
    · exact excluded14_5
    · exact excluded14_6
    · exact excluded14_7
    · exact excluded14_8
    · exact excluded14_9
theorem next14 : model14.insert step14 = model15 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown290000300000
end ConwaySoifer.Simplified.Certificates

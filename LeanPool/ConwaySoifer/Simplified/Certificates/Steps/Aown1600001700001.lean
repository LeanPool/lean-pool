/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1600001700001
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part0
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part1
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part2
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part3
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part4
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part5
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part6
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part7
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1600001700001Part8

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown160000170000

/-!
# Aown 160000 170000 1

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
namespace Aown160000170000

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan8Owner0Part0 :
    fan8Owner0Part0.check (model8.B 0 ++ [step8.q]) 9000000000000
      (model8.caps 0) 0 1 100 12
      ([261600000000, -2490000000000], [796800000000, 4980000000000]) = true := by
  decide +kernel

theorem excluded8_0 : ExcludedOn (model8.B 0 ++ [step8.q]) 9000000000000 (model8.caps 0) (model8.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded8Owner0)
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded8Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan8Owner0Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded8_1 : ExcludedOn (model8.B 1 ++ [step8.q]) 9000000000000 (model8.caps 1) (model8.ord
    1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_1

theorem excluded8_2 : ExcludedOn (model8.B 2 ++ [step8.q]) 9000000000000 (model8.caps 2) (model8.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_2

theorem excluded8_3 : ExcludedOn (model8.B 3 ++ [step8.q]) 9000000000000 (model8.caps 3) (model8.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_3

theorem excluded8_4 : ExcludedOn (model8.B 4 ++ [step8.q]) 9000000000000 (model8.caps 4) (model8.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_4

theorem excluded8_5 : ExcludedOn (model8.B 5 ++ [step8.q]) 9000000000000 (model8.caps 5) (model8.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_5

theorem excluded8_7 : ExcludedOn (model8.B 7 ++ [step8.q]) 9000000000000 (model8.caps 7) (model8.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_7

theorem excluded8_8 : ExcludedOn (model8.B 8 ++ [step8.q]) 9000000000000 (model8.caps 8) (model8.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_8

theorem excluded8_9 : ExcludedOn (model8.B 9 ++ [step8.q]) 9000000000000 (model8.caps 9) (model8.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded8_9

theorem checked8 : StepValid model8 9000000000000 step8 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded8_0
    · exact excluded8_1
    · exact excluded8_2
    · exact excluded8_3
    · exact excluded8_4
    · exact excluded8_5
    · exact (hj rfl).elim
    · exact excluded8_7
    · exact excluded8_8
    · exact excluded8_9
theorem next8 : model8.insert step8 = model9 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded9_0 : ExcludedOn (model9.B 0 ++ [step9.q]) 9000000000000 (model9.caps 0) (model9.ord
    0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_0

theorem excluded9_2 : ExcludedOn (model9.B 2 ++ [step9.q]) 9000000000000 (model9.caps 2) (model9.ord
    2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_2

theorem excluded9_3 : ExcludedOn (model9.B 3 ++ [step9.q]) 9000000000000 (model9.caps 3) (model9.ord
    3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_3

theorem excluded9_4 : ExcludedOn (model9.B 4 ++ [step9.q]) 9000000000000 (model9.caps 4) (model9.ord
    4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_4

theorem excluded9_5 : ExcludedOn (model9.B 5 ++ [step9.q]) 9000000000000 (model9.caps 5) (model9.ord
    5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_5

theorem excluded9_6 : ExcludedOn (model9.B 6 ++ [step9.q]) 9000000000000 (model9.caps 6) (model9.ord
    6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_6

theorem excluded9_7 : ExcludedOn (model9.B 7 ++ [step9.q]) 9000000000000 (model9.caps 7) (model9.ord
    7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded9Owner7)
      (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded9Owner7
  as_aux_lemma => exact checkedWitnessForExcluded9_7

theorem excluded9_8 : ExcludedOn (model9.B 8 ++ [step9.q]) 9000000000000 (model9.caps 8) (model9.ord
    8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_8

theorem excluded9_9 : ExcludedOn (model9.B 9 ++ [step9.q]) 9000000000000 (model9.caps 9) (model9.ord
    9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded9_9

theorem checked9 : StepValid model9 9000000000000 step9 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded9_0
    · exact (hj rfl).elim
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
  apply ExclusionHint.sound (.pair 0 10) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_0

theorem excluded10_1 : ExcludedOn (model10.B 1 ++ [step10.q]) 9000000000000 (model10.caps 1)
    (model10.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded10Owner1)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded10Owner1
  as_aux_lemma => exact checkedWitnessForExcluded10_1

theorem excluded10_2 : ExcludedOn (model10.B 2 ++ [step10.q]) 9000000000000 (model10.caps 2)
    (model10.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_2

theorem excluded10_3 : ExcludedOn (model10.B 3 ++ [step10.q]) 9000000000000 (model10.caps 3)
    (model10.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_3

theorem excluded10_4 : ExcludedOn (model10.B 4 ++ [step10.q]) 9000000000000 (model10.caps 4)
    (model10.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_4

theorem excluded10_5 : ExcludedOn (model10.B 5 ++ [step10.q]) 9000000000000 (model10.caps 5)
    (model10.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_5

theorem excluded10_6 : ExcludedOn (model10.B 6 ++ [step10.q]) 9000000000000 (model10.caps 6)
    (model10.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_6

theorem excluded10_8 : ExcludedOn (model10.B 8 ++ [step10.q]) 9000000000000 (model10.caps 8)
    (model10.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_8

theorem excluded10_9 : ExcludedOn (model10.B 9 ++ [step10.q]) 9000000000000 (model10.caps 9)
    (model10.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded10_9

theorem checked10 : StepValid model10 9000000000000 step10 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded10_0
    · exact excluded10_1
    · exact excluded10_2
    · exact excluded10_3
    · exact excluded10_4
    · exact excluded10_5
    · exact excluded10_6
    · exact (hj rfl).elim
    · exact excluded10_8
    · exact excluded10_9
theorem next10 : model10.insert step10 = model11 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan11Owner0Part0 :
    fan11Owner0Part0.check (model11.B 0 ++ [step11.q]) 9000000000000
      (model11.caps 0) 0 1 100 12
      ([398400000000, 2490000000000], [1838400000000, 2490000000000]) = true := by
  decide +kernel

theorem excluded11_0 : ExcludedOn (model11.B 0 ++ [step11.q]) 9000000000000 (model11.caps 0)
    (model11.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded11Owner0)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded11Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan11Owner0Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded11_1 : ExcludedOn (model11.B 1 ++ [step11.q]) 9000000000000 (model11.caps 1)
    (model11.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_1

theorem excluded11_2 : ExcludedOn (model11.B 2 ++ [step11.q]) 9000000000000 (model11.caps 2)
    (model11.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_2

theorem excluded11_4 : ExcludedOn (model11.B 4 ++ [step11.q]) 9000000000000 (model11.caps 4)
    (model11.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_4

theorem excluded11_5 : ExcludedOn (model11.B 5 ++ [step11.q]) 9000000000000 (model11.caps 5)
    (model11.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_5

theorem excluded11_6 : ExcludedOn (model11.B 6 ++ [step11.q]) 9000000000000 (model11.caps 6)
    (model11.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_6

theorem excluded11_7 : ExcludedOn (model11.B 7 ++ [step11.q]) 9000000000000 (model11.caps 7)
    (model11.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_7

theorem excluded11_8 : ExcludedOn (model11.B 8 ++ [step11.q]) 9000000000000 (model11.caps 8)
    (model11.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_8

theorem excluded11_9 : ExcludedOn (model11.B 9 ++ [step11.q]) 9000000000000 (model11.caps 9)
    (model11.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded11_9

theorem checked11 : StepValid model11 9000000000000 step11 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded11_0
    · exact excluded11_1
    · exact excluded11_2
    · exact (hj rfl).elim
    · exact excluded11_4
    · exact excluded11_5
    · exact excluded11_6
    · exact excluded11_7
    · exact excluded11_8
    · exact excluded11_9
theorem next11 : model11.insert step11 = model12 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded12_1 : ExcludedOn (model12.B 1 ++ [step12.q]) 9000000000000 (model12.caps 1)
    (model12.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded12_1

theorem excluded12_2 : ExcludedOn (model12.B 2 ++ [step12.q]) 9000000000000 (model12.caps 2)
    (model12.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded12Owner2)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded12Owner2
  as_aux_lemma => exact checkedWitnessForExcluded12_2

theorem excluded12_3 : ExcludedOn (model12.B 3 ++ [step12.q]) 9000000000000 (model12.caps 3)
    (model12.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded12Owner3)
      (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded12Owner3
  as_aux_lemma => exact checkedWitnessForExcluded12_3

theorem excluded12_4 : ExcludedOn (model12.B 4 ++ [step12.q]) 9000000000000 (model12.caps 4)
    (model12.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded12_4

theorem excluded12_5 : ExcludedOn (model12.B 5 ++ [step12.q]) 9000000000000 (model12.caps 5)
    (model12.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded12_5

theorem excluded12_6 : ExcludedOn (model12.B 6 ++ [step12.q]) 9000000000000 (model12.caps 6)
    (model12.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded12_6

theorem excluded12_7 : ExcludedOn (model12.B 7 ++ [step12.q]) 9000000000000 (model12.caps 7)
    (model12.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded12_7

theorem excluded12_8 : ExcludedOn (model12.B 8 ++ [step12.q]) 9000000000000 (model12.caps 8)
    (model12.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded12_8

theorem excluded12_9 : ExcludedOn (model12.B 9 ++ [step12.q]) 9000000000000 (model12.caps 9)
    (model12.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded12_9

theorem checked12 : StepValid model12 9000000000000 step12 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded12_1
    · exact excluded12_2
    · exact excluded12_3
    · exact excluded12_4
    · exact excluded12_5
    · exact excluded12_6
    · exact excluded12_7
    · exact excluded12_8
    · exact excluded12_9
theorem next12 : model12.insert step12 = model13 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded13_0 : ExcludedOn (model13.B 0 ++ [step13.q]) 9000000000000 (model13.caps 0)
    (model13.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 7 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_0

theorem excluded13_1 : ExcludedOn (model13.B 1 ++ [step13.q]) 9000000000000 (model13.caps 1)
    (model13.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_1

theorem excluded13_2 : ExcludedOn (model13.B 2 ++ [step13.q]) 9000000000000 (model13.caps 2)
    (model13.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_2

theorem excluded13_3 : ExcludedOn (model13.B 3 ++ [step13.q]) 9000000000000 (model13.caps 3)
    (model13.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_3

theorem excluded13_4 : ExcludedOn (model13.B 4 ++ [step13.q]) 9000000000000 (model13.caps 4)
    (model13.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_4

theorem excluded13_6 : ExcludedOn (model13.B 6 ++ [step13.q]) 9000000000000 (model13.caps 6)
    (model13.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_6

theorem excluded13_7 : ExcludedOn (model13.B 7 ++ [step13.q]) 9000000000000 (model13.caps 7)
    (model13.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_7

theorem excluded13_8 : ExcludedOn (model13.B 8 ++ [step13.q]) 9000000000000 (model13.caps 8)
    (model13.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded13_8

theorem excluded13_9 : ExcludedOn (model13.B 9 ++ [step13.q]) 9000000000000 (model13.caps 9)
    (model13.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded13Owner9)
      (den
      := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded13Owner9
  as_aux_lemma => exact checkedWitnessForExcluded13_9

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
    · exact (hj rfl).elim
    · exact excluded13_6
    · exact excluded13_7
    · exact excluded13_8
    · exact excluded13_9
theorem next13 : model13.insert step13 = model14 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded14_1 : ExcludedOn (model14.B 1 ++ [step14.q]) 9000000000000 (model14.caps 1)
    (model14.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded14Owner1)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  delta witnessForExcluded14Owner1
  as_aux_lemma => exact checkedWitnessForExcluded14_1

theorem excluded14_2 : ExcludedOn (model14.B 2 ++ [step14.q]) 9000000000000 (model14.caps 2)
    (model14.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded14Owner2)
      (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded14Owner2
  as_aux_lemma => exact checkedWitnessForExcluded14_2

theorem excluded14_3 : ExcludedOn (model14.B 3 ++ [step14.q]) 9000000000000 (model14.caps 3)
    (model14.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded14_3

theorem excluded14_4 : ExcludedOn (model14.B 4 ++ [step14.q]) 9000000000000 (model14.caps 4)
    (model14.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded14_4

theorem excluded14_5 : ExcludedOn (model14.B 5 ++ [step14.q]) 9000000000000 (model14.caps 5)
    (model14.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded14_5

theorem excluded14_6 : ExcludedOn (model14.B 6 ++ [step14.q]) 9000000000000 (model14.caps 6)
    (model14.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded14_6

theorem excluded14_7 : ExcludedOn (model14.B 7 ++ [step14.q]) 9000000000000 (model14.caps 7)
    (model14.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded14_7

theorem excluded14_8 : ExcludedOn (model14.B 8 ++ [step14.q]) 9000000000000 (model14.caps 8)
    (model14.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded14_8

theorem excluded14_9 : ExcludedOn (model14.B 9 ++ [step14.q]) 9000000000000 (model14.caps 9)
    (model14.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded14_9

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

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan15Owner0Part5Checks :
    (fan15Owner0Part0.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 0 740624 318861100 12
      ([-660000000000], [2100000000000]) = true) ∧
    (fan15Owner0Part1.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 0 740624 318861100 12
      ([2193600000000, -2490000000000], [2329800000000, 4980000000000]) = true) ∧
    (fan15Owner0Part2.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 740624 2083888 318861100 12
      ([-1533000000000], [4785000000000]) = true) ∧
    (fan15Owner0Part3.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 740624 2083888 318861100 12
      ([796800000000, 4980000000000], [1041600000000, -2490000000000]) = true) ∧
    (fan15Owner0Part4.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 2224 3403 340300 12
      ([-1533000000000], [4785000000000]) = true) ∧
    (fan15Owner0Part5.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 2224 3403 340300 12
      ([660000000000], [780000000000]) = true) := by
  have checkedTail0 :
      fan15Owner0Part0.check (model15.B 0 ++ [step15.q]) 9000000000000
        (model15.caps 0) 0 740624 318861100 12
        ([-660000000000], [2100000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan15Owner0Part1.check (model15.B 0 ++ [step15.q]) 9000000000000
        (model15.caps 0) 0 740624 318861100 12
        ([2193600000000, -2490000000000], [2329800000000, 4980000000000]) = true := by
    delta fan15Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail2 :
      fan15Owner0Part2.check (model15.B 0 ++ [step15.q]) 9000000000000
        (model15.caps 0) 740624 2083888 318861100 12
        ([-1533000000000], [4785000000000]) = true := by
    decide +kernel
  have checkedTail3 :
      fan15Owner0Part3.check (model15.B 0 ++ [step15.q]) 9000000000000
        (model15.caps 0) 740624 2083888 318861100 12
        ([796800000000, 4980000000000], [1041600000000, -2490000000000]) = true := by
    delta fan15Owner0Part3
    simp only [FanWitness.check, checkedTail2,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail4 :
      fan15Owner0Part4.check (model15.B 0 ++ [step15.q]) 9000000000000
        (model15.caps 0) 2224 3403 340300 12
        ([-1533000000000], [4785000000000]) = true := by
    decide +kernel
  have checkedTail5 :
      fan15Owner0Part5.check (model15.B 0 ++ [step15.q]) 9000000000000
        (model15.caps 0) 2224 3403 340300 12
        ([660000000000], [780000000000]) = true := by
    delta fan15Owner0Part5
    simp only [FanWitness.check, checkedTail4,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1, checkedTail2, checkedTail3, checkedTail4, checkedTail5⟩

private theorem checkedFan15Owner0Part1 :
    fan15Owner0Part1.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 0 740624 318861100 12
      ([2193600000000, -2490000000000], [2329800000000, 4980000000000]) = true := by
  exact checkedFan15Owner0Part5Checks.2.1

private theorem checkedFan15Owner0Part3 :
    fan15Owner0Part3.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 740624 2083888 318861100 12
      ([796800000000, 4980000000000], [1041600000000, -2490000000000]) = true := by
  exact checkedFan15Owner0Part5Checks.2.2.2.1

private theorem checkedFan15Owner0Part5 :
    fan15Owner0Part5.check (model15.B 0 ++ [step15.q]) 9000000000000
      (model15.caps 0) 2224 3403 340300 12
      ([660000000000], [780000000000]) = true := by
  exact checkedFan15Owner0Part5Checks.2.2.2.2.2

theorem excluded15_0 : ExcludedOn (model15.B 0 ++ [step15.q]) 9000000000000 (model15.caps 0)
    (model15.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (2224) (3403) (340300) (.split (0) (740624) (2083888)
      (318861100) (.witnessedFan (.next ([2592000000000], [93000000000]) (some (10, 2, 10)) (some
      (10, 2, 10)) (.next ([1838400000000, 2490000000000], [398400000000, 2490000000000]) (some (10,
      2, 10)) (some (10, 2, 10)) (.next ([3252000000000], [873000000000]) (some (10, 2, 10)) (some
      (10, 2, 10)) (.next ([796800000000, 4980000000000], [261600000000, -2490000000000]) (some (10,
      2, 10)) (some (10, 2, 10)) (.next ([3388800000000, 4980000000000], [1134600000000,
      -2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([1058400000000, 2490000000000],
      [398400000000, 2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([1440000000000],
      [660000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([3252000000000],
      [1533000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([261600000000, -2490000000000],
      [136800000000, 4980000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([2990400000000,
      2490000000000], [1931400000000, 2490000000000]) (some (10, 2, 10)) (some (10, 3, 10)) (.next
      ([1041600000000, -2490000000000], [796800000000, 4980000000000]) (some (10, 3, 10)) (some (10,
      3, 10)) (.next ([2592000000000], [2193000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
      ([780000000000], [660000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([398400000000,
      2490000000000], [398400000000, 2490000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next
      ([2193600000000, -2490000000000], [2329800000000, 4980000000000]) (some (10, 3, 10)) (some
      (10, 3, 10)) fan15Owner0Part1)))))))))))))))) (.witnessedFan (.next ([2592000000000],
      [93000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([1838400000000, 2490000000000],
      [398400000000, 2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([3252000000000],
      [873000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([796800000000, 4980000000000],
      [261600000000, -2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([3388800000000,
      4980000000000], [1134600000000, -2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([1058400000000, 2490000000000], [398400000000, 2490000000000]) (some (10, 2, 10)) (some (10,
      2, 10)) (.next ([1440000000000], [660000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([3252000000000], [1533000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([261600000000, -2490000000000], [136800000000, 4980000000000]) (some (10, 2, 10)) (some (10,
      2, 10)) (.next ([1041600000000, -2490000000000], [796800000000, 4980000000000]) (some (10, 2,
      10)) (some (10, 3, 10)) (.next ([2592000000000], [2193000000000]) (some (10, 3, 10)) (some
      (10, 3, 10)) (.next ([780000000000], [660000000000]) (some (10, 3, 10)) (some (10, 3, 10))
      (.next ([398400000000, 2490000000000], [398400000000, 2490000000000]) (some (10, 3, 10)) (some
      (10, 3, 10)) (.next ([2193600000000, -2490000000000], [2329800000000, 4980000000000]) (some
      (10, 3, 10)) (some (10, 3, 10)) (.next ([1932000000000], [2193000000000]) (some (10, 3, 10))
      (some (10, 3, 10)) (.next ([660000000000], [780000000000]) (some (10, 3, 10)) (some (10, 3,
      10)) (.next ([796800000000, 4980000000000], [1041600000000, -2490000000000]) (some (10, 3,
      10)) (some (10, 3, 10)) fan15Owner0Part3))))))))))))))))))) (.witnessedFan (.next
      ([2592000000000], [93000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([1838400000000,
      2490000000000], [398400000000, 2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([3252000000000], [873000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next ([796800000000,
      4980000000000], [261600000000, -2490000000000]) (some (10, 2, 10)) (some (10, 2, 10)) (.next
      ([3388800000000, 4980000000000], [1134600000000, -2490000000000]) (some (10, 2, 10)) (some
      (10, 2, 10)) (.next ([1058400000000, 2490000000000], [398400000000, 2490000000000]) (some (10,
      2, 10)) (some (10, 2, 10)) (.next ([1440000000000], [660000000000]) (some (10, 2, 10)) (some
      (10, 2, 10)) (.next ([3252000000000], [1533000000000]) (some (10, 2, 10)) (some (10, 2, 10))
      (.next ([2990400000000, 2490000000000], [1931400000000, 2490000000000]) (some (10, 2, 10))
      (some (10, 2, 10)) (.next ([261600000000, -2490000000000], [136800000000, 4980000000000])
      (some (10, 2, 10)) (some (10, 2, 10)) (.next ([1041600000000, -2490000000000], [796800000000,
      4980000000000]) (some (10, 2, 10)) (some (10, 3, 10)) (.next ([2592000000000],
      [2193000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([780000000000], [660000000000])
      (some (10, 3, 10)) (some (10, 3, 10)) (.next ([398400000000, 2490000000000], [398400000000,
      2490000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([2193600000000, -2490000000000],
      [2329800000000, 4980000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([1932000000000],
      [2193000000000]) (some (10, 3, 10)) (some (10, 3, 10)) (.next ([660000000000], [780000000000])
      (some (10, 3, 10)) (some (10, 3, 10)) fan15Owner0Part5))))))))))))))))))) (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan15Owner0Part1, checkedFan15Owner0Part3, checkedFan15Owner0Part5,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded15_1 : ExcludedOn (model15.B 1 ++ [step15.q]) 9000000000000 (model15.caps 1)
    (model15.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded15Owner1)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  delta witnessForExcluded15Owner1
  as_aux_lemma => exact checkedWitnessForExcluded15_1

theorem excluded15_3 : ExcludedOn (model15.B 3 ++ [step15.q]) 9000000000000 (model15.caps 3)
    (model15.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded15_3

theorem excluded15_4 : ExcludedOn (model15.B 4 ++ [step15.q]) 9000000000000 (model15.caps 4)
    (model15.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded15_4

theorem excluded15_5 : ExcludedOn (model15.B 5 ++ [step15.q]) 9000000000000 (model15.caps 5)
    (model15.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded15_5

theorem excluded15_6 : ExcludedOn (model15.B 6 ++ [step15.q]) 9000000000000 (model15.caps 6)
    (model15.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded15_6

theorem excluded15_7 : ExcludedOn (model15.B 7 ++ [step15.q]) 9000000000000 (model15.caps 7)
    (model15.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded15Owner7)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100
      (by decide +kernel)
  delta witnessForExcluded15Owner7
  as_aux_lemma => exact checkedWitnessForExcluded15_7

theorem excluded15_8 : ExcludedOn (model15.B 8 ++ [step15.q]) 9000000000000 (model15.caps 8)
    (model15.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded15_8

theorem excluded15_9 : ExcludedOn (model15.B 9 ++ [step15.q]) 9000000000000 (model15.caps 9)
    (model15.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded15_9

theorem checked15 : StepValid model15 9000000000000 step15 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded15_0
    · exact excluded15_1
    · exact (hj rfl).elim
    · exact excluded15_3
    · exact excluded15_4
    · exact excluded15_5
    · exact excluded15_6
    · exact excluded15_7
    · exact excluded15_8
    · exact excluded15_9
theorem next15 : model15.insert step15 = model16 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Aown160000170000
end ConwaySoifer.Simplified.Certificates

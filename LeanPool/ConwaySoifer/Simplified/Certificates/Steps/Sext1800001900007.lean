/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sext1800001900007
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part0
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part1
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part2
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part3
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part4
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part5
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part6
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part7
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sext1800001900007Part8

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sext180000190000

/-!
# Sext 180000 190000 7

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
namespace Sext180000190000

theorem excluded56_0 : ExcludedOn (model56.B 0 ++ [step56.q]) 9000000000000 (model56.caps 0)
    (model56.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_0

theorem excluded56_1 : ExcludedOn (model56.B 1 ++ [step56.q]) 9000000000000 (model56.caps 1)
    (model56.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_1

theorem excluded56_2 : ExcludedOn (model56.B 2 ++ [step56.q]) 9000000000000 (model56.caps 2)
    (model56.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_2

theorem excluded56_3 : ExcludedOn (model56.B 3 ++ [step56.q]) 9000000000000 (model56.caps 3)
    (model56.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded56Owner3)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded56Owner3
  as_aux_lemma => exact checkedWitnessForExcluded56_3

theorem excluded56_4 : ExcludedOn (model56.B 4 ++ [step56.q]) 9000000000000 (model56.caps 4)
    (model56.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_4

theorem excluded56_5 : ExcludedOn (model56.B 5 ++ [step56.q]) 9000000000000 (model56.caps 5)
    (model56.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_5

theorem excluded56_6 : ExcludedOn (model56.B 6 ++ [step56.q]) 9000000000000 (model56.caps 6)
    (model56.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_6

theorem excluded56_7 : ExcludedOn (model56.B 7 ++ [step56.q]) 9000000000000 (model56.caps 7)
    (model56.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_7

theorem excluded56_9 : ExcludedOn (model56.B 9 ++ [step56.q]) 9000000000000 (model56.caps 9)
    (model56.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded56_9

theorem checked56 : StepValid model56 9000000000000 step56 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded56_0
    · exact excluded56_1
    · exact excluded56_2
    · exact excluded56_3
    · exact excluded56_4
    · exact excluded56_5
    · exact excluded56_6
    · exact excluded56_7
    · exact (hj rfl).elim
    · exact excluded56_9
theorem next56 : model56.insert step56 = model57 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded57_0 : ExcludedOn (model57.B 0 ++ [step57.q]) 9000000000000 (model57.caps 0)
    (model57.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded57_0

theorem excluded57_1 : ExcludedOn (model57.B 1 ++ [step57.q]) 9000000000000 (model57.caps 1)
    (model57.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded57_1

theorem excluded57_2 : ExcludedOn (model57.B 2 ++ [step57.q]) 9000000000000 (model57.caps 2)
    (model57.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded57_2

theorem excluded57_4 : ExcludedOn (model57.B 4 ++ [step57.q]) 9000000000000 (model57.caps 4)
    (model57.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded57Owner4)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded57Owner4
  as_aux_lemma => exact checkedWitnessForExcluded57_4

theorem excluded57_5 : ExcludedOn (model57.B 5 ++ [step57.q]) 9000000000000 (model57.caps 5)
    (model57.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded57_5

theorem excluded57_6 : ExcludedOn (model57.B 6 ++ [step57.q]) 9000000000000 (model57.caps 6)
    (model57.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded57_6

theorem excluded57_7 : ExcludedOn (model57.B 7 ++ [step57.q]) 9000000000000 (model57.caps 7)
    (model57.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded57_7

theorem excluded57_8 : ExcludedOn (model57.B 8 ++ [step57.q]) 9000000000000 (model57.caps 8)
    (model57.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded57Owner8)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded57Owner8
  as_aux_lemma => exact checkedWitnessForExcluded57_8

theorem excluded57_9 : ExcludedOn (model57.B 9 ++ [step57.q]) 9000000000000 (model57.caps 9)
    (model57.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded57_9

theorem checked57 : StepValid model57 9000000000000 step57 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded57_0
    · exact excluded57_1
    · exact excluded57_2
    · exact (hj rfl).elim
    · exact excluded57_4
    · exact excluded57_5
    · exact excluded57_6
    · exact excluded57_7
    · exact excluded57_8
    · exact excluded57_9
theorem next57 : model57.insert step57 = model58 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded58_0 : ExcludedOn (model58.B 0 ++ [step58.q]) 9000000000000 (model58.caps 0)
    (model58.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_0

theorem excluded58_1 : ExcludedOn (model58.B 1 ++ [step58.q]) 9000000000000 (model58.caps 1)
    (model58.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_1

theorem excluded58_3 : ExcludedOn (model58.B 3 ++ [step58.q]) 9000000000000 (model58.caps 3)
    (model58.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded58Owner3)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded58Owner3
  as_aux_lemma => exact checkedWitnessForExcluded58_3

theorem excluded58_4 : ExcludedOn (model58.B 4 ++ [step58.q]) 9000000000000 (model58.caps 4)
    (model58.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_4

theorem excluded58_5 : ExcludedOn (model58.B 5 ++ [step58.q]) 9000000000000 (model58.caps 5)
    (model58.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_5

theorem excluded58_6 : ExcludedOn (model58.B 6 ++ [step58.q]) 9000000000000 (model58.caps 6)
    (model58.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_6

theorem excluded58_7 : ExcludedOn (model58.B 7 ++ [step58.q]) 9000000000000 (model58.caps 7)
    (model58.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_7

theorem excluded58_8 : ExcludedOn (model58.B 8 ++ [step58.q]) 9000000000000 (model58.caps 8)
    (model58.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_8

theorem excluded58_9 : ExcludedOn (model58.B 9 ++ [step58.q]) 9000000000000 (model58.caps 9)
    (model58.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded58_9

theorem checked58 : StepValid model58 9000000000000 step58 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded58_0
    · exact excluded58_1
    · exact (hj rfl).elim
    · exact excluded58_3
    · exact excluded58_4
    · exact excluded58_5
    · exact excluded58_6
    · exact excluded58_7
    · exact excluded58_8
    · exact excluded58_9
theorem next58 : model58.insert step58 = model59 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded59_0 : ExcludedOn (model59.B 0 ++ [step59.q]) 9000000000000 (model59.caps 0)
    (model59.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 3 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_0

theorem excluded59_1 : ExcludedOn (model59.B 1 ++ [step59.q]) 9000000000000 (model59.caps 1)
    (model59.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_1

theorem excluded59_2 : ExcludedOn (model59.B 2 ++ [step59.q]) 9000000000000 (model59.caps 2)
    (model59.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_2

theorem excluded59_4 : ExcludedOn (model59.B 4 ++ [step59.q]) 9000000000000 (model59.caps 4)
    (model59.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded59Owner4)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded59Owner4
  as_aux_lemma => exact checkedWitnessForExcluded59_4

theorem excluded59_5 : ExcludedOn (model59.B 5 ++ [step59.q]) 9000000000000 (model59.caps 5)
    (model59.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_5

theorem excluded59_6 : ExcludedOn (model59.B 6 ++ [step59.q]) 9000000000000 (model59.caps 6)
    (model59.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_6

theorem excluded59_7 : ExcludedOn (model59.B 7 ++ [step59.q]) 9000000000000 (model59.caps 7)
    (model59.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_7

theorem excluded59_8 : ExcludedOn (model59.B 8 ++ [step59.q]) 9000000000000 (model59.caps 8)
    (model59.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_8

theorem excluded59_9 : ExcludedOn (model59.B 9 ++ [step59.q]) 9000000000000 (model59.caps 9)
    (model59.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded59_9

theorem checked59 : StepValid model59 9000000000000 step59 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded59_0
    · exact excluded59_1
    · exact excluded59_2
    · exact (hj rfl).elim
    · exact excluded59_4
    · exact excluded59_5
    · exact excluded59_6
    · exact excluded59_7
    · exact excluded59_8
    · exact excluded59_9
theorem next59 : model59.insert step59 = model60 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded60_0 : ExcludedOn (model60.B 0 ++ [step60.q]) 9000000000000 (model60.caps 0)
    (model60.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_0

theorem excluded60_1 : ExcludedOn (model60.B 1 ++ [step60.q]) 9000000000000 (model60.caps 1)
    (model60.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_1

theorem excluded60_2 : ExcludedOn (model60.B 2 ++ [step60.q]) 9000000000000 (model60.caps 2)
    (model60.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded60Owner2)
      (den := 9000000000000) (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded60Owner2
  as_aux_lemma => exact checkedWitnessForExcluded60_2

theorem excluded60_4 : ExcludedOn (model60.B 4 ++ [step60.q]) 9000000000000 (model60.caps 4)
    (model60.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_4

theorem excluded60_5 : ExcludedOn (model60.B 5 ++ [step60.q]) 9000000000000 (model60.caps 5)
    (model60.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_5

theorem excluded60_6 : ExcludedOn (model60.B 6 ++ [step60.q]) 9000000000000 (model60.caps 6)
    (model60.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_6

theorem excluded60_7 : ExcludedOn (model60.B 7 ++ [step60.q]) 9000000000000 (model60.caps 7)
    (model60.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_7

theorem excluded60_8 : ExcludedOn (model60.B 8 ++ [step60.q]) 9000000000000 (model60.caps 8)
    (model60.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_8

theorem excluded60_9 : ExcludedOn (model60.B 9 ++ [step60.q]) 9000000000000 (model60.caps 9)
    (model60.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded60_9

theorem checked60 : StepValid model60 9000000000000 step60 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded60_0
    · exact excluded60_1
    · exact excluded60_2
    · exact (hj rfl).elim
    · exact excluded60_4
    · exact excluded60_5
    · exact excluded60_6
    · exact excluded60_7
    · exact excluded60_8
    · exact excluded60_9
theorem next60 : model60.insert step60 = model61 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded61_0 : ExcludedOn (model61.B 0 ++ [step61.q]) 9000000000000 (model61.caps 0)
    (model61.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 5 12) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_0

theorem excluded61_1 : ExcludedOn (model61.B 1 ++ [step61.q]) 9000000000000 (model61.caps 1)
    (model61.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_1

theorem excluded61_2 : ExcludedOn (model61.B 2 ++ [step61.q]) 9000000000000 (model61.caps 2)
    (model61.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_2

theorem excluded61_3 : ExcludedOn (model61.B 3 ++ [step61.q]) 9000000000000 (model61.caps 3)
    (model61.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded61Owner3)
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded61Owner3
  as_aux_lemma => exact checkedWitnessForExcluded61_3

theorem excluded61_5 : ExcludedOn (model61.B 5 ++ [step61.q]) 9000000000000 (model61.caps 5)
    (model61.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_5

theorem excluded61_6 : ExcludedOn (model61.B 6 ++ [step61.q]) 9000000000000 (model61.caps 6)
    (model61.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_6

theorem excluded61_7 : ExcludedOn (model61.B 7 ++ [step61.q]) 9000000000000 (model61.caps 7)
    (model61.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_7

theorem excluded61_8 : ExcludedOn (model61.B 8 ++ [step61.q]) 9000000000000 (model61.caps 8)
    (model61.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_8

theorem excluded61_9 : ExcludedOn (model61.B 9 ++ [step61.q]) 9000000000000 (model61.caps 9)
    (model61.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded61_9

theorem checked61 : StepValid model61 9000000000000 step61 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded61_0
    · exact excluded61_1
    · exact excluded61_2
    · exact excluded61_3
    · exact (hj rfl).elim
    · exact excluded61_5
    · exact excluded61_6
    · exact excluded61_7
    · exact excluded61_8
    · exact excluded61_9
theorem next61 : model61.insert step61 = model62 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded62_1 : ExcludedOn (model62.B 1 ++ [step62.q]) 9000000000000 (model62.caps 1)
    (model62.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded62_1

theorem excluded62_2 : ExcludedOn (model62.B 2 ++ [step62.q]) 9000000000000 (model62.caps 2)
    (model62.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded62Owner2)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded62Owner2
  as_aux_lemma => exact checkedWitnessForExcluded62_2

theorem excluded62_3 : ExcludedOn (model62.B 3 ++ [step62.q]) 9000000000000 (model62.caps 3)
    (model62.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded62Owner3)
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded62Owner3
  as_aux_lemma => exact checkedWitnessForExcluded62_3

theorem excluded62_4 : ExcludedOn (model62.B 4 ++ [step62.q]) 9000000000000 (model62.caps 4)
    (model62.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded62Owner4)
      (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded62Owner4
  as_aux_lemma => exact checkedWitnessForExcluded62_4

theorem excluded62_5 : ExcludedOn (model62.B 5 ++ [step62.q]) 9000000000000 (model62.caps 5)
    (model62.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded62_5

theorem excluded62_6 : ExcludedOn (model62.B 6 ++ [step62.q]) 9000000000000 (model62.caps 6)
    (model62.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded62_6

theorem excluded62_7 : ExcludedOn (model62.B 7 ++ [step62.q]) 9000000000000 (model62.caps 7)
    (model62.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded62_7

theorem excluded62_8 : ExcludedOn (model62.B 8 ++ [step62.q]) 9000000000000 (model62.caps 8)
    (model62.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded62_8

theorem excluded62_9 : ExcludedOn (model62.B 9 ++ [step62.q]) 9000000000000 (model62.caps 9)
    (model62.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded62_9

theorem checked62 : StepValid model62 9000000000000 step62 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded62_1
    · exact excluded62_2
    · exact excluded62_3
    · exact excluded62_4
    · exact excluded62_5
    · exact excluded62_6
    · exact excluded62_7
    · exact excluded62_8
    · exact excluded62_9
theorem next62 : model62.insert step62 = model63 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded63_0 : ExcludedOn (model63.B 0 ++ [step63.q]) 9000000000000 (model63.caps 0)
    (model63.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded63Owner0)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded63Owner0
  as_aux_lemma => exact checkedWitnessForExcluded63_0

theorem excluded63_1 : ExcludedOn (model63.B 1 ++ [step63.q]) 9000000000000 (model63.caps 1)
    (model63.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded63Owner1)
      (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded63Owner1
  as_aux_lemma => exact checkedWitnessForExcluded63_1

theorem excluded63_3 : ExcludedOn (model63.B 3 ++ [step63.q]) 9000000000000 (model63.caps 3)
    (model63.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (3) (4) (400) (.witnessedFan (.next ([7875000000000],
      [555000000000]) (some (4, 0, 6)) (some (5, 0, 6)) (.next ([4950000000000], [675000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000, 0], [810000000000, -9000000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([4635000000000], [1305000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5130000000000, 9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([2445000000000], [810000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([5445000000000], [2430000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([3000000000000], [1620000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4620000000000],
      [3000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1710000000000], [1425000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3510000000000], [3240000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([1995000000000, 9000000000000], [3330000000000, -9000000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([750000000000], [2490000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan63Owner3Part0)))))))))))))))) (.witnessedFan (.next ([7875000000000], [555000000000]) (some
      (4, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000, 0], [810000000000, -9000000000000]) (some
      (5, 0, 6)) (some (5, 0, 6)) (.next ([4950000000000], [675000000000]) (some (5, 0, 6)) (some
      (5, 0, 6)) (.next ([1995000000000], [330000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([4635000000000], [1305000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5130000000000,
      9000000000000], [1620000000000, -9000000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([2445000000000], [810000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([5445000000000],
      [2430000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next ([3000000000000], [1620000000000])
      (some (5, 0, 6)) (some (5, 0, 6)) (.next ([4620000000000], [3000000000000]) (some (5, 0, 6))
      (some (5, 0, 6)) (.next ([1710000000000], [1425000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      (.next ([3510000000000], [3240000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([1995000000000, 9000000000000], [3330000000000, -9000000000000]) (some (5, 0, 6)) (some (5,
      0, 6)) (.next ([1380000000000], [3750000000000]) (some (5, 0, 6)) (some (5, 0, 6)) (.next
      ([750000000000], [2490000000000]) (some (5, 0, 6)) (some (5, 0, 6))
      fan63Owner3Part1))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded63_3

theorem excluded63_4 : ExcludedOn (model63.B 4 ++ [step63.q]) 9000000000000 (model63.caps 4)
    (model63.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded63_4

theorem excluded63_5 : ExcludedOn (model63.B 5 ++ [step63.q]) 9000000000000 (model63.caps 5)
    (model63.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded63_5

theorem excluded63_6 : ExcludedOn (model63.B 6 ++ [step63.q]) 9000000000000 (model63.caps 6)
    (model63.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded63_6

theorem excluded63_7 : ExcludedOn (model63.B 7 ++ [step63.q]) 9000000000000 (model63.caps 7)
    (model63.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded63_7

theorem excluded63_8 : ExcludedOn (model63.B 8 ++ [step63.q]) 9000000000000 (model63.caps 8)
    (model63.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded63_8

theorem excluded63_9 : ExcludedOn (model63.B 9 ++ [step63.q]) 9000000000000 (model63.caps 9)
    (model63.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded63_9

theorem checked63 : StepValid model63 9000000000000 step63 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded63_0
    · exact excluded63_1
    · exact (hj rfl).elim
    · exact excluded63_3
    · exact excluded63_4
    · exact excluded63_5
    · exact excluded63_6
    · exact excluded63_7
    · exact excluded63_8
    · exact excluded63_9
theorem next63 : model63.insert step63 = model64 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sext180000190000
end ConwaySoifer.Simplified.Certificates

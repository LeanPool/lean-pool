/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Sint2000002100006
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part0
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part1
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part2
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part3
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part4
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part5
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part6
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part7
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Sint2000002100006Part8

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Sint200000210000

/-!
# Sint 200000 210000 6

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
namespace Sint200000210000

theorem excluded48_0 : ExcludedOn (model48.B 0 ++ [step48.q]) 9000000000000 (model48.caps 0)
    (model48.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_0

theorem excluded48_1 : ExcludedOn (model48.B 1 ++ [step48.q]) 9000000000000 (model48.caps 1)
    (model48.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_1

theorem excluded48_2 : ExcludedOn (model48.B 2 ++ [step48.q]) 9000000000000 (model48.caps 2)
    (model48.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_2

theorem excluded48_3 : ExcludedOn (model48.B 3 ++ [step48.q]) 9000000000000 (model48.caps 3)
    (model48.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_3

theorem excluded48_4 : ExcludedOn (model48.B 4 ++ [step48.q]) 9000000000000 (model48.caps 4)
    (model48.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded48Owner4)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded48Owner4
  as_aux_lemma => exact checkedWitnessForExcluded48_4

theorem excluded48_5 : ExcludedOn (model48.B 5 ++ [step48.q]) 9000000000000 (model48.caps 5)
    (model48.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_5

theorem excluded48_6 : ExcludedOn (model48.B 6 ++ [step48.q]) 9000000000000 (model48.caps 6)
    (model48.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_6

theorem excluded48_7 : ExcludedOn (model48.B 7 ++ [step48.q]) 9000000000000 (model48.caps 7)
    (model48.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_7

theorem excluded48_9 : ExcludedOn (model48.B 9 ++ [step48.q]) 9000000000000 (model48.caps 9)
    (model48.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded48_9

theorem checked48 : StepValid model48 9000000000000 step48 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded48_0
    · exact excluded48_1
    · exact excluded48_2
    · exact excluded48_3
    · exact excluded48_4
    · exact excluded48_5
    · exact excluded48_6
    · exact excluded48_7
    · exact (hj rfl).elim
    · exact excluded48_9
theorem next48 : model48.insert step48 = model49 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded49_0 : ExcludedOn (model49.B 0 ++ [step49.q]) 9000000000000 (model49.caps 0)
    (model49.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 6 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded49_0

theorem excluded49_1 : ExcludedOn (model49.B 1 ++ [step49.q]) 9000000000000 (model49.caps 1)
    (model49.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded49_1

theorem excluded49_2 : ExcludedOn (model49.B 2 ++ [step49.q]) 9000000000000 (model49.caps 2)
    (model49.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded49_2

theorem excluded49_3 : ExcludedOn (model49.B 3 ++ [step49.q]) 9000000000000 (model49.caps 3)
    (model49.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded49Owner3)
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded49Owner3
  as_aux_lemma => exact checkedWitnessForExcluded49_3

theorem excluded49_5 : ExcludedOn (model49.B 5 ++ [step49.q]) 9000000000000 (model49.caps 5)
    (model49.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded49_5

theorem excluded49_6 : ExcludedOn (model49.B 6 ++ [step49.q]) 9000000000000 (model49.caps 6)
    (model49.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded49_6

theorem excluded49_7 : ExcludedOn (model49.B 7 ++ [step49.q]) 9000000000000 (model49.caps 7)
    (model49.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded49_7

theorem excluded49_8 : ExcludedOn (model49.B 8 ++ [step49.q]) 9000000000000 (model49.caps 8)
    (model49.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded49Owner8)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded49Owner8
  as_aux_lemma => exact checkedWitnessForExcluded49_8

theorem excluded49_9 : ExcludedOn (model49.B 9 ++ [step49.q]) 9000000000000 (model49.caps 9)
    (model49.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded49_9

theorem checked49 : StepValid model49 9000000000000 step49 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded49_0
    · exact excluded49_1
    · exact excluded49_2
    · exact excluded49_3
    · exact (hj rfl).elim
    · exact excluded49_5
    · exact excluded49_6
    · exact excluded49_7
    · exact excluded49_8
    · exact excluded49_9
theorem next49 : model49.insert step49 = model50 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded50_0 : ExcludedOn (model50.B 0 ++ [step50.q]) 9000000000000 (model50.caps 0)
    (model50.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 9) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_0

theorem excluded50_1 : ExcludedOn (model50.B 1 ++ [step50.q]) 9000000000000 (model50.caps 1)
    (model50.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_1

theorem excluded50_2 : ExcludedOn (model50.B 2 ++ [step50.q]) 9000000000000 (model50.caps 2)
    (model50.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_2

theorem excluded50_3 : ExcludedOn (model50.B 3 ++ [step50.q]) 9000000000000 (model50.caps 3)
    (model50.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_3

theorem excluded50_4 : ExcludedOn (model50.B 4 ++ [step50.q]) 9000000000000 (model50.caps 4)
    (model50.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded50Owner4)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded50Owner4
  as_aux_lemma => exact checkedWitnessForExcluded50_4

theorem excluded50_6 : ExcludedOn (model50.B 6 ++ [step50.q]) 9000000000000 (model50.caps 6)
    (model50.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_6

theorem excluded50_7 : ExcludedOn (model50.B 7 ++ [step50.q]) 9000000000000 (model50.caps 7)
    (model50.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_7

theorem excluded50_8 : ExcludedOn (model50.B 8 ++ [step50.q]) 9000000000000 (model50.caps 8)
    (model50.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_8

theorem excluded50_9 : ExcludedOn (model50.B 9 ++ [step50.q]) 9000000000000 (model50.caps 9)
    (model50.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded50_9

theorem checked50 : StepValid model50 9000000000000 step50 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded50_0
    · exact excluded50_1
    · exact excluded50_2
    · exact excluded50_3
    · exact excluded50_4
    · exact (hj rfl).elim
    · exact excluded50_6
    · exact excluded50_7
    · exact excluded50_8
    · exact excluded50_9
theorem next50 : model50.insert step50 = model51 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded51_0 : ExcludedOn (model51.B 0 ++ [step51.q]) 9000000000000 (model51.caps 0)
    (model51.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded51Owner0)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded51Owner0
  as_aux_lemma => exact checkedWitnessForExcluded51_0

theorem excluded51_1 : ExcludedOn (model51.B 1 ++ [step51.q]) 9000000000000 (model51.caps 1)
    (model51.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded51_1

theorem excluded51_2 : ExcludedOn (model51.B 2 ++ [step51.q]) 9000000000000 (model51.caps 2)
    (model51.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded51_2

theorem excluded51_4 : ExcludedOn (model51.B 4 ++ [step51.q]) 9000000000000 (model51.caps 4)
    (model51.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded51Owner4)
      (den := 9000000000000) (fuel :=
      12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded51Owner4
  as_aux_lemma => exact checkedWitnessForExcluded51_4

theorem excluded51_5 : ExcludedOn (model51.B 5 ++ [step51.q]) 9000000000000 (model51.caps 5)
    (model51.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded51_5

theorem excluded51_6 : ExcludedOn (model51.B 6 ++ [step51.q]) 9000000000000 (model51.caps 6)
    (model51.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded51_6

theorem excluded51_7 : ExcludedOn (model51.B 7 ++ [step51.q]) 9000000000000 (model51.caps 7)
    (model51.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded51_7

theorem excluded51_8 : ExcludedOn (model51.B 8 ++ [step51.q]) 9000000000000 (model51.caps 8)
    (model51.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded51_8

theorem excluded51_9 : ExcludedOn (model51.B 9 ++ [step51.q]) 9000000000000 (model51.caps 9)
    (model51.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded51_9

theorem checked51 : StepValid model51 9000000000000 step51 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded51_0
    · exact excluded51_1
    · exact excluded51_2
    · exact (hj rfl).elim
    · exact excluded51_4
    · exact excluded51_5
    · exact excluded51_6
    · exact excluded51_7
    · exact excluded51_8
    · exact excluded51_9
theorem next51 : model51.insert step51 = model52 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded52_0 : ExcludedOn (model52.B 0 ++ [step52.q]) 9000000000000 (model52.caps 0)
    (model52.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded52Owner0)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded52Owner0
  as_aux_lemma => exact checkedWitnessForExcluded52_0

theorem excluded52_1 : ExcludedOn (model52.B 1 ++ [step52.q]) 9000000000000 (model52.caps 1)
    (model52.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded52_1

theorem excluded52_3 : ExcludedOn (model52.B 3 ++ [step52.q]) 9000000000000 (model52.caps 3)
    (model52.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded52Owner3)
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded52Owner3
  as_aux_lemma => exact checkedWitnessForExcluded52_3

theorem excluded52_4 : ExcludedOn (model52.B 4 ++ [step52.q]) 9000000000000 (model52.caps 4)
    (model52.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded52_4

theorem excluded52_5 : ExcludedOn (model52.B 5 ++ [step52.q]) 9000000000000 (model52.caps 5)
    (model52.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded52_5

theorem excluded52_6 : ExcludedOn (model52.B 6 ++ [step52.q]) 9000000000000 (model52.caps 6)
    (model52.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded52_6

theorem excluded52_7 : ExcludedOn (model52.B 7 ++ [step52.q]) 9000000000000 (model52.caps 7)
    (model52.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded52_7

theorem excluded52_8 : ExcludedOn (model52.B 8 ++ [step52.q]) 9000000000000 (model52.caps 8)
    (model52.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded52_8

theorem excluded52_9 : ExcludedOn (model52.B 9 ++ [step52.q]) 9000000000000 (model52.caps 9)
    (model52.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded52_9

theorem checked52 : StepValid model52 9000000000000 step52 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded52_0
    · exact excluded52_1
    · exact (hj rfl).elim
    · exact excluded52_3
    · exact excluded52_4
    · exact excluded52_5
    · exact excluded52_6
    · exact excluded52_7
    · exact excluded52_8
    · exact excluded52_9
theorem next52 : model52.insert step52 = model53 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded53_0 : ExcludedOn (model53.B 0 ++ [step53.q]) 9000000000000 (model53.caps 0)
    (model53.ord 0) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded53Owner0)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded53Owner0
  as_aux_lemma => exact checkedWitnessForExcluded53_0

theorem excluded53_1 : ExcludedOn (model53.B 1 ++ [step53.q]) 9000000000000 (model53.caps 1)
    (model53.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded53Owner1)
      (den := 9000000000000)
      (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded53Owner1
  as_aux_lemma => exact checkedWitnessForExcluded53_1

theorem excluded53_2 : ExcludedOn (model53.B 2 ++ [step53.q]) 9000000000000 (model53.caps 2)
    (model53.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 4) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded53_2

theorem excluded53_3 : ExcludedOn (model53.B 3 ++ [step53.q]) 9000000000000 (model53.caps 3)
    (model53.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded53_3

theorem excluded53_4 : ExcludedOn (model53.B 4 ++ [step53.q]) 9000000000000 (model53.caps 4)
    (model53.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded53_4

theorem excluded53_5 : ExcludedOn (model53.B 5 ++ [step53.q]) 9000000000000 (model53.caps 5)
    (model53.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded53Owner5)
      (den := 9000000000000)
      (fuel
      := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded53Owner5
  as_aux_lemma => exact checkedWitnessForExcluded53_5

theorem excluded53_7 : ExcludedOn (model53.B 7 ++ [step53.q]) 9000000000000 (model53.caps 7)
    (model53.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded53_7

theorem excluded53_8 : ExcludedOn (model53.B 8 ++ [step53.q]) 9000000000000 (model53.caps 8)
    (model53.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded53_8

theorem excluded53_9 : ExcludedOn (model53.B 9 ++ [step53.q]) 9000000000000 (model53.caps 9)
    (model53.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded53_9

theorem checked53 : StepValid model53 9000000000000 step53 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact excluded53_0
    · exact excluded53_1
    · exact excluded53_2
    · exact excluded53_3
    · exact excluded53_4
    · exact excluded53_5
    · exact (hj rfl).elim
    · exact excluded53_7
    · exact excluded53_8
    · exact excluded53_9
theorem next53 : model53.insert step53 = model54 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded54_1 : ExcludedOn (model54.B 1 ++ [step54.q]) 9000000000000 (model54.caps 1)
    (model54.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded54Owner1)
      (den := 9000000000000) (fuel := 12) (by decide +kernel)
      0 1 100 (by decide +kernel)
  delta witnessForExcluded54Owner1
  as_aux_lemma => exact checkedWitnessForExcluded54_1

theorem excluded54_2 : ExcludedOn (model54.B 2 ++ [step54.q]) 9000000000000 (model54.caps 2)
    (model54.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.split (0) (25) (56) (5600) (.witnessedFan (.next ([450000000000,
      -9000000000000], [0, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next
      ([3825000000000], [375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([1800000000000],
      [450000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([7200000000000, -9000000000000],
      [1800000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6750000000000,
      -9000000000000], [2250000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2925000000000,
      -9000000000000], [1875000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1875000000000], [2400000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([75000000000,
      -9000000000000], [4200000000000, 9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([0,
      0], [1800000000000, 9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([0,
      -9000000000000], [450000000000]) (some (0, 2, 2)) (some (0, 2, 3)) (.next ([-375000000000],
      [4200000000000]) (some (0, 2, 3)) (some (1, 2, 3)) (.next ([-450000000000], [2250000000000])
      (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-1800000000000, -9000000000000], [9000000000000,
      0]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-2250000000000, 0], [9000000000000,
      -9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-1875000000000, 0],
      [4800000000000, -9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-2400000000000],
      [4275000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-4200000000000, -9000000000000],
      [4275000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.terminal (some (1, 2, 3)) (some (1, 2,
      0)) (some (1, 2, 3))))))))))))))))))))) (.split (75) (140) (168) (16800) (.witnessedFan (.next
      ([3825000000000], [375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([450000000000,
      -9000000000000], [0, 9000000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next
      ([1800000000000], [450000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([7200000000000,
      -9000000000000], [1800000000000, 9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([6750000000000, -9000000000000], [2250000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([2925000000000, -9000000000000], [1875000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next
      ([1875000000000], [2400000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([75000000000,
      -9000000000000], [4200000000000, 9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([0,
      0], [1800000000000, 9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([-375000000000],
      [4200000000000]) (some (0, 2, 2)) (some (0, 2, 3)) (.next ([0, -9000000000000],
      [450000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-450000000000], [2250000000000])
      (some (0, 2, 3)) (some (1, 2, 3)) (.next ([-1800000000000, -9000000000000], [9000000000000,
      0]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-2250000000000, 0], [9000000000000,
      -9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-1875000000000, 0],
      [4800000000000, -9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-2400000000000],
      [4275000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-4200000000000, -9000000000000],
      [4275000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.terminal (some (1, 2, 3)) (some (1, 2,
      0)) (some (1, 2, 3))))))))))))))))))))) (.witnessedFan (.next ([4275000000000, 0],
      [-75000000000, 9000000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([3825000000000],
      [375000000000]) (some (0, 1, 2)) (some (0, 1, 2)) (.next ([450000000000, -9000000000000], [0,
      9000000000000]) (some (0, 1, 2)) (some (0, 4, 2)) (.next ([1800000000000], [450000000000])
      (some (0, 4, 2)) (some (0, 4, 2)) (.next ([7200000000000, -9000000000000], [1800000000000,
      9000000000000]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([6750000000000, -9000000000000],
      [2250000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([2925000000000, -9000000000000],
      [1875000000000, 0]) (some (0, 4, 2)) (some (0, 4, 2)) (.next ([1875000000000],
      [2400000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([0, 0], [1800000000000,
      9000000000000]) (some (0, 2, 2)) (some (0, 2, 2)) (.next ([75000000000, -9000000000000],
      [4200000000000, 9000000000000]) (some (0, 2, 2)) (some (0, 2, 3)) (.next ([-375000000000],
      [4200000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([0, -9000000000000],
      [450000000000]) (some (0, 2, 3)) (some (0, 2, 3)) (.next ([-450000000000], [2250000000000])
      (some (0, 2, 3)) (some (1, 2, 3)) (.next ([-1800000000000, -9000000000000], [9000000000000,
      0]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-2250000000000, 0], [9000000000000,
      -9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-1875000000000, 0],
      [4800000000000, -9000000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.next ([-2400000000000],
      [4275000000000]) (some (1, 2, 3)) (some (1, 2, 3)) (.terminal (some (1, 2, 3)) (some (1, 2,
      0)) (some (1, 2, 3))))))))))))))))))))))) (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1 100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_2

theorem excluded54_3 : ExcludedOn (model54.B 3 ++ [step54.q]) 9000000000000 (model54.caps 3)
    (model54.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_3

theorem excluded54_4 : ExcludedOn (model54.B 4 ++ [step54.q]) 9000000000000 (model54.caps 4)
    (model54.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_4

theorem excluded54_5 : ExcludedOn (model54.B 5 ++ [step54.q]) 9000000000000 (model54.caps 5)
    (model54.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_5

theorem excluded54_6 : ExcludedOn (model54.B 6 ++ [step54.q]) 9000000000000 (model54.caps 6)
    (model54.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.pair 1 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_6

theorem excluded54_7 : ExcludedOn (model54.B 7 ++ [step54.q]) 9000000000000 (model54.caps 7)
    (model54.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 2 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_7

theorem excluded54_8 : ExcludedOn (model54.B 8 ++ [step54.q]) 9000000000000 (model54.caps 8)
    (model54.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_8

theorem excluded54_9 : ExcludedOn (model54.B 9 ++ [step54.q]) 9000000000000 (model54.caps 9)
    (model54.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded54_9

theorem checked54 : StepValid model54 9000000000000 step54 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded54_1
    · exact excluded54_2
    · exact excluded54_3
    · exact excluded54_4
    · exact excluded54_5
    · exact excluded54_6
    · exact excluded54_7
    · exact excluded54_8
    · exact excluded54_9
theorem next54 : model54.insert step54 = model55 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

theorem excluded55_1 : ExcludedOn (model55.B 1 ++ [step55.q]) 9000000000000 (model55.caps 1)
    (model55.ord 1) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded55Owner1)
      (den := 9000000000000) (fuel := 12)
      (by decide +kernel) 0 1
      100 (by decide +kernel)
  delta witnessForExcluded55Owner1
  as_aux_lemma => exact checkedWitnessForExcluded55_1

theorem excluded55_2 : ExcludedOn (model55.B 2 ++ [step55.q]) 9000000000000 (model55.caps 2)
    (model55.ord 2) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded55Owner2)
      (den :=
      9000000000000) (fuel := 12) (by decide +kernel) 0 1 100 (by decide +kernel)
  delta witnessForExcluded55Owner2
  as_aux_lemma => exact checkedWitnessForExcluded55_2

theorem excluded55_3 : ExcludedOn (model55.B 3 ++ [step55.q]) 9000000000000 (model55.caps 3)
    (model55.ord 3) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded55_3

theorem excluded55_4 : ExcludedOn (model55.B 4 ++ [step55.q]) 9000000000000 (model55.caps 4)
    (model55.ord 4) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded55_4

theorem excluded55_5 : ExcludedOn (model55.B 5 ++ [step55.q]) 9000000000000 (model55.caps 5)
    (model55.ord 5) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 5) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded55_5

theorem excluded55_6 : ExcludedOn (model55.B 6 ++ [step55.q]) 9000000000000 (model55.caps 6)
    (model55.ord 6) 0 1 100 := by
  apply ExclusionHint.sound (.witnessedFan witnessForExcluded55Owner6)
      (den := 9000000000000) (fuel := 12) (by decide +kernel) 0
      1 100
      (by decide +kernel)
  delta witnessForExcluded55Owner6
  as_aux_lemma => exact checkedWitnessForExcluded55_6

theorem excluded55_7 : ExcludedOn (model55.B 7 ++ [step55.q]) 9000000000000 (model55.caps 7)
    (model55.ord 7) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded55_7

theorem excluded55_8 : ExcludedOn (model55.B 8 ++ [step55.q]) 9000000000000 (model55.caps 8)
    (model55.ord 8) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded55_8

theorem excluded55_9 : ExcludedOn (model55.B 9 ++ [step55.q]) 9000000000000 (model55.caps 9)
    (model55.ord 9) 0 1 100 := by
  apply ExclusionHint.sound (.pair 0 3) (den := 9000000000000) (fuel := 12) (by decide +kernel) 0 1
      100 (by decide +kernel)
  as_aux_lemma => exact checkedWitnessForExcluded55_9

theorem checked55 : StepValid model55 9000000000000 step55 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact excluded55_1
    · exact excluded55_2
    · exact excluded55_3
    · exact excluded55_4
    · exact excluded55_5
    · exact excluded55_6
    · exact excluded55_7
    · exact excluded55_8
    · exact excluded55_9
theorem next55 : model55.insert step55 = model56 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> decide +kernel

end Sint200000210000
end ConwaySoifer.Simplified.Certificates

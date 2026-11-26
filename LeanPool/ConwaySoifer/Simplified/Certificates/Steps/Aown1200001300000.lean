/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Arithmetic
import LeanPool.ConwaySoifer.Certificates.CheckpointOwnerProofs
public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1200001300000
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part0
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part1
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part2
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part3
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part4
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part5
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part6
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part7
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1200001300000Part8

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown120000130000

/-!
# Aown 120000 130000 0

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

theorem excluded0_1 : ExcludedOn (model0.B 1 ++ [step0.q]) 9000000000000 (model0.caps 1) (model0.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_1

theorem excluded0_2 : ExcludedOn (model0.B 2 ++ [step0.q]) 9000000000000 (model0.caps 2) (model0.ord
    2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded0Owner2)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_2

theorem excluded0_3 : ExcludedOn (model0.B 3 ++ [step0.q]) 9000000000000 (model0.caps 3) (model0.ord
    3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded0Owner3)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_3

theorem excluded0_4 : ExcludedOn (model0.B 4 ++ [step0.q]) 9000000000000 (model0.caps 4) (model0.ord
    4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_4

theorem excluded0_5 : ExcludedOn (model0.B 5 ++ [step0.q]) 9000000000000 (model0.caps 5) (model0.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_5

theorem excluded0_6 : ExcludedOn (model0.B 6 ++ [step0.q]) 9000000000000 (model0.caps 6) (model0.ord
    6) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_6

theorem excluded0_7 : ExcludedOn (model0.B 7 ++ [step0.q]) 9000000000000 (model0.caps 7) (model0.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_7

theorem excluded0_8 : ExcludedOn (model0.B 8 ++ [step0.q]) 9000000000000 (model0.caps 8) (model0.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_8

theorem excluded0_9 : ExcludedOn (model0.B 9 ++ [step0.q]) 9000000000000 (model0.caps 9) (model0.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded0_9

theorem checked0 : StepValid model0 9000000000000 step0 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact (hj rfl).elim
    · exact excluded0_1
    · exact excluded0_2
    · exact excluded0_3
    · exact excluded0_4
    · exact excluded0_5
    · exact excluded0_6
    · exact excluded0_7
    · exact excluded0_8
    · exact excluded0_9
theorem next0 : model0.insert step0 = model1 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

theorem excluded1_1 : ExcludedOn (model1.B 1 ++ [step1.q]) 9000000000000 (model1.caps 1) (model1.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded1_1

theorem excluded1_2 : ExcludedOn (model1.B 2 ++ [step1.q]) 9000000000000 (model1.caps 2) (model1.ord
    2) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded1_2

theorem excluded1_3 : ExcludedOn (model1.B 3 ++ [step1.q]) 9000000000000 (model1.caps 3) (model1.ord
    3) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded1_3

theorem excluded1_4 : ExcludedOn (model1.B 4 ++ [step1.q]) 9000000000000 (model1.caps 4) (model1.ord
    4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded1_4

theorem excluded1_5 : ExcludedOn (model1.B 5 ++ [step1.q]) 9000000000000 (model1.caps 5) (model1.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded1Owner5)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded1Owner5
  as_aux_lemma => exact checkedWitnessForExcluded1_5

theorem excluded1_6 : ExcludedOn (model1.B 6 ++ [step1.q]) 9000000000000 (model1.caps 6) (model1.ord
    6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded1Owner6)
      (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded1Owner6
  as_aux_lemma => exact checkedWitnessForExcluded1_6

theorem excluded1_7 : ExcludedOn (model1.B 7 ++ [step1.q]) 9000000000000 (model1.caps 7) (model1.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded1_7

theorem excluded1_8 : ExcludedOn (model1.B 8 ++ [step1.q]) 9000000000000 (model1.caps 8) (model1.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded1_8

theorem excluded1_9 : ExcludedOn (model1.B 9 ++ [step1.q]) 9000000000000 (model1.caps 9) (model1.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded1_9

theorem checked1 : StepValid model1 9000000000000 step1 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact (hj rfl).elim
    · exact excluded1_1
    · exact excluded1_2
    · exact excluded1_3
    · exact excluded1_4
    · exact excluded1_5
    · exact excluded1_6
    · exact excluded1_7
    · exact excluded1_8
    · exact excluded1_9
theorem next1 : model1.insert step1 = model2 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

theorem excluded2_1 : ExcludedOn (model2.B 1 ++ [step2.q]) 9000000000000 (model2.caps 1) (model2.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded2_1

theorem excluded2_2 : ExcludedOn (model2.B 2 ++ [step2.q]) 9000000000000 (model2.caps 2) (model2.ord
    2) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded2Owner2)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded2Owner2
  as_aux_lemma => exact checkedWitnessForExcluded2_2

theorem excluded2_3 : ExcludedOn (model2.B 3 ++ [step2.q]) 9000000000000 (model2.caps 3) (model2.ord
    3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded2_3

theorem excluded2_4 : ExcludedOn (model2.B 4 ++ [step2.q]) 9000000000000 (model2.caps 4) (model2.ord
    4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded2_4

theorem excluded2_5 : ExcludedOn (model2.B 5 ++ [step2.q]) 9000000000000 (model2.caps 5) (model2.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded2_5

theorem excluded2_6 : ExcludedOn (model2.B 6 ++ [step2.q]) 9000000000000 (model2.caps 6) (model2.ord
    6) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded2Owner6)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded2Owner6
  as_aux_lemma => exact checkedWitnessForExcluded2_6

theorem excluded2_7 : ExcludedOn (model2.B 7 ++ [step2.q]) 9000000000000 (model2.caps 7) (model2.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded2_7

theorem excluded2_8 : ExcludedOn (model2.B 8 ++ [step2.q]) 9000000000000 (model2.caps 8) (model2.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded2_8

theorem excluded2_9 : ExcludedOn (model2.B 9 ++ [step2.q]) 9000000000000 (model2.caps 9) (model2.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded2_9

theorem checked2 : StepValid model2 9000000000000 step2 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact (hj rfl).elim
    · exact excluded2_1
    · exact excluded2_2
    · exact excluded2_3
    · exact excluded2_4
    · exact excluded2_5
    · exact excluded2_6
    · exact excluded2_7
    · exact excluded2_8
    · exact excluded2_9
theorem next2 : model2.insert step2 = model3 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan3Owner0Part0 :
    fan3Owner0Part0.check (model3.B 0 ++ [step3.q]) 9000000000000
      (model3.caps 0) 0 1 100 12
      ([313200000000, 2610000000000], [313200000000, 2610000000000]) = true := by
  as_aux_lemma => exact checkedFan3Owner0Part0Arithmetic

theorem excluded3_0 : ExcludedOn (model3.B 0 ++ [step3.q]) 9000000000000 (model3.caps 0) (model3.ord
    0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded3Owner0)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide)
      0 1
      100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded3Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan3Owner0Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded3_1 : ExcludedOn (model3.B 1 ++ [step3.q]) 9000000000000 (model3.caps 1) (model3.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded3Owner1)
      (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded3Owner1
  as_aux_lemma => exact checkedWitnessForExcluded3_1

theorem excluded3_3 : ExcludedOn (model3.B 3 ++ [step3.q]) 9000000000000 (model3.caps 3) (model3.ord
    3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded3_3

theorem excluded3_4 : ExcludedOn (model3.B 4 ++ [step3.q]) 9000000000000 (model3.caps 4) (model3.ord
    4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded3_4

theorem excluded3_5 : ExcludedOn (model3.B 5 ++ [step3.q]) 9000000000000 (model3.caps 5) (model3.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded3_5

theorem excluded3_6 : ExcludedOn (model3.B 6 ++ [step3.q]) 9000000000000 (model3.caps 6) (model3.ord
    6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded3_6

theorem excluded3_7 : ExcludedOn (model3.B 7 ++ [step3.q]) 9000000000000 (model3.caps 7) (model3.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded3Owner7)
      (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded3Owner7
  as_aux_lemma => exact checkedWitnessForExcluded3_7

theorem excluded3_8 : ExcludedOn (model3.B 8 ++ [step3.q]) 9000000000000 (model3.caps 8) (model3.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded3_8

theorem excluded3_9 : ExcludedOn (model3.B 9 ++ [step3.q]) 9000000000000 (model3.caps 9) (model3.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded3_9

theorem checked3 : StepValid model3 9000000000000 step3 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded3_0
    · exact excluded3_1
    · exact (hj rfl).elim
    · exact excluded3_3
    · exact excluded3_4
    · exact excluded3_5
    · exact excluded3_6
    · exact excluded3_7
    · exact excluded3_8
    · exact excluded3_9
theorem next3 : model3.insert step3 = model4 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan4Owner0Part0 :
    fan4Owner0Part0.check (model4.B 0 ++ [step4.q]) 9000000000000
      (model4.caps 0) 0 1 100 12
      ([7186800000000, -2610000000000], [1706400000000, 5220000000000]) = true := by
  as_aux_lemma => exact checkedFan4Owner0Part0Arithmetic

theorem excluded4_0 : ExcludedOn (model4.B 0 ++ [step4.q]) 9000000000000 (model4.caps 0) (model4.ord
    0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded4Owner0)
      (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0
      1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded4Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan4Owner0Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded4_1 : ExcludedOn (model4.B 1 ++ [step4.q]) 9000000000000 (model4.caps 1) (model4.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded4Owner1)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded4Owner1
  as_aux_lemma => exact checkedWitnessForExcluded4_1

theorem excluded4_3 : ExcludedOn (model4.B 3 ++ [step4.q]) 9000000000000 (model4.caps 3) (model4.ord
    3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded4_3

theorem excluded4_4 : ExcludedOn (model4.B 4 ++ [step4.q]) 9000000000000 (model4.caps 4) (model4.ord
    4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded4_4

theorem excluded4_5 : ExcludedOn (model4.B 5 ++ [step4.q]) 9000000000000 (model4.caps 5) (model4.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded4_5

theorem excluded4_6 : ExcludedOn (model4.B 6 ++ [step4.q]) 9000000000000 (model4.caps 6) (model4.ord
    6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded4_6

theorem excluded4_7 : ExcludedOn (model4.B 7 ++ [step4.q]) 9000000000000 (model4.caps 7) (model4.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded4Owner7)
      (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded4Owner7
  as_aux_lemma => exact checkedWitnessForExcluded4_7

theorem excluded4_8 : ExcludedOn (model4.B 8 ++ [step4.q]) 9000000000000 (model4.caps 8) (model4.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded4_8

theorem excluded4_9 : ExcludedOn (model4.B 9 ++ [step4.q]) 9000000000000 (model4.caps 9) (model4.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded4_9

theorem checked4 : StepValid model4 9000000000000 step4 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded4_0
    · exact excluded4_1
    · exact (hj rfl).elim
    · exact excluded4_3
    · exact excluded4_4
    · exact excluded4_5
    · exact excluded4_6
    · exact excluded4_7
    · exact excluded4_8
    · exact excluded4_9
theorem next4 : model4.insert step4 = model5 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan5Owner0Part0 :
    fan5Owner0Part0.check (model5.B 0 ++ [step5.q]) 9000000000000
      (model5.caps 0) 0 1 100 12
      ([7093200000000, 2610000000000], [2533200000000, 2610000000000]) = true := by
  as_aux_lemma => exact checkedFan5Owner0Part0Arithmetic

theorem excluded5_0 : ExcludedOn (model5.B 0 ++ [step5.q]) 9000000000000 (model5.caps 0) (model5.ord
    0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded5Owner0)
      (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded5Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan5Owner0Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded5_1 : ExcludedOn (model5.B 1 ++ [step5.q]) 9000000000000 (model5.caps 1) (model5.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_1

theorem excluded5_2 : ExcludedOn (model5.B 2 ++ [step5.q]) 9000000000000 (model5.caps 2) (model5.ord
    2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_2

theorem excluded5_3 : ExcludedOn (model5.B 3 ++ [step5.q]) 9000000000000 (model5.caps 3) (model5.ord
    3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_3

theorem excluded5_4 : ExcludedOn (model5.B 4 ++ [step5.q]) 9000000000000 (model5.caps 4) (model5.ord
    4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_4

theorem excluded5_5 : ExcludedOn (model5.B 5 ++ [step5.q]) 9000000000000 (model5.caps 5) (model5.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_5

theorem excluded5_7 : ExcludedOn (model5.B 7 ++ [step5.q]) 9000000000000 (model5.caps 7) (model5.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_7

theorem excluded5_8 : ExcludedOn (model5.B 8 ++ [step5.q]) 9000000000000 (model5.caps 8) (model5.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_8

theorem excluded5_9 : ExcludedOn (model5.B 9 ++ [step5.q]) 9000000000000 (model5.caps 9) (model5.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded5_9

theorem checked5 : StepValid model5 9000000000000 step5 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded5_0
    · exact excluded5_1
    · exact excluded5_2
    · exact excluded5_3
    · exact excluded5_4
    · exact excluded5_5
    · exact (hj rfl).elim
    · exact excluded5_7
    · exact excluded5_8
    · exact excluded5_9
theorem next5 : model5.insert step5 = model6 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

theorem excluded6_0 : ExcludedOn (model6.B 0 ++ [step6.q]) 9000000000000 (model6.caps 0) (model6.ord
    0) 0 1 100 := by
  refine exclude_checkpoint (.pair 4 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_0

theorem excluded6_1 : ExcludedOn (model6.B 1 ++ [step6.q]) 9000000000000 (model6.caps 1) (model6.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_1

theorem excluded6_2 : ExcludedOn (model6.B 2 ++ [step6.q]) 9000000000000 (model6.caps 2) (model6.ord
    2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_2

theorem excluded6_3 : ExcludedOn (model6.B 3 ++ [step6.q]) 9000000000000 (model6.caps 3) (model6.ord
    3) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_3

theorem excluded6_5 : ExcludedOn (model6.B 5 ++ [step6.q]) 9000000000000 (model6.caps 5) (model6.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_5

theorem excluded6_6 : ExcludedOn (model6.B 6 ++ [step6.q]) 9000000000000 (model6.caps 6) (model6.ord
    6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_6

theorem excluded6_7 : ExcludedOn (model6.B 7 ++ [step6.q]) 9000000000000 (model6.caps 7) (model6.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_7

theorem excluded6_8 : ExcludedOn (model6.B 8 ++ [step6.q]) 9000000000000 (model6.caps 8) (model6.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_8

theorem excluded6_9 : ExcludedOn (model6.B 9 ++ [step6.q]) 9000000000000 (model6.caps 9) (model6.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded6_9

theorem checked6 : StepValid model6 9000000000000 step6 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded6_0
    · exact excluded6_1
    · exact excluded6_2
    · exact excluded6_3
    · exact (hj rfl).elim
    · exact excluded6_5
    · exact excluded6_6
    · exact excluded6_7
    · exact excluded6_8
    · exact excluded6_9
theorem next6 : model6.insert step6 = model7 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan7Owner0Part3Checks :
    (fan7Owner0Part0.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 0 3836 15494700 12
      ([116400000000, 5220000000000], [196800000000, -2610000000000]) = true) ∧
    (fan7Owner0Part1.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 3836 60106 15494700 12
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true) ∧
    (fan7Owner0Part2.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 60106 116376 15494700 12
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true) ∧
    (fan7Owner0Part3.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 2984 3973 397300 12
      ([6705000000000], [2805000000000]) = true) := by
  have checkedTail0 :
      fan7Owner0Part0.check (model7.B 0 ++ [step7.q]) 9000000000000
        (model7.caps 0) 0 3836 15494700 12
        ([116400000000, 5220000000000], [196800000000, -2610000000000]) = true := by
    as_aux_lemma => exact checkedFan7Owner0Part0Arithmetic
  have checkedTail1 :
      fan7Owner0Part1.check (model7.B 0 ++ [step7.q]) 9000000000000
        (model7.caps 0) 3836 60106 15494700 12
        ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true := by
    as_aux_lemma => exact checkedFan7Owner0Part1Arithmetic
  have checkedTail2 :
      fan7Owner0Part2.check (model7.B 0 ++ [step7.q]) 9000000000000
        (model7.caps 0) 60106 116376 15494700 12
        ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true := by
    as_aux_lemma => exact checkedFan7Owner0Part2Arithmetic
  have checkedTail3 :
      fan7Owner0Part3.check (model7.B 0 ++ [step7.q]) 9000000000000
        (model7.caps 0) 2984 3973 397300 12
        ([6705000000000], [2805000000000]) = true := by
    as_aux_lemma => exact checkedFan7Owner0Part3Arithmetic
  exact ⟨checkedTail0, checkedTail1, checkedTail2, checkedTail3⟩

private theorem checkedFan7Owner0Part0 :
    fan7Owner0Part0.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 0 3836 15494700 12
      ([116400000000, 5220000000000], [196800000000, -2610000000000]) = true := by
  exact checkedFan7Owner0Part3Checks.1

private theorem checkedFan7Owner0Part1 :
    fan7Owner0Part1.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 3836 60106 15494700 12
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true := by
  exact checkedFan7Owner0Part3Checks.2.1

private theorem checkedFan7Owner0Part2 :
    fan7Owner0Part2.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 60106 116376 15494700 12
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) = true := by
  exact checkedFan7Owner0Part3Checks.2.2.1

private theorem checkedFan7Owner0Part3 :
    fan7Owner0Part3.check (model7.B 0 ++ [step7.q]) 9000000000000
      (model7.caps 0) 2984 3973 397300 12
      ([6705000000000], [2805000000000]) = true := by
  exact checkedFan7Owner0Part3Checks.2.2.2

theorem excluded7_0 : ExcludedOn (model7.B 0 ++ [step7.q]) 9000000000000 (model7.caps 0) (model7.ord
    0) 0 1 100 := by
  refine exclude_checkpoint (.split (0) (2984) (3973) (397300) (.split (0) (3836) (116376)
      (15494700) (.witnessedFan (.next ([1393200000000, 2610000000000], [313200000000,
      2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([7018200000000, 2610000000000],
      [1668600000000, -5220000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([7331400000000,
      5220000000000], [1981800000000, -2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([6391800000000, -2610000000000], [1981800000000, -2610000000000]) (some (7, 1, 4)) (some (7,
      1, 4)) (.next ([626400000000, 5220000000000], [196800000000, -2610000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([6195000000000], [2295000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([7018200000000, 2610000000000], [2608200000000, 2610000000000]) (some (7, 1, 4)) (some
      (7, 1, 4)) (.next ([823200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1,
      4)) (some (7, 1, 4)) (.next ([6705000000000], [2805000000000]) (some (7, 1, 4)) (some (7, 1,
      4)) (.next ([196800000000, -2610000000000], [116400000000, 5220000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([5625000000000], [3375000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([766800000000, -2610000000000], [626400000000, 5220000000000]) (some (7, 1, 4)) (some
      (7, 1, 7)) (.next ([570000000000], [510000000000]) (some (7, 1, 7)) (some (7, 1, 7)) (.next
      ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1, 7)) (some (7, 1,
      7)) (.next ([510000000000], [570000000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.next
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) (some (7, 2, 7)) (some (7, 2,
      7)) (.next ([116400000000, 5220000000000], [196800000000, -2610000000000]) (some (7, 2, 7))
      (some (7, 2, 7)) fan7Owner0Part0)))))))))))))))))) (.split (3836) (60106) (116376) (15494700)
      (.witnessedFan (.next ([1393200000000, 2610000000000], [313200000000, 2610000000000]) (some
      (7, 1, 4)) (some (7, 1, 4)) (.next ([7018200000000, 2610000000000], [1668600000000,
      -5220000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([7331400000000, 5220000000000],
      [1981800000000, -2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([626400000000,
      5220000000000], [196800000000, -2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([6195000000000], [2295000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([7018200000000,
      2610000000000], [2608200000000, 2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([823200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1, 4)) (some (7, 1,
      4)) (.next ([6705000000000], [2805000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([5625000000000], [3375000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([196800000000,
      -2610000000000], [116400000000, 5220000000000]) (some (7, 1, 4)) (some (7, 1, 7)) (.next
      ([766800000000, -2610000000000], [626400000000, 5220000000000]) (some (7, 1, 7)) (some (7, 1,
      7)) (.next ([570000000000], [510000000000]) (some (7, 1, 7)) (some (7, 1, 7)) (.next
      ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1, 7)) (some (7, 1,
      7)) (.next ([510000000000], [570000000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.next
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) (some (7, 2, 7)) (some (7, 2,
      7)) fan7Owner0Part1)))))))))))))))) (.witnessedFan (.next ([1393200000000, 2610000000000],
      [313200000000, 2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([7331400000000,
      5220000000000], [1981800000000, -2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([626400000000, 5220000000000], [196800000000, -2610000000000]) (some (7, 1, 4)) (some (7, 1,
      4)) (.next ([6391800000000, -2610000000000], [1981800000000, -2610000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([6195000000000], [2295000000000]) (some (7, 1, 4)) (some (7, 1, 4))
      (.next ([7018200000000, 2610000000000], [2608200000000, 2610000000000]) (some (7, 1, 4)) (some
      (7, 1, 4)) (.next ([823200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1,
      4)) (some (7, 1, 4)) (.next ([6705000000000], [2805000000000]) (some (7, 1, 4)) (some (7, 1,
      4)) (.next ([5625000000000], [3375000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([196800000000, -2610000000000], [116400000000, 5220000000000]) (some (7, 1, 4)) (some (7, 1,
      7)) (.next ([766800000000, -2610000000000], [626400000000, 5220000000000]) (some (7, 1, 7))
      (some (7, 1, 7)) (.next ([570000000000], [510000000000]) (some (7, 1, 7)) (some (7, 1, 7))
      (.next ([313200000000, 2610000000000], [313200000000, 2610000000000]) (some (7, 1, 7)) (some
      (7, 1, 7)) (.next ([510000000000], [570000000000]) (some (7, 1, 7)) (some (7, 2, 7)) (.next
      ([626400000000, 5220000000000], [766800000000, -2610000000000]) (some (7, 2, 7)) (some (7, 2,
      7)) fan7Owner0Part2)))))))))))))))))) (.witnessedFan (.next ([7018200000000, 2610000000000],
      [1668600000000, -5220000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([1393200000000,
      2610000000000], [313200000000, 2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next
      ([626400000000, 5220000000000], [196800000000, -2610000000000]) (some (7, 1, 4)) (some (7, 1,
      4)) (.next ([7331400000000, 5220000000000], [1981800000000, -2610000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([6391800000000, -2610000000000], [1981800000000, -2610000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) (.next ([6195000000000], [2295000000000]) (some (7, 1, 4))
      (some (7, 1, 4)) (.next ([7018200000000, 2610000000000], [2608200000000, 2610000000000]) (some
      (7, 1, 4)) (some (7, 1, 4)) (.next ([823200000000, 2610000000000], [313200000000,
      2610000000000]) (some (7, 1, 4)) (some (7, 1, 4)) (.next ([6705000000000], [2805000000000])
      (some (7, 1, 4)) (some (7, 1, 4)) fan7Owner0Part3))))))))))) (den := 9000000000000) (fuel :=
      12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    refine split_check_of_checks ?_ ?_ ?_ ?_ ?_
    · decide
    · decide
    · decide
    · refine split_check_of_checks ?_ ?_ ?_ ?_ ?_
      · decide
      · decide
      · decide
      · simp only [ExclusionHint.check, FanWitness.check, checkedFan7Owner0Part0,
          Bool.and_eq_true, and_true]
        repeat' apply And.intro
        all_goals decide
      · refine split_check_of_checks ?_ ?_ ?_ ?_ ?_
        · decide
        · decide
        · decide
        · simp only [ExclusionHint.check, FanWitness.check, checkedFan7Owner0Part1,
            Bool.and_eq_true, and_true]
          repeat' apply And.intro
          all_goals decide
        · simp only [ExclusionHint.check, FanWitness.check, checkedFan7Owner0Part2,
            Bool.and_eq_true, and_true]
          repeat' apply And.intro
          all_goals decide
    · simp only [ExclusionHint.check, FanWitness.check, checkedFan7Owner0Part3,
        Bool.and_eq_true, and_true]
      repeat' apply And.intro
      all_goals decide

theorem excluded7_1 : ExcludedOn (model7.B 1 ++ [step7.q]) 9000000000000 (model7.caps 1) (model7.ord
    1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_1

theorem excluded7_2 : ExcludedOn (model7.B 2 ++ [step7.q]) 9000000000000 (model7.caps 2) (model7.ord
    2) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_2

theorem excluded7_4 : ExcludedOn (model7.B 4 ++ [step7.q]) 9000000000000 (model7.caps 4) (model7.ord
    4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_4

theorem excluded7_5 : ExcludedOn (model7.B 5 ++ [step7.q]) 9000000000000 (model7.caps 5) (model7.ord
    5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_5

theorem excluded7_6 : ExcludedOn (model7.B 6 ++ [step7.q]) 9000000000000 (model7.caps 6) (model7.ord
    6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_6

theorem excluded7_7 : ExcludedOn (model7.B 7 ++ [step7.q]) 9000000000000 (model7.caps 7) (model7.ord
    7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_7

theorem excluded7_8 : ExcludedOn (model7.B 8 ++ [step7.q]) 9000000000000 (model7.caps 8) (model7.ord
    8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_8

theorem excluded7_9 : ExcludedOn (model7.B 9 ++ [step7.q]) 9000000000000 (model7.caps 9) (model7.ord
    9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded7_9

theorem checked7 : StepValid model7 9000000000000 step7 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · apply forall_checkpoint_owners
    all_goals intro hj
    · exact excluded7_0
    · exact excluded7_1
    · exact excluded7_2
    · exact (hj rfl).elim
    · exact excluded7_4
    · exact excluded7_5
    · exact excluded7_6
    · exact excluded7_7
    · exact excluded7_8
    · exact excluded7_9
theorem next7 : model7.insert step7 = model8 := by
  apply Model.ext_checkpoint_owners
  intro j
  fin_cases j
  all_goals constructor
  all_goals try
    guard_target = _ ∧ _
    constructor
  all_goals try
    guard_target = (_ : List IPoint) = _
    as_aux_lemma => rfl
  all_goals try
    guard_target = (_ : List Cap) = _
    as_aux_lemma => rfl
  all_goals as_aux_lemma => rfl

end Aown120000130000
end ConwaySoifer.Simplified.Certificates

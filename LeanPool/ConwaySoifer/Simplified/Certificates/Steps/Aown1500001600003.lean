/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Certificates.FanData.Aown1500001600003
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part0
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part1
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part2
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part3
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part4
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part5
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part6
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part7
import LeanPool.ConwaySoifer.Simplified.Certificates.FanChecks.Aown1500001600003Part8

public import LeanPool.ConwaySoifer.Simplified.Certificates.Checkpoints.Aown150000160000

/-!
# Aown 150000 160000 3

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
namespace Aown150000160000

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan24Owner0Part3Checks :
    (fan24Owner0Part0.check (model24.B 0 ++ [step24.q]) 9000000000000
      (model24.caps 0) 0 1 100 12
      ([-1005000000000], [2880000000000]) = true) ∧
    (fan24Owner0Part1.check (model24.B 0 ++ [step24.q]) 9000000000000
      (model24.caps 0) 0 1 100 12
      ([0, 0], [1134000000000, 7560000000000]) = true) ∧
    (fan24Owner0Part2.check (model24.B 0 ++ [step24.q]) 9000000000000
      (model24.caps 0) 0 1 100 12
      ([3075000000000], [2100000000000]) = true) ∧
    (fan24Owner0Part3.check (model24.B 0 ++ [step24.q]) 9000000000000
      (model24.caps 0) 0 1 100 12
      ([4275000000000], [45000000000]) = true) := by
  have checkedTail0 :
      fan24Owner0Part0.check (model24.B 0 ++ [step24.q]) 9000000000000
        (model24.caps 0) 0 1 100 12
        ([-1005000000000], [2880000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan24Owner0Part1.check (model24.B 0 ++ [step24.q]) 9000000000000
        (model24.caps 0) 0 1 100 12
        ([0, 0], [1134000000000, 7560000000000]) = true := by
    delta fan24Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail2 :
      fan24Owner0Part2.check (model24.B 0 ++ [step24.q]) 9000000000000
        (model24.caps 0) 0 1 100 12
        ([3075000000000], [2100000000000]) = true := by
    delta fan24Owner0Part2
    simp only [FanWitness.check, checkedTail1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail3 :
      fan24Owner0Part3.check (model24.B 0 ++ [step24.q]) 9000000000000
        (model24.caps 0) 0 1 100 12
        ([4275000000000], [45000000000]) = true := by
    delta fan24Owner0Part3
    simp only [FanWitness.check, checkedTail2,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1, checkedTail2, checkedTail3⟩

private theorem checkedFan24Owner0Part3 :
    fan24Owner0Part3.check (model24.B 0 ++ [step24.q]) 9000000000000
      (model24.caps 0) 0 1 100 12
      ([4275000000000], [45000000000]) = true := by
  exact checkedFan24Owner0Part3Checks.2.2.2

theorem excluded24_0 : ExcludedOn (model24.B 0 ++ [step24.q]) 9000000000000 (model24.caps 0)
    (model24.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded24Owner0)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded24Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan24Owner0Part3,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded24_1 : ExcludedOn (model24.B 1 ++ [step24.q]) 9000000000000 (model24.caps 1)
    (model24.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded24_1

theorem excluded24_2 : ExcludedOn (model24.B 2 ++ [step24.q]) 9000000000000 (model24.caps 2)
    (model24.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded24_2

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan24Owner4Part0 :
    fan24Owner4Part0.check (model24.B 4 ++ [step24.q]) 9000000000000
      (model24.caps 4) 0 1 100 12
      ([4875000000000], [3450000000000, -9000000000000]) = true := by
  decide +kernel

theorem excluded24_4 : ExcludedOn (model24.B 4 ++ [step24.q]) 9000000000000 (model24.caps 4)
    (model24.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded24Owner4)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide)
      0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded24Owner4
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan24Owner4Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded24_5 : ExcludedOn (model24.B 5 ++ [step24.q]) 9000000000000 (model24.caps 5)
    (model24.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded24_5

theorem excluded24_6 : ExcludedOn (model24.B 6 ++ [step24.q]) 9000000000000 (model24.caps 6)
    (model24.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded24_6

theorem excluded24_7 : ExcludedOn (model24.B 7 ++ [step24.q]) 9000000000000 (model24.caps 7)
    (model24.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded24_7

theorem excluded24_8 : ExcludedOn (model24.B 8 ++ [step24.q]) 9000000000000 (model24.caps 8)
    (model24.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded24_8

theorem excluded24_9 : ExcludedOn (model24.B 9 ++ [step24.q]) 9000000000000 (model24.caps 9)
    (model24.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded24_9

theorem checked24 : StepValid model24 9000000000000 step24 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded24_0
    · exact excluded24_1
    · exact excluded24_2
    · exact (hj rfl).elim
    · exact excluded24_4
    · exact excluded24_5
    · exact excluded24_6
    · exact excluded24_7
    · exact excluded24_8
    · exact excluded24_9
theorem next24 : model24.insert step24 = model25 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded25_0 : ExcludedOn (model25.B 0 ++ [step25.q]) 9000000000000 (model25.caps 0)
    (model25.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 6 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_0

theorem excluded25_1 : ExcludedOn (model25.B 1 ++ [step25.q]) 9000000000000 (model25.caps 1)
    (model25.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_1

theorem excluded25_2 : ExcludedOn (model25.B 2 ++ [step25.q]) 9000000000000 (model25.caps 2)
    (model25.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_2

theorem excluded25_3 : ExcludedOn (model25.B 3 ++ [step25.q]) 9000000000000 (model25.caps 3)
    (model25.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_3

theorem excluded25_4 : ExcludedOn (model25.B 4 ++ [step25.q]) 9000000000000 (model25.caps 4)
    (model25.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 4 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_4

theorem excluded25_6 : ExcludedOn (model25.B 6 ++ [step25.q]) 9000000000000 (model25.caps 6)
    (model25.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_6

theorem excluded25_7 : ExcludedOn (model25.B 7 ++ [step25.q]) 9000000000000 (model25.caps 7)
    (model25.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_7

theorem excluded25_8 : ExcludedOn (model25.B 8 ++ [step25.q]) 9000000000000 (model25.caps 8)
    (model25.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_8

theorem excluded25_9 : ExcludedOn (model25.B 9 ++ [step25.q]) 9000000000000 (model25.caps 9)
    (model25.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded25_9

theorem checked25 : StepValid model25 9000000000000 step25 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
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
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan26Owner0Part3Checks :
    (fan26Owner0Part0.check (model26.B 0 ++ [step26.q]) 9000000000000
      (model26.caps 0) 0 1 100 12
      ([-3000000000000], [9450000000000]) = true) ∧
    (fan26Owner0Part1.check (model26.B 0 ++ [step26.q]) 9000000000000
      (model26.caps 0) 0 1 100 12
      ([-45000000000], [4320000000000]) = true) ∧
    (fan26Owner0Part2.check (model26.B 0 ++ [step26.q]) 9000000000000
      (model26.caps 0) 0 1 100 12
      ([1875000000000], [1005000000000]) = true) ∧
    (fan26Owner0Part3.check (model26.B 0 ++ [step26.q]) 9000000000000
      (model26.caps 0) 0 1 100 12
      ([2250000000000], [45000000000]) = true) := by
  have checkedTail0 :
      fan26Owner0Part0.check (model26.B 0 ++ [step26.q]) 9000000000000
        (model26.caps 0) 0 1 100 12
        ([-3000000000000], [9450000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan26Owner0Part1.check (model26.B 0 ++ [step26.q]) 9000000000000
        (model26.caps 0) 0 1 100 12
        ([-45000000000], [4320000000000]) = true := by
    delta fan26Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail2 :
      fan26Owner0Part2.check (model26.B 0 ++ [step26.q]) 9000000000000
        (model26.caps 0) 0 1 100 12
        ([1875000000000], [1005000000000]) = true := by
    delta fan26Owner0Part2
    simp only [FanWitness.check, checkedTail1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail3 :
      fan26Owner0Part3.check (model26.B 0 ++ [step26.q]) 9000000000000
        (model26.caps 0) 0 1 100 12
        ([2250000000000], [45000000000]) = true := by
    delta fan26Owner0Part3
    simp only [FanWitness.check, checkedTail2,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1, checkedTail2, checkedTail3⟩

private theorem checkedFan26Owner0Part3 :
    fan26Owner0Part3.check (model26.B 0 ++ [step26.q]) 9000000000000
      (model26.caps 0) 0 1 100 12
      ([2250000000000], [45000000000]) = true := by
  exact checkedFan26Owner0Part3Checks.2.2.2

theorem excluded26_0 : ExcludedOn (model26.B 0 ++ [step26.q]) 9000000000000 (model26.caps 0)
    (model26.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded26Owner0)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded26Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan26Owner0Part3,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded26_1 : ExcludedOn (model26.B 1 ++ [step26.q]) 9000000000000 (model26.caps 1)
    (model26.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded26Owner1)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded26Owner1
  as_aux_lemma => exact checkedWitnessForExcluded26_1

theorem excluded26_3 : ExcludedOn (model26.B 3 ++ [step26.q]) 9000000000000 (model26.caps 3)
    (model26.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded26_3

theorem excluded26_4 : ExcludedOn (model26.B 4 ++ [step26.q]) 9000000000000 (model26.caps 4)
    (model26.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded26_4

theorem excluded26_5 : ExcludedOn (model26.B 5 ++ [step26.q]) 9000000000000 (model26.caps 5)
    (model26.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded26_5

theorem excluded26_6 : ExcludedOn (model26.B 6 ++ [step26.q]) 9000000000000 (model26.caps 6)
    (model26.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded26_6

theorem excluded26_7 : ExcludedOn (model26.B 7 ++ [step26.q]) 9000000000000 (model26.caps 7)
    (model26.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded26Owner7)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded26Owner7
  as_aux_lemma => exact checkedWitnessForExcluded26_7

theorem excluded26_8 : ExcludedOn (model26.B 8 ++ [step26.q]) 9000000000000 (model26.caps 8)
    (model26.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded26_8

theorem excluded26_9 : ExcludedOn (model26.B 9 ++ [step26.q]) 9000000000000 (model26.caps 9)
    (model26.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded26_9

theorem checked26 : StepValid model26 9000000000000 step26 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded26_0
    · exact excluded26_1
    · exact (hj rfl).elim
    · exact excluded26_3
    · exact excluded26_4
    · exact excluded26_5
    · exact excluded26_6
    · exact excluded26_7
    · exact excluded26_8
    · exact excluded26_9
theorem next26 : model26.insert step26 = model27 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan27Owner0Part2Checks :
    (fan27Owner0Part0.check (model27.B 0 ++ [step27.q]) 9000000000000
      (model27.caps 0) 0 1 100 12
      ([-2025000000000], [8700000000000]) = true) ∧
    (fan27Owner0Part1.check (model27.B 0 ++ [step27.q]) 9000000000000
      (model27.caps 0) 0 1 100 12
      ([705000000000], [5295000000000]) = true) ∧
    (fan27Owner0Part2.check (model27.B 0 ++ [step27.q]) 9000000000000
      (model27.caps 0) 0 1 100 12
      ([7275000000000], [1725000000000]) = true) := by
  have checkedTail0 :
      fan27Owner0Part0.check (model27.B 0 ++ [step27.q]) 9000000000000
        (model27.caps 0) 0 1 100 12
        ([-2025000000000], [8700000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan27Owner0Part1.check (model27.B 0 ++ [step27.q]) 9000000000000
        (model27.caps 0) 0 1 100 12
        ([705000000000], [5295000000000]) = true := by
    delta fan27Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail2 :
      fan27Owner0Part2.check (model27.B 0 ++ [step27.q]) 9000000000000
        (model27.caps 0) 0 1 100 12
        ([7275000000000], [1725000000000]) = true := by
    delta fan27Owner0Part2
    simp only [FanWitness.check, checkedTail1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1, checkedTail2⟩

private theorem checkedFan27Owner0Part2 :
    fan27Owner0Part2.check (model27.B 0 ++ [step27.q]) 9000000000000
      (model27.caps 0) 0 1 100 12
      ([7275000000000], [1725000000000]) = true := by
  exact checkedFan27Owner0Part2Checks.2.2

theorem excluded27_0 : ExcludedOn (model27.B 0 ++ [step27.q]) 9000000000000 (model27.caps 0)
    (model27.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded27Owner0)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded27Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan27Owner0Part2,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded27_1 : ExcludedOn (model27.B 1 ++ [step27.q]) 9000000000000 (model27.caps 1)
    (model27.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded27Owner1)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded27Owner1
  as_aux_lemma => exact checkedWitnessForExcluded27_1

theorem excluded27_3 : ExcludedOn (model27.B 3 ++ [step27.q]) 9000000000000 (model27.caps 3)
    (model27.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded27_3

theorem excluded27_4 : ExcludedOn (model27.B 4 ++ [step27.q]) 9000000000000 (model27.caps 4)
    (model27.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded27_4

theorem excluded27_5 : ExcludedOn (model27.B 5 ++ [step27.q]) 9000000000000 (model27.caps 5)
    (model27.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded27_5

theorem excluded27_6 : ExcludedOn (model27.B 6 ++ [step27.q]) 9000000000000 (model27.caps 6)
    (model27.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded27_6

theorem excluded27_7 : ExcludedOn (model27.B 7 ++ [step27.q]) 9000000000000 (model27.caps 7)
    (model27.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded27Owner7)
      (den := 9000000000000) (fuel := 12) (by as_aux_lemma => decide)
      0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded27Owner7
  as_aux_lemma => exact checkedWitnessForExcluded27_7

theorem excluded27_8 : ExcludedOn (model27.B 8 ++ [step27.q]) 9000000000000 (model27.caps 8)
    (model27.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded27_8

theorem excluded27_9 : ExcludedOn (model27.B 9 ++ [step27.q]) 9000000000000 (model27.caps 9)
    (model27.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded27_9

theorem checked27 : StepValid model27 9000000000000 step27 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded27_0
    · exact excluded27_1
    · exact (hj rfl).elim
    · exact excluded27_3
    · exact excluded27_4
    · exact excluded27_5
    · exact excluded27_6
    · exact excluded27_7
    · exact excluded27_8
    · exact excluded27_9
theorem next27 : model27.insert step27 = model28 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan28Owner0Part2Checks :
    (fan28Owner0Part0.check (model28.B 0 ++ [step28.q]) 9000000000000
      (model28.caps 0) 0 1 100 12
      ([-1800000000000], [7500000000000]) = true) ∧
    (fan28Owner0Part1.check (model28.B 0 ++ [step28.q]) 9000000000000
      (model28.caps 0) 0 1 100 12
      ([150000000000], [7050000000000]) = true) ∧
    (fan28Owner0Part2.check (model28.B 0 ++ [step28.q]) 9000000000000
      (model28.caps 0) 0 1 100 12
      ([5700000000000], [1800000000000]) = true) := by
  have checkedTail0 :
      fan28Owner0Part0.check (model28.B 0 ++ [step28.q]) 9000000000000
        (model28.caps 0) 0 1 100 12
        ([-1800000000000], [7500000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan28Owner0Part1.check (model28.B 0 ++ [step28.q]) 9000000000000
        (model28.caps 0) 0 1 100 12
        ([150000000000], [7050000000000]) = true := by
    delta fan28Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail2 :
      fan28Owner0Part2.check (model28.B 0 ++ [step28.q]) 9000000000000
        (model28.caps 0) 0 1 100 12
        ([5700000000000], [1800000000000]) = true := by
    delta fan28Owner0Part2
    simp only [FanWitness.check, checkedTail1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1, checkedTail2⟩

private theorem checkedFan28Owner0Part2 :
    fan28Owner0Part2.check (model28.B 0 ++ [step28.q]) 9000000000000
      (model28.caps 0) 0 1 100 12
      ([5700000000000], [1800000000000]) = true := by
  exact checkedFan28Owner0Part2Checks.2.2

theorem excluded28_0 : ExcludedOn (model28.B 0 ++ [step28.q]) 9000000000000 (model28.caps 0)
    (model28.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded28Owner0)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  delta witnessForExcluded28Owner0
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan28Owner0Part2,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded28_1 : ExcludedOn (model28.B 1 ++ [step28.q]) 9000000000000 (model28.caps 1)
    (model28.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded28Owner1)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded28Owner1
  as_aux_lemma => exact checkedWitnessForExcluded28_1

theorem excluded28_3 : ExcludedOn (model28.B 3 ++ [step28.q]) 9000000000000 (model28.caps 3)
    (model28.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded28_3

theorem excluded28_4 : ExcludedOn (model28.B 4 ++ [step28.q]) 9000000000000 (model28.caps 4)
    (model28.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded28_4

theorem excluded28_5 : ExcludedOn (model28.B 5 ++ [step28.q]) 9000000000000 (model28.caps 5)
    (model28.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded28_5

theorem excluded28_6 : ExcludedOn (model28.B 6 ++ [step28.q]) 9000000000000 (model28.caps 6)
    (model28.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded28_6

theorem excluded28_7 : ExcludedOn (model28.B 7 ++ [step28.q]) 9000000000000 (model28.caps 7)
    (model28.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded28Owner7)
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded28Owner7
  as_aux_lemma => exact checkedWitnessForExcluded28_7

theorem excluded28_8 : ExcludedOn (model28.B 8 ++ [step28.q]) 9000000000000 (model28.caps 8)
    (model28.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded28_8

theorem excluded28_9 : ExcludedOn (model28.B 9 ++ [step28.q]) 9000000000000 (model28.caps 9)
    (model28.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded28_9

theorem checked28 : StepValid model28 9000000000000 step28 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded28_0
    · exact excluded28_1
    · exact (hj rfl).elim
    · exact excluded28_3
    · exact excluded28_4
    · exact excluded28_5
    · exact excluded28_6
    · exact excluded28_7
    · exact excluded28_8
    · exact excluded28_9
theorem next28 : model28.insert step28 = model29 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

-- Verify the shared tails in one proof to bound the kernel working set.
private theorem checkedFan29Owner0Part7Checks :
    (fan29Owner0Part0.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 0 485 95100 12
      ([-3900000000000], [9750000000000]) = true) ∧
    (fan29Owner0Part1.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 0 485 95100 12
      ([-45000000000], [4320000000000]) = true) ∧
    (fan29Owner0Part2.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 0 485 95100 12
      ([2997000000000, -2520000000000], [2106000000000, 5040000000000]) = true) ∧
    (fan29Owner0Part3.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 0 485 95100 12
      ([2250000000000], [45000000000]) = true) ∧
    (fan29Owner0Part4.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 485 951 95100 12
      ([-3828000000000, -2520000000000], [9756000000000, 5040000000000]) = true) ∧
    (fan29Owner0Part5.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 485 951 95100 12
      ([-192000000000, 2520000000000], [6948000000000, 2520000000000]) = true) ∧
    (fan29Owner0Part6.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 485 951 95100 12
      ([5100000000000], [4200000000000]) = true) ∧
    (fan29Owner0Part7.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 485 951 95100 12
      ([6156000000000, 5040000000000], [972000000000, -2520000000000]) = true) := by
  have checkedTail0 :
      fan29Owner0Part0.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 0 485 95100 12
        ([-3900000000000], [9750000000000]) = true := by
    decide +kernel
  have checkedTail1 :
      fan29Owner0Part1.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 0 485 95100 12
        ([-45000000000], [4320000000000]) = true := by
    delta fan29Owner0Part1
    simp only [FanWitness.check, checkedTail0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail2 :
      fan29Owner0Part2.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 0 485 95100 12
        ([2997000000000, -2520000000000], [2106000000000, 5040000000000]) = true := by
    delta fan29Owner0Part2
    simp only [FanWitness.check, checkedTail1,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail3 :
      fan29Owner0Part3.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 0 485 95100 12
        ([2250000000000], [45000000000]) = true := by
    delta fan29Owner0Part3
    simp only [FanWitness.check, checkedTail2,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail4 :
      fan29Owner0Part4.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 485 951 95100 12
        ([-3828000000000, -2520000000000], [9756000000000, 5040000000000]) = true := by
    decide +kernel
  have checkedTail5 :
      fan29Owner0Part5.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 485 951 95100 12
        ([-192000000000, 2520000000000], [6948000000000, 2520000000000]) = true := by
    delta fan29Owner0Part5
    simp only [FanWitness.check, checkedTail4,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail6 :
      fan29Owner0Part6.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 485 951 95100 12
        ([5100000000000], [4200000000000]) = true := by
    delta fan29Owner0Part6
    simp only [FanWitness.check, checkedTail5,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have checkedTail7 :
      fan29Owner0Part7.check (model29.B 0 ++ [step29.q]) 9000000000000
        (model29.caps 0) 485 951 95100 12
        ([6156000000000, 5040000000000], [972000000000, -2520000000000]) = true := by
    delta fan29Owner0Part7
    simp only [FanWitness.check, checkedTail6,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  exact ⟨checkedTail0, checkedTail1, checkedTail2, checkedTail3, checkedTail4, checkedTail5,
    checkedTail6, checkedTail7⟩

private theorem checkedFan29Owner0Part3 :
    fan29Owner0Part3.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 0 485 95100 12
      ([2250000000000], [45000000000]) = true := by
  exact checkedFan29Owner0Part7Checks.2.2.2.1

private theorem checkedFan29Owner0Part7 :
    fan29Owner0Part7.check (model29.B 0 ++ [step29.q]) 9000000000000
      (model29.caps 0) 485 951 95100 12
      ([6156000000000, 5040000000000], [972000000000, -2520000000000]) = true := by
  exact checkedFan29Owner0Part7Checks.2.2.2.2.2.2.2

theorem excluded29_0 : ExcludedOn (model29.B 0 ++ [step29.q]) 9000000000000 (model29.caps 0)
    (model29.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.split (0) (485) (951) (95100) (.witnessedFan (.next ([4275000000000],
      [45000000000]) (some (7, 2, 11)) (some (8, 2, 11)) (.next ([5400000000000], [75000000000])
      (some (8, 2, 11)) (some (8, 2, 11)) (.next ([2250000000000], [45000000000]) (some (8, 2, 11))
      (some (8, 2, 11)) fan29Owner0Part3)))) (.witnessedFan (.next ([4275000000000], [45000000000])
      (some (7, 2, 11)) (some (8, 2, 11)) (.next ([5400000000000], [75000000000]) (some (8, 2, 11))
      (some (8, 2, 11)) (.next ([2250000000000], [45000000000]) (some (8, 2, 11)) (some (8, 2, 11))
      (.next ([3375000000000], [75000000000]) (some (8, 2, 11)) (some (9, 2, 11)) (.next
      ([6756000000000, 5040000000000], [192000000000, -2520000000000]) (some (9, 2, 11)) (some (9,
      2, 11)) (.next ([1125000000000], [30000000000]) (some (9, 2, 11)) (some (9, 2, 11)) (.next
      ([6750000000000], [270000000000]) (some (9, 2, 11)) (some (10, 2, 11)) (.next ([1056000000000,
      5040000000000], [72000000000, -2520000000000]) (some (10, 2, 11)) (some (10, 2, 11)) (.next
      ([6855000000000], [1020000000000]) (some (10, 2, 11)) (some (10, 2, 11)) (.next
      ([6378000000000, 2520000000000], [948000000000, 2520000000000]) (some (10, 2, 11)) (some (10,
      2, 11)) (.next ([6156000000000, 5040000000000], [972000000000, -2520000000000]) (some (10, 2,
      11)) (some (10, 2, 11)) fan29Owner0Part7)))))))))))))
      (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100
      (by as_aux_lemma => decide) ?_
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan29Owner0Part3, checkedFan29Owner0Part7,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded29_1 : ExcludedOn (model29.B 1 ++ [step29.q]) 9000000000000 (model29.caps 1)
    (model29.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 2 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_1

theorem excluded29_2 : ExcludedOn (model29.B 2 ++ [step29.q]) 9000000000000 (model29.caps 2)
    (model29.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_2

theorem excluded29_3 : ExcludedOn (model29.B 3 ++ [step29.q]) 9000000000000 (model29.caps 3)
    (model29.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_3

theorem excluded29_4 : ExcludedOn (model29.B 4 ++ [step29.q]) 9000000000000 (model29.caps 4)
    (model29.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 6) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_4

theorem excluded29_5 : ExcludedOn (model29.B 5 ++ [step29.q]) 9000000000000 (model29.caps 5)
    (model29.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_5

theorem excluded29_7 : ExcludedOn (model29.B 7 ++ [step29.q]) 9000000000000 (model29.caps 7)
    (model29.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_7

theorem excluded29_8 : ExcludedOn (model29.B 8 ++ [step29.q]) 9000000000000 (model29.caps 8)
    (model29.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_8

theorem excluded29_9 : ExcludedOn (model29.B 9 ++ [step29.q]) 9000000000000 (model29.caps 9)
    (model29.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded29_9

theorem checked29 : StepValid model29 9000000000000 step29 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded29_0
    · exact excluded29_1
    · exact excluded29_2
    · exact excluded29_3
    · exact excluded29_4
    · exact excluded29_5
    · exact (hj rfl).elim
    · exact excluded29_7
    · exact excluded29_8
    · exact excluded29_9
theorem next29 : model29.insert step29 = model30 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded30_0 : ExcludedOn (model30.B 0 ++ [step30.q]) 9000000000000 (model30.caps 0)
    (model30.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_0

theorem excluded30_1 : ExcludedOn (model30.B 1 ++ [step30.q]) 9000000000000 (model30.caps 1)
    (model30.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_1

theorem excluded30_2 : ExcludedOn (model30.B 2 ++ [step30.q]) 9000000000000 (model30.caps 2)
    (model30.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_2

theorem excluded30_3 : ExcludedOn (model30.B 3 ++ [step30.q]) 9000000000000 (model30.caps 3)
    (model30.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.pair 1 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_3

-- Limit kernel memory by checking this fan tail separately.
private theorem checkedFan30Owner4Part0 :
    fan30Owner4Part0.check (model30.B 4 ++ [step30.q]) 9000000000000
      (model30.caps 4) 0 1 100 12
      ([1350000000000, 9000000000000], [1350000000000, 9000000000000]) = true := by
  decide +kernel

theorem excluded30_4 : ExcludedOn (model30.B 4 ++ [step30.q]) 9000000000000 (model30.caps 4)
    (model30.ord 4) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded30Owner4)
      (den :=
      9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded30Owner4
  as_aux_lemma =>
    simp only [ExclusionHint.check, FanWitness.check,
      checkedFan30Owner4Part0,
      Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide

theorem excluded30_5 : ExcludedOn (model30.B 5 ++ [step30.q]) 9000000000000 (model30.caps 5)
    (model30.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_5

theorem excluded30_6 : ExcludedOn (model30.B 6 ++ [step30.q]) 9000000000000 (model30.caps 6)
    (model30.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_6

theorem excluded30_7 : ExcludedOn (model30.B 7 ++ [step30.q]) 9000000000000 (model30.caps 7)
    (model30.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_7

theorem excluded30_9 : ExcludedOn (model30.B 9 ++ [step30.q]) 9000000000000 (model30.caps 9)
    (model30.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded30_9

theorem checked30 : StepValid model30 9000000000000 step30 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded30_0
    · exact excluded30_1
    · exact excluded30_2
    · exact excluded30_3
    · exact excluded30_4
    · exact excluded30_5
    · exact excluded30_6
    · exact excluded30_7
    · exact (hj rfl).elim
    · exact excluded30_9
theorem next30 : model30.insert step30 = model31 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

theorem excluded31_0 : ExcludedOn (model31.B 0 ++ [step31.q]) 9000000000000 (model31.caps 0)
    (model31.ord 0) 0 1 100 := by
  refine exclude_checkpoint (.pair 6 11) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded31_0

theorem excluded31_1 : ExcludedOn (model31.B 1 ++ [step31.q]) 9000000000000 (model31.caps 1)
    (model31.ord 1) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded31_1

theorem excluded31_2 : ExcludedOn (model31.B 2 ++ [step31.q]) 9000000000000 (model31.caps 2)
    (model31.ord 2) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 7) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded31_2

theorem excluded31_3 : ExcludedOn (model31.B 3 ++ [step31.q]) 9000000000000 (model31.caps 3)
    (model31.ord 3) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded31Owner3)
      (den :=
      9000000000000) (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded31Owner3
  as_aux_lemma => exact checkedWitnessForExcluded31_3

theorem excluded31_5 : ExcludedOn (model31.B 5 ++ [step31.q]) 9000000000000 (model31.caps 5)
    (model31.ord 5) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 5) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded31_5

theorem excluded31_6 : ExcludedOn (model31.B 6 ++ [step31.q]) 9000000000000 (model31.caps 6)
    (model31.ord 6) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 3) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded31_6

theorem excluded31_7 : ExcludedOn (model31.B 7 ++ [step31.q]) 9000000000000 (model31.caps 7)
    (model31.ord 7) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded31_7

theorem excluded31_8 : ExcludedOn (model31.B 8 ++ [step31.q]) 9000000000000 (model31.caps 8)
    (model31.ord 8) 0 1 100 := by
  refine exclude_checkpoint (.witnessedFan witnessForExcluded31Owner8)
      (den := 9000000000000)
      (fuel := 12) (by as_aux_lemma => decide) 0 1 100 (by as_aux_lemma => decide) ?_
  delta witnessForExcluded31Owner8
  as_aux_lemma => exact checkedWitnessForExcluded31_8

theorem excluded31_9 : ExcludedOn (model31.B 9 ++ [step31.q]) 9000000000000 (model31.caps 9)
    (model31.ord 9) 0 1 100 := by
  refine exclude_checkpoint (.pair 0 4) (den := 9000000000000) (fuel := 12)
      (by as_aux_lemma => decide) 0 1
      100 (by as_aux_lemma => decide) ?_
  as_aux_lemma => exact checkedWitnessForExcluded31_9

theorem checked31 : StepValid model31 9000000000000 step31 0 1 100 := by
  apply step_checkpoint (fuel := 12)
  · as_aux_lemma => decide
  · as_aux_lemma => decide
  · as_aux_lemma => rfl
  · intro j hj
    fin_cases j
    · exact excluded31_0
    · exact excluded31_1
    · exact excluded31_2
    · exact excluded31_3
    · exact (hj rfl).elim
    · exact excluded31_5
    · exact excluded31_6
    · exact excluded31_7
    · exact excluded31_8
    · exact excluded31_9
theorem next31 : model31.insert step31 = model32 := by
  apply Model.ext_fields
  all_goals intro j; fin_cases j <;> (as_aux_lemma => rfl)

end Aown150000160000
end ConwaySoifer.Simplified.Certificates

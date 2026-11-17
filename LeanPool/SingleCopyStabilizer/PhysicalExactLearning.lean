/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.QuantumRound
public import LeanPool.SingleCopyStabilizer.PhysicalSampling
public import LeanPool.SingleCopyStabilizer.SharpExactLearning


/-! The actual amplitude experiment realizes the verified label process.
Zero-probability observations are handled without consulting the unknown
stabilizer labels in the physical algorithm. -/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.PhysicalExactLearning

open Measurement PhysicalSampling QuantumRound
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On every possible observation, the physical and algebraic updates agree. -/
theorem label_next_of_supported (S : PureStabilizerState ι)
    (o : ExactLearning.Outcome ι) (hu : o.1 ∈ xProjection S.labels) :
    labels (quantumRound S o) = ExactLearning.next (labels S) o := by
  apply Subtype.ext
  change binaryRound S.labels o.1 o.2 = safeBinaryRound S.labels o.1 o.2
  exact (safeBinaryRound_of_mem S.labels o.1 o.2 hu).symm

/-- Failure to reach full diagonal rank, evaluated on the actual Born
branching experiment with concrete CNOT and H/HS amplitude updates. -/
def failureProbability : ℕ → PureStabilizerState ι → ℝ
  | 0, S => if ExactLearning.rank (labels S) = 0 then 0 else 1
  | t + 1, S => ∑ o : ExactLearning.Outcome ι,
      (outcomePMF S o).toReal * failureProbability t (quantumRound S o)

/-- The finite tree probabilities coincide, with all sampling and physical
gate hypotheses discharged. -/
theorem failureProbability_eq_labelProcess (t : ℕ) (S : PureStabilizerState ι) :
    failureProbability t S = ExactLearning.process.failureProbability t (labels S) := by
  classical
  induction t generalizing S with
  | zero => rfl
  | succ t ih =>
    change (∑ o : ExactLearning.Outcome ι,
      (outcomePMF S o).toReal * failureProbability t (quantumRound S o)) =
      ∑ o : ExactLearning.Outcome ι, ExactLearning.weight (labels S) o *
        ExactLearning.process.failureProbability t (ExactLearning.next (labels S) o)
    apply Finset.sum_congr rfl
    intro o _
    rw [outcomePMF_toReal, ih]
    by_cases hu : o.1 ∈ xProjection S.labels
    · rw [label_next_of_supported S o hu]
    · simp [ExactLearning.weight, labels, hu]

theorem failureProbability_nonneg (t : ℕ) (S : PureStabilizerState ι) :
    0 ≤ failureProbability t S := by
  rw [failureProbability_eq_labelProcess]
  exact ExactLearning.process.failure_probability_nonneg t (labels S)

theorem failureProbability_le_one (t : ℕ) (S : PureStabilizerState ι) :
    failureProbability t S ≤ 1 := by
  rw [failureProbability_eq_labelProcess]
  exact ExactLearning.process.failure_probability_le_one t (labels S)

/-- Physical adaptive compression with a leading `2n` round budget. -/
theorem compression_failure_probability (S : PureStabilizerState ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    failureProbability (SharpExactLearning.roundBudget (Fintype.card ι) δ) S ≤ δ := by
  rw [failureProbability_eq_labelProcess]
  exact SharpExactLearning.compression_failure_probability (labels S) δ hδ hδmax

theorem compression_failure_probability_after_budget (S : PureStabilizerState ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) (T : ℕ)
    (hT : SharpExactLearning.roundBudget (Fintype.card ι) δ ≤ T) :
    failureProbability T S ≤ δ := by
  rw [failureProbability_eq_labelProcess]
  exact SharpExactLearning.compression_failure_probability_after_budget
    (labels S) δ hδ hδmax T hT

end LeanPool.SingleCopyStabilizer.PhysicalExactLearning

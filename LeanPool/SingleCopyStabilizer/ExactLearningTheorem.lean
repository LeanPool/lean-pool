/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Transcript
public import LeanPool.SingleCopyStabilizer.InstructionSemantics


/-!
# Exact qubit learning: correctness and physical resources

This is the public combined theorem. The learner returns a finite recorded
circuit and one computational-basis string. Its exact correctness probability,
copy count, and interpreted elementary gate cost are proved together.

The confidence constants are conservative. Classical machine runtime and
lower bounds are not asserted by this theorem.
-/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.ExactLearningTheorem

open Measurement OutputCorrectness ExactResources
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- Real probability that the returned description is exactly the input
pure state, with global phase ignored. -/
def successProbability (T : ℕ) (S : PureStabilizerState ι) : ℝ :=
  (((descriptionPMF T S).map fun d =>
    decide (SameRay S.amplitude (Circuit.decode d.1 d.2))) true).toReal

/-- Exact recovery at the explicit leading-`2n` round budget. Every possible
execution uses `2T+1` copies and at most `(n+1)T²` elementary gate applications.
The counted instructions implement the circuit used by the learned-state
decoder; they are not merely a separate numerical cost assignment. -/
theorem exact_learning (S : PureStabilizerState ι) (δ : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    let T := SharpExactLearning.roundBudget (Fintype.card ι) δ
    1 - δ ≤ successProbability T S ∧
      ∀ d ∈ (descriptionPMF T S).support,
        d.1.length = T ∧
        protocolCopyCount d.1 = 2 * T + 1 ∧
        protocolGateCost d.1 ≤ (Fintype.card ι + 1) * T ^ 2 ∧
        InstructionSemantics.instructionsEquiv (circuitInstructions d.1) =
          Circuit.circuitEquiv d.1 ∧
        IsNormalized (Circuit.decode d.1 d.2) := by
  classical
  dsimp only
  refine ⟨description_success_probability S δ hδ hδmax, ?_⟩
  intro d hd
  exact ⟨Transcript.supported_length _ S d hd,
    Transcript.supported_copy_count _ S d hd,
    Transcript.supported_protocol_gate_cost _ S d hd,
    InstructionSemantics.circuitInstructions_denote d.1,
    Circuit.decode_normalized d.1 d.2⟩

/-- The number of copies at this budget has the explicit leading `4n` bound. -/
theorem exact_learning_copy_bound (S : PureStabilizerState ι) (δ : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1) (d : Description ι)
    (hd : d ∈ (descriptionPMF
      (SharpExactLearning.roundBudget (Fintype.card ι) δ) S).support) :
    (protocolCopyCount d.1 : ℝ) < 4 * (Fintype.card ι : ℝ) + 11 +
      16 * Real.sqrt ((2 * (Fintype.card ι : ℝ) + 4) * Real.log (1 / δ)) +
      128 * Real.log (1 / δ) := by
  classical
  rw [Transcript.supported_copy_count _ S d hd]
  exact SharpExactLearning.copyBudget_upper (Fintype.card ι) δ hδ hδmax

/-- Every supported output of the exact learner obeys an explicit
`O(n + log(1/δ))` copy bound with a universal constant. -/
theorem exact_learning_copy_bound_linear (hn : 1 ≤ Fintype.card ι)
    (S : PureStabilizerState ι) (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (d : Description ι)
    (hd : d ∈ (descriptionPMF
      (SharpExactLearning.roundBudget (Fintype.card ι) δ) S).support) :
    (protocolCopyCount d.1 : ℝ) <
      136 * ((Fintype.card ι : ℝ) + Real.log (1 / δ)) := by
  classical
  rw [Transcript.supported_copy_count _ S d hd]
  exact SharpExactLearning.copyBudget_linear (Fintype.card ι) hn δ hδ hδmax

end LeanPool.SingleCopyStabilizer.ExactLearningTheorem

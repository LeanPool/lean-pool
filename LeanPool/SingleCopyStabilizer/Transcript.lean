/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.OutputCorrectness
public import LeanPool.SingleCopyStabilizer.ExactResources


/-!
# Finite classical exact-learning transcripts

Every possible returned description contains exactly the prescribed number
of round records. The copy and gate bounds therefore apply to the actual
classical output distribution, rather than an unrelated arbitrary list.
-/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.Transcript

open Measurement OutputCorrectness
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The physical experiment retaining its circuit record and final readout. -/
abbrev transcriptPMF (T : ℕ) (S : PureStabilizerState ι) : PMF (Description ι) :=
  descriptionPMF T S

/-- Its decoded interpretation is exactly the proved output-state law. -/
theorem transcriptPMF_decode (T : ℕ) (S : PureStabilizerState ι) :
    (transcriptPMF T S).map (fun d => Circuit.decode d.1 d.2) = outputPMF T S :=
  descriptionPMF_decode T S

/-- Every possible transcript records exactly one outcome per scheduled round,
including zero differences that append no quantum gates. -/
theorem supported_length (T : ℕ) (S : PureStabilizerState ι) (d : Description ι)
    (hd : d ∈ (transcriptPMF T S).support) : d.1.length = T := by
  classical
  induction T generalizing S d with
  | zero =>
    change d ∈ (descriptionPMF 0 S).support at hd
    rw [descriptionPMF, PMF.mem_support_map_iff] at hd
    obtain ⟨z, _, rfl⟩ := hd
    rfl
  | succ T ih =>
    change d ∈ (descriptionPMF (T + 1) S).support at hd
    rw [descriptionPMF, PMF.mem_support_bind_iff] at hd
    obtain ⟨o, _, hd⟩ := hd
    rw [PMF.mem_support_map_iff] at hd
    obtain ⟨e, he, rfl⟩ := hd
    simpa using congrArg Nat.succ (ih (QuantumRound.quantumRound S o) e he)

/-- Histories of the wrong length have exactly zero output probability. -/
theorem zero_of_length_ne (T : ℕ) (S : PureStabilizerState ι) (d : Description ι)
    (hlen : d.1.length ≠ T) : transcriptPMF T S d = 0 := by
  classical
  by_contra hne
  exact hlen (supported_length T S d ((PMF.mem_support_iff _ _).mpr hne))

/-- The returned finite description corresponds to exactly `2T+1` consumed
input copies, for every possible run and independently of success. -/
theorem supported_copy_count (T : ℕ) (S : PureStabilizerState ι) (d : Description ι)
    (hd : d ∈ (transcriptPMF T S).support) :
    ExactResources.protocolCopyCount d.1 = 2 * T + 1 :=
  ExactResources.protocolCopyCount_eq d.1 T (supported_length T S d hd)

/-- At most `(n+1)T` elementary instructions describe the final circuit. -/
theorem supported_circuit_gate_count (T : ℕ) (S : PureStabilizerState ι)
    (d : Description ι) (hd : d ∈ (transcriptPMF T S).support) :
    ExactResources.listCircuitGateCount d.1 ≤ (Fintype.card ι + 1) * T := by
  classical
  simpa only [supported_length T S d hd] using ExactResources.listCircuitGateCount_le d.1

/-- All gates used on the fresh copies and final readout total at most
`(n+1)T²`, for every supported classical output description. -/
theorem supported_protocol_gate_cost (T : ℕ) (S : PureStabilizerState ι)
    (d : Description ι) (hd : d ∈ (transcriptPMF T S).support) :
    ExactResources.protocolGateCost d.1 ≤ (Fintype.card ι + 1) * T ^ 2 := by
  classical
  simpa only [supported_length T S d hd] using ExactResources.protocolGateCost_le d.1

theorem supported_protocol_gate_cost_two_n (T : ℕ) (S : PureStabilizerState ι)
    (d : Description ι) (hd : d ∈ (transcriptPMF T S).support)
    (hn : 1 ≤ Fintype.card ι) :
    ExactResources.protocolGateCost d.1 ≤ 2 * Fintype.card ι * T ^ 2 := by
  classical
  simpa only [supported_length T S d hd] using
    ExactResources.protocolGateCost_le_two_n d.1 hn

open Classical in
/-- Correctness stated directly on the recorded finite output, with any
round count at least the proved confidence budget. -/
theorem failure_probability_after_budget (S : PureStabilizerState ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) (T : ℕ)
    (hT : SharpExactLearning.roundBudget (Fintype.card ι) δ ≤ T) :
    ((transcriptPMF T S).map fun d =>
      decide (SameRay S.amplitude (Circuit.decode d.1 d.2))) false ≤ ENNReal.ofReal δ := by
  classical
  have h := exact_learning_failure_probability_after_budget S δ hδ hδmax T hT
  unfold outputFailure at h
  rw [← transcriptPMF_decode, PMF.map_comp] at h
  exact h

end LeanPool.SingleCopyStabilizer.Transcript

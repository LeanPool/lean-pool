/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.Circuit
public import LeanPool.SingleCopyStabilizer.QuantumRound
public import LeanPool.SingleCopyStabilizer.PhysicalSampling
public import LeanPool.SingleCopyStabilizer.PhysicalExactLearning


/-! Exact state reconstruction from the adaptive experiment's actual output.
Correctness identifies amplitudes up to a unit-modulus global scalar. -/

@[expose] public section

noncomputable section


namespace LeanPool.SingleCopyStabilizer.OutputCorrectness

open Measurement
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Equality of pure states up to a physically irrelevant global phase. -/
def SameRay (ψ φ : Amplitude ι) : Prop :=
  ∃ c : ℂ, Complex.normSq c = 1 ∧ ψ = c • φ

omit [DecidableEq ι] [Fintype ι] in
theorem sameRay_refl (ψ : Amplitude ι) : SameRay ψ ψ := by
  classical
  exact ⟨1, by simp, by simp⟩

omit [DecidableEq ι] [Fintype ι] in
/-- Reversing a linear gate transports exactly the same global phase. -/
theorem sameRay_inverse_iff (U : Amplitude ι ≃ₗ[ℂ] Amplitude ι)
    (ψ φ : Amplitude ι) : SameRay ψ (U.symm φ) ↔ SameRay (U ψ) φ := by
  classical
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using congrArg U h
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    apply U.injective
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using h

theorem roundEquiv_apply (u : Bits ι) (b : ZMod 2) (ψ : Amplitude ι) :
    Circuit.roundEquiv u b ψ = QuantumRound.applyRoundAmplitude u b ψ := by
  classical
  by_cases hu : u = 0
  · subst u
    simp
  · rw [Circuit.roundEquiv_apply_of_ne u b hu,
      QuantumRound.applyRoundAmplitude_of_ne u b ψ hu, Circuit.correctionEquiv_apply]
    rfl

/-- The actual adaptive learner's returned amplitude. The terminal experiment
reads one computational outcome. Each recursive step performs two fresh-copy
Born measurements and the correction coin, then reverses the recorded round
on the recursively decoded result. -/
def outputPMF : ℕ → PureStabilizerState ι → PMF (Amplitude ι)
  | 0, S => (bornPMF S.amplitude S.normalized).map Circuit.basis
  | t + 1, S => (PhysicalSampling.outcomePMF S).bind fun o =>
      (outputPMF t (QuantumRound.quantumRound S o)).map (Circuit.roundEquiv o.1 o.2).symm

/-- Finite classical output: the chronological round records and one final
computational-basis string. No unknown amplitudes are included in the output. -/
abbrev Description (ι : Type*) := List (Circuit.Outcome ι) × Bits ι

/-- The same physical experiment retaining its classical circuit description. -/
def descriptionPMF : ℕ → PureStabilizerState ι → PMF (Description ι)
  | 0, S => (bornPMF S.amplitude S.normalized).map fun z => ([], z)
  | t + 1, S => (PhysicalSampling.outcomePMF S).bind fun o =>
      (descriptionPMF t (QuantumRound.quantumRound S o)).map fun d => (o :: d.1, d.2)

/-- Interpreting the returned finite description gives exactly the amplitude
distribution in `outputPMF`. -/
theorem descriptionPMF_decode (t : ℕ) (S : PureStabilizerState ι) :
    (descriptionPMF t S).map (fun d => Circuit.decode d.1 d.2) = outputPMF t S := by
  classical
  induction t generalizing S with
  | zero => simp [descriptionPMF, outputPMF, PMF.map_comp, Function.comp_def]
  | succ t ih =>
    rw [descriptionPMF, PMF.map_bind, outputPMF]
    congr 1
    funext o
    rw [← ih, PMF.map_comp, PMF.map_comp]
    congr 1

/-- Every classical description denotes a normalized pure state. -/
theorem description_normalized (d : Description ι) :
    IsNormalized (Circuit.decode d.1 d.2) := Circuit.decode_normalized d.1 d.2

/-- The learner's output distribution is supported on normalized amplitudes. -/
theorem outputPMF_normalized (t : ℕ) (S : PureStabilizerState ι)
    (ψ : Amplitude ι) (hψ : ψ ∈ (outputPMF t S).support) : IsNormalized ψ := by
  classical
  rw [← descriptionPMF_decode, PMF.support_map] at hψ
  obtain ⟨d, _, rfl⟩ := hψ
  exact description_normalized d

open Classical in
/-- Actual probability that the output fails to represent the input state.
The Boolean pushforward avoids introducing a measure on amplitude space. -/
def outputFailure (t : ℕ) (S : PureStabilizerState ι) : ENNReal :=
  ((outputPMF t S).map fun φ => decide (SameRay S.amplitude φ)) false

/-- At full diagonal rank the single final Born readout reconstructs the
current input amplitude up to global phase with probability one. -/
theorem outputFailure_zero_of_rank_zero (S : PureStabilizerState ι)
    (hrank : ExactLearning.rank (PhysicalSampling.labels S) = 0) :
    outputFailure 0 S = 0 := by
  classical
  have hfull := (ExactLearning.rank_zero_iff_full_diagonal
    (PhysicalSampling.labels S)).mp hrank
  obtain ⟨z, c, hc, hamp⟩ := full_diagonal_basis_amplitude S.amplitude S.normalized
    S.labels S.eigenlabels hfull
  have hray : SameRay S.amplitude (Circuit.basis z) := by
    refine ⟨c, hc, ?_⟩
    simpa only [Circuit.smul_basis] using hamp
  have hpmf : bornPMF S.amplitude S.normalized = PMF.pure z := by
    ext x
    by_cases hx : x = z
    · subst x
      simp [bornPMF_apply, bornWeight, hamp, hc, PMF.pure_apply]
    · simp [bornPMF_apply, bornWeight, hamp, hx, PMF.pure_apply]
  simp [outputFailure, outputPMF, hpmf, PMF.pure_map, hray]

/-- The output error is the Born-weighted mean of the errors of later rounds.
Reversing a recorded Clifford cannot create a reconstruction error. -/
theorem outputFailure_succ (t : ℕ) (S : PureStabilizerState ι) :
    outputFailure (t + 1) S = ∑ o : ExactLearning.Outcome ι,
      PhysicalSampling.outcomePMF S o * outputFailure t (QuantumRound.quantumRound S o) := by
  classical
  unfold outputFailure
  rw [outputPMF, PMF.map_bind, PMF.bind_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  rw [PMF.map_comp]
  congr 2
  funext φ
  simp only [Function.comp_apply, sameRay_inverse_iff, roundEquiv_apply,
    QuantumRound.quantumRound_amplitude]
  rfl

/-- The probability of returning the wrong state is at most the probability
of incomplete diagonal compression in the actual physical experiment. -/
theorem outputFailure_le_compression (t : ℕ) (S : PureStabilizerState ι) :
    outputFailure t S ≤ ENNReal.ofReal (PhysicalExactLearning.failureProbability t S) := by
  classical
  induction t generalizing S with
  | zero =>
    by_cases hrank : ExactLearning.rank (PhysicalSampling.labels S) = 0
    · simp [PhysicalExactLearning.failureProbability, hrank,
        outputFailure_zero_of_rank_zero S hrank]
    · simp only [PhysicalExactLearning.failureProbability, ite_eq_right hrank,
        ENNReal.ofReal_one]
      exact PMF.coe_le_one _ _
  | succ t ih =>
    rw [outputFailure_succ, PhysicalExactLearning.failureProbability,
      ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg ENNReal.toReal_nonneg
        (PhysicalExactLearning.failureProbability_nonneg t (QuantumRound.quantumRound S o)))]
    apply Finset.sum_le_sum
    intro o _
    calc
      _ ≤ PhysicalSampling.outcomePMF S o * ENNReal.ofReal
          (PhysicalExactLearning.failureProbability t (QuantumRound.quantumRound S o)) :=
        mul_le_mul_right (ih (QuantumRound.quantumRound S o)) _
      _ = _ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- The actual learner returns the exact input pure state up to global phase,
except with probability at most δ, at the proved leading-2n round budget. -/
theorem exact_learning_failure_probability (S : PureStabilizerState ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    outputFailure (SharpExactLearning.roundBudget (Fintype.card ι) δ) S ≤ ENNReal.ofReal δ := by
  classical
  exact (outputFailure_le_compression _ S).trans (ENNReal.ofReal_le_ofReal
    (PhysicalExactLearning.compression_failure_probability S δ hδ hδmax))

theorem exact_learning_failure_probability_after_budget (S : PureStabilizerState ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) (T : ℕ)
    (hT : SharpExactLearning.roundBudget (Fintype.card ι) δ ≤ T) :
    outputFailure T S ≤ ENNReal.ofReal δ := by
  classical
  exact (outputFailure_le_compression T S).trans (ENNReal.ofReal_le_ofReal
    (PhysicalExactLearning.compression_failure_probability_after_budget S δ hδ hδmax T hT))

open Classical in
/-- The same correctness guarantee stated directly for the finite classical
description that the learner returns. -/
theorem description_failure_probability (S : PureStabilizerState ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ((descriptionPMF (SharpExactLearning.roundBudget (Fintype.card ι) δ) S).map
      fun d => decide (SameRay S.amplitude (Circuit.decode d.1 d.2))) false ≤ ENNReal.ofReal δ := by
  classical
  have h := exact_learning_failure_probability S δ hδ hδmax
  unfold outputFailure at h
  rw [← descriptionPMF_decode, PMF.map_comp] at h
  exact h

/-- For a Boolean correctness experiment, the success and failure
probabilities sum to one. -/
theorem bool_success_probability_ge (p : PMF Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hfailure : p false ≤ ENNReal.ofReal δ) : 1 - δ ≤ (p true).toReal := by
  classical
  have hsum : p true + p false = 1 := by
    have h := p.tsum_coe
    rw [tsum_fintype] at h
    simpa only [Fintype.sum_bool] using h
  have hreal : (p true).toReal + (p false).toReal = 1 := by
    rw [← ENNReal.toReal_add (p.apply_ne_top true) (p.apply_ne_top false), hsum]
    simp
  have hfailreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfailure
  rw [ENNReal.toReal_ofReal hδ] at hfailreal
  linarith

open Classical in
/-- Direct real-valued success guarantee for the returned classical circuit
description: it exactly represents the input pure state with probability
at least `1-δ`. -/
theorem description_success_probability (S : PureStabilizerState ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    1 - δ ≤ (((descriptionPMF (SharpExactLearning.roundBudget (Fintype.card ι) δ) S).map
      fun d => decide (SameRay S.amplitude (Circuit.decode d.1 d.2))) true).toReal := by
  classical
  apply bool_success_probability_ge _ δ hδ.le
  exact description_failure_probability S δ hδ hδmax

end LeanPool.SingleCopyStabilizer.OutputCorrectness

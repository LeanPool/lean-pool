/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneBandLimitedCompactness
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Local Rellich from concrete band-limited cores

The spectral-isolation step of the paper (§2.3) needs compactness of the restriction of
`H¹(ℝ²)` to a bounded disc containing the support of the velocity, quoted there as Rellich's
theorem.  This module reduces that statement to a single literal hypothesis about concrete
coefficient-level operators.

The band-limited API supplies a low-frequency part of the physical `H¹ → L²` embedding at every
real radius.  Specializing to the radii `n + 1` gives a sequence of low-frequency operators with
an exact low/high decomposition and operator-norm convergence to the embedding.  Feeding that
sequence into the abstract norm-limit criterion for compact operators leaves exactly one premise:
compactness of the concrete time--frequency concentration maps
`wholePlaneBandLimitedRestrictionFromCoeff`, proved in
`WholePlaneBandLimitedRellichUnconditional`.  No separate predicate or certificate renames local
Rellich compactness.

## Contents

* Natural-radius low-frequency approximation for whole-plane `H¹`: decay along the positive
  natural radii, the low-frequency sequence with its exact decomposition, and operator-norm
  convergence.
* Local Rellich from concrete band-limited cores: compactness of the finite-measure scalar
  `H¹` restrictions under the literal band-limited premise.
-/

@[expose] public section

/-!
## Natural-radius low-frequency approximation for whole-plane `H¹`

The band-limited API gives a low-frequency part of the physical `H¹ → L²`
embedding at every real radius.  Here we specialize it to the positive radii
`n + 1` and obtain a concrete sequence of low-frequency operators.

The main outputs are the exact low/high decomposition and convergence in
operator norm.  Compactness of the low-frequency operators is proved in the
spatial-frequency truncation modules.
-/

namespace FastDynamo

noncomputable section

open Filter

/-! ## Decay along the positive natural radii -/

/-- At radius `n + 1`, the Fourier-tail decay factor is bounded by the
elementary reciprocal `(n + 1)⁻¹`. -/
theorem h1HighFrequencyDecay_natSucc_le_inv (n : ℕ) :
    h1HighFrequencyDecay ((n : ℝ) + 1) ≤ ((n : ℝ) + 1)⁻¹ := by
  unfold h1HighFrequencyDecay
  have hradius : 0 < (n : ℝ) + 1 := by positivity
  have hsqrt : 0 < Real.sqrt (1 + ((n : ℝ) + 1) ^ 2) := by
    positivity
  apply (inv_le_inv₀ hsqrt hradius).2
  apply Real.le_sqrt_of_sq_le
  linarith

/-- The explicit Fourier-tail decay tends to zero along the radii `n + 1`.
The proof is Archimedean and uses the reciprocal comparison above. -/
theorem h1HighFrequencyDecay_natSucc_tendsto_zero :
    Tendsto (fun n : ℕ ↦ h1HighFrequencyDecay ((n : ℝ) + 1))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ε⁻¹
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (h1HighFrequencyDecay_nonneg ((n : ℝ) + 1))]
  have hinv_lt_radius : ε⁻¹ < (n : ℝ) + 1 := by
    calc
      ε⁻¹ < (N : ℝ) := hN
      _ ≤ (n : ℝ) := by exact_mod_cast hn
      _ < (n : ℝ) + 1 := by linarith
  exact (h1HighFrequencyDecay_natSucc_le_inv n).trans_lt
    ((inv_lt_comm₀ (by positivity : 0 < (n : ℝ) + 1) hε).2
      hinv_lt_radius)

/-! ## Low-frequency sequence and exact decomposition -/

/-- The band-limited `H¹ → L²` map, sampled at the positive natural
radii `n + 1`. -/
def wholePlaneH1LowFrequencyNat
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (n : ℕ) :
    WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  wholePlaneH1LowFrequency F ((n : ℝ) + 1)

/-! ## Operator-norm convergence -/

/-- Quantitative operator-norm error bound for the low-frequency
approximation. -/
theorem norm_wholePlaneH1LowFrequencyNat_sub_embedding_le
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (n : ℕ) :
    ‖wholePlaneH1LowFrequencyNat F n -
        wholePlaneH1Embedding F‖ ≤
      h1HighFrequencyDecay ((n : ℝ) + 1) *
        ‖wholePlaneH1CoeffRecovery F‖ := by
  exact norm_wholePlaneH1LowFrequency_sub_embedding_le F (by positivity)

/-- Explicit epsilon form of operator-norm convergence, matching the hypothesis of
`isCompactOperator_wholePlaneScalarRestrictionH1_of_compact_approximation`. -/
theorem wholePlaneH1LowFrequencyNat_norm_convergence
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    ∀ ε > 0, ∃ N, ∀ n ≥ N,
      ‖wholePlaneH1LowFrequencyNat F n -
        wholePlaneH1Embedding F‖ < ε := by
  intro ε hε
  have hupper :
      Tendsto
        (fun n : ℕ ↦ h1HighFrequencyDecay ((n : ℝ) + 1) *
          ‖wholePlaneH1CoeffRecovery F‖) atTop (nhds 0) := by
    simpa using h1HighFrequencyDecay_natSucc_tendsto_zero.mul_const
      ‖wholePlaneH1CoeffRecovery F‖
  rw [Metric.tendsto_atTop] at hupper
  obtain ⟨N, hN⟩ := hupper ε hε
  refine ⟨N, fun n hn ↦
    (norm_wholePlaneH1LowFrequencyNat_sub_embedding_le F n).trans_lt ?_⟩
  have hdist := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg
      (h1HighFrequencyDecay_nonneg ((n : ℝ) + 1))
      (norm_nonneg (wholePlaneH1CoeffRecovery F)))] at hdist
  exact hdist

end

end FastDynamo

/-!
## Local Rellich from concrete band-limited cores

This part assembles the explicit natural-radius low-frequency approximation
above with the abstract norm-limit criterion for compact operators.

The one analytic premise is stated exactly for the concrete
coefficient-level time--frequency concentration maps
`wholePlaneBandLimitedRestrictionFromCoeff` (it is proved in
`WholePlaneBandLimitedRellichUnconditional`).  No separate predicate or
certificate renames local Rellich compactness.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- If every positive-natural-radius coefficient-level time--frequency
concentration map is compact, then restriction of scalar whole-plane `H¹` to
the measurable finite-measure set `s` is compact. -/
theorem
    isCompactOperator_wholePlaneScalarRestrictionH1_of_bandLimited_cores
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ ∞)
    (hcore : ∀ n : ℕ, IsCompactOperator
      (wholePlaneBandLimitedRestrictionFromCoeff s hs hsm
        ((n : ℝ) + 1))) :
    IsCompactOperator (wholePlaneScalarRestrictionH1 s hs hsm) := by
  apply
    isCompactOperator_wholePlaneScalarRestrictionH1_of_compact_approximation
      s hs hsm (wholePlaneH1LowFrequencyNat ℂ)
  · intro n
    simpa only [wholePlaneH1LowFrequencyNat] using
      isCompactOperator_wholePlaneScalarCutoff_comp_h1LowFrequency_of_core
        s hs hsm ((n : ℝ) + 1) (hcore n)
  · exact wholePlaneH1LowFrequencyNat_norm_convergence ℂ

end

end FastDynamo

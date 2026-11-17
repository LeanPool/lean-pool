/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.CompactDomain
public import LeanPool.KLS.FunctionalInequalities.KLS.IsotropicSupport
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.Generator
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt
public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.InverseSqrt
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.JointRegularity
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Probability.IntrinsicTranslation
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.CauchySchwarz
public import LeanPool.KLS.FunctionalInequalities.Probability.CoordinateThirdMoment
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Covariance algebra and radius bounds for compact posteriors
-/

@[expose] public section

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- For a compactly supported isotropic prior every posterior has strictly positive covariance. -/
theorem Isotropic.compactPosterior_covariance_pos (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ :=
  compactPosterior_covariance_pos_of_affineSupport_eq_top μ hc (hiso.affineSupport_eq_top) c Q hv

/-- The posterior covariance is a unit. -/
theorem Isotropic.compactPosterior_covariance_isUnit (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    IsUnit (Covariance.operator (compactPosterior μ hc c Q : Measure E)) :=
  Analysis.isUnit_of_inner_self_pos _
    (fun _ hv => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv)

/-- The posterior covariance has a two-sided inverse. -/
theorem Isotropic.compactPosterior_exists_covariance_inverse (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ B : E →L[ℝ] E,
      (Covariance.operator (compactPosterior μ hc c Q : Measure E)).comp B =
          ContinuousLinearMap.id ℝ E ∧
        B.comp (Covariance.operator (compactPosterior μ hc c Q : Measure E)) =
          ContinuousLinearMap.id ℝ E :=
  Analysis.exists_inverse_of_inner_self_pos _
    (fun _ hv => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv)

/--
The posterior covariance has a self-adjoint, strictly positive two-sided inverse (the symmetric
positive rate `M = Cov⁻¹` of the source; no square root is taken). -/
theorem Isotropic.compactPosterior_exists_positive_symmetric_inverse (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ B : E →L[ℝ] E,
      IsSelfAdjoint B ∧
        (∀ v : E, v ≠ 0 → 0 < ⟪B v, v⟫) ∧
          (Covariance.operator (compactPosterior μ hc c Q : Measure E)).comp B =
              ContinuousLinearMap.id ℝ E ∧
            B.comp (Covariance.operator (compactPosterior μ hc c Q : Measure E)) =
              ContinuousLinearMap.id ℝ E := by
  obtain ⟨B, hAB, hBA⟩ := Isotropic.compactPosterior_exists_covariance_inverse μ hc hiso c Q
  refine
    ⟨B, Analysis.isSelfAdjoint_of_comp_eq_id _ _ (Covariance.operator_isSelfAdjoint _) hAB,
      fun _ hv => Analysis.inner_self_pos_of_comp_eq_id _ _ ?_ hAB hv, hAB, hBA⟩
  exact fun _ hw => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hw

/--
The canonical inverse `Ring.inverse (Cov μ_{c,Q})` is a two-sided, self-adjoint, strictly positive
inverse. -/
theorem Isotropic.compactPosterior_ringInverse_covariance (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    A.comp (Ring.inverse A) = ContinuousLinearMap.id ℝ E ∧
      (Ring.inverse A).comp A = ContinuousLinearMap.id ℝ E ∧
        IsSelfAdjoint (Ring.inverse A) ∧ (∀ v : E, v ≠ 0 → 0 < ⟪Ring.inverse A v, v⟫) := by
  dsimp only
  let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
  have hu : IsUnit A := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  have hright : A.comp (Ring.inverse A) = ContinuousLinearMap.id ℝ E :=
    Ring.mul_inverse_cancel A hu
  have hleft : (Ring.inverse A).comp A = ContinuousLinearMap.id ℝ E :=
    Ring.inverse_mul_cancel A hu
  exact
    ⟨hright, hleft,
      Analysis.isSelfAdjoint_of_comp_eq_id A _ (Covariance.operator_isSelfAdjoint _) hright,
      fun v hv =>
      Analysis.inner_self_pos_of_comp_eq_id A _
        (fun w hw => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hw) hright hv⟩

/--
**The BKL posterior of a log-concave compact prior is log-concave for `Q ≥ 0`** (p. 19: "each `μ_t`
is
log-concave since `Q_t ≥ 0`"); singular priors, `Q = 0`, any `c` and rank zero included. -/
theorem compactPosterior_logConcave (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hLC : KLS.LogConcave μ) (c : E) (Q : E →L[ℝ] E)
    (hSym : IsSelfAdjoint Q) (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) :
    KLS.LogConcave (compactPosterior μ hc c Q) := by
  apply
    LogConcave.logConcave_of_concave_tilt μ (compactPosterior μ hc c Q) hLC
      (quadraticExponent c Q) (by unfold quadraticExponent; fun_prop)
  · exact
      Probability.Posterior.quadraticExponent_concave c Q
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSym) hQ
  · rfl

/-- The posterior covariance is a positive operator. -/
theorem Isotropic.compactPosterior_covariance_isPositive (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    (Covariance.operator (compactPosterior μ hc c Q : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv).le

/--
**The diffusion coefficient `A^{-1/2}` of (67)**: for a compactly supported isotropic prior and
every finite
`(c, Q)` (including `0`, negative `Q`, rank zero), `σ = inverseSqrt (Cov μ_{c,Q})` is self-adjoint,
positive,
strictly positive, `σ² = σσ* = Cov⁻¹` and `Cov σσ* = σσ* Cov = 1`. Coefficient algebra only; no
regularity,
SDE, Itô or martingale statement. -/
theorem Isotropic.compactPosterior_inverseSqrt_spec (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    let σ := inverseSqrt A
    IsSelfAdjoint σ ∧
      σ.IsPositive ∧
        (∀ v : E, v ≠ 0 → 0 < ⟪σ v, v⟫) ∧
          σ * σ = Ring.inverse A ∧
            σ * σ.adjoint = Ring.inverse A ∧
              A * (σ * σ.adjoint) = 1 ∧ (σ * σ.adjoint) * A = 1 := by
  dsimp only
  let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
  have hp := Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hu := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  obtain ⟨hpos, hsa, hsquare, hgram, hl, hr⟩ := inverseSqrt_spec A hp hu
  exact
    ⟨hsa, hpos, fun _ hv => inverseSqrtIn_inner_self_pos _ A hp hu hv, hsquare, hgram, hl, hr⟩

/-- At the initial pair `c = Q = 0` the diffusion coefficient is `Id`. -/
theorem Isotropic.inverseSqrt_covariance_compactPosterior_zero
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    inverseSqrt (Covariance.operator (compactPosterior μ hc 0 0 : Measure E)) =
      ContinuousLinearMap.id ℝ E := by
  rw [compactPosterior_zero, hiso.covariance_identity]
  change inverseSqrt (1 : E →L[ℝ] E) = 1
  apply inverseSqrt_unique _ _ isUnit_one
  · exact ContinuousLinearMap.isPositive_one
  · simp

variable {ι : Type*} [Fintype ι]

/--
**Generator cancellation at the source rate** `M = Cov(μ_{c,Q})⁻¹` (BKL (67)–(68), deterministic
part): for a
compactly supported isotropic prior, every finite `(c, Q)` and measurable `f` bounded on the
support,
`D_c[M a] + ∂_Q[M] + ½ Σ_i D²_c[M e_i, e_i] = 0`; the symmetry of the literal `Ring.inverse` of the
constructed
posterior covariance comes from the covariance domain. Not an inverse-square-root, SDE, Itô or
martingale
statement. -/
theorem Isotropic.compactPosterior_generator_cancellation (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) {f : E → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    let M := Ring.inverse A
    fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (M (posteriorMean μ c Q)) +
          deriv (fun t : ℝ => posteriorExpectation μ c (Q + t • M) f) 0 +
        (1 / 2 : ℝ) *
          (∑ i,
            bilinearIteratedFDerivTwo ℝ (fun y => posteriorExpectation μ y Q f) c (M (b i))
              (b i)) =
      0 := by
  dsimp only
  have hsa := (Isotropic.compactPosterior_ringInverse_covariance μ hc hiso c Q).2.2.1
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  apply posteriorExpectation_generator_cancellation μ hc hf hC hfb c Q _ b
  intro u v
  exact hs u v

/--
At the initial parameters `c = Q = 0` the posterior is the isotropic prior, so the rate is `Id`;
this
describes the initial pair only. -/
theorem Isotropic.ringInverse_covariance_compactPosterior_zero (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    Ring.inverse (Covariance.operator (compactPosterior μ hc 0 0 : Measure E)) =
      ContinuousLinearMap.id ℝ E := by
  rw [compactPosterior_zero, hiso.covariance_identity]
  exact Ring.inverse_one (E →L[ℝ] E)
section CovarianceRadius

open ProbabilityTheory

/--
**Posterior covariance radius bound**: if the prior support lies in the closed ball of radius `r`,
then
`‖Cov μ_{c,Q}‖ ≤ r²` for every finite `(c, Q)`. Route: `⟪A v, w⟫ = cov(⟪v,·⟫, ⟪w,·⟫)`,
Cauchy–Schwarz,
`Var⟪v,·⟫ ≤ ∫ ⟪v,x⟫² ≤ r² ‖v‖²` on the support, then `‖A v‖² = ⟪A v, A v⟫ ≤ r² ‖v‖ ‖A v‖`. -/
theorem opNorm_covariance_compactPosterior_le_sq_radius (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure E).support ⊆ Metric.closedBall (0 : E) r) (c : E) (Q : E →L[ℝ] E) :
    ‖Covariance.operator (compactPosterior μ hc c Q : Measure E)‖ ≤ r ^ 2 := by
  let ν : Measure E := compactPosterior μ hc c Q
  let A : E →L[ℝ] E := Covariance.operator ν
  have hprob : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  change ‖A‖ ≤ r ^ 2
  have hid : MemLp id 2 ν := by simpa only [ν] using compactPosterior_memLp_id_two μ hc c Q
  have hmem (v : E) : MemLp (fun x : E => ⟪v, x⟫) 2 ν := by
    have hh : MemLp (fun x : E => ⟪id x, v⟫) 2 ν := hid.inner_const v
    simpa [real_inner_comm] using hh
  have hvar (v : E) : variance (fun x : E => ⟪v, x⟫) ν ≤ r ^ 2 * ‖v‖ ^ 2 := by
    have hle : (∫ x, (⟪v, x⟫) ^ 2 ∂ν) ≤ ∫ _x, r ^ 2 * ‖v‖ ^ 2 ∂ν := by
      apply integral_mono_ae
      · exact (hmem v).integrable_sq
      · exact integrable_const _
      · filter_upwards [Measure.support_mem_ae (μ := ν)] with x hx
        have hx' : x ∈ (μ : Measure E).support := by
          rw [← compactPosterior_support μ hc c Q]
          exact hx
        have hxball : x ∈ Metric.closedBall (0 : E) r := hsupp hx'
        have hnorm : ‖x‖ ≤ r := by simpa [mem_closedBall_zero_iff] using hxball
        have habs : |⟪v, x⟫| ≤ r * ‖v‖ := by
          calc
            |⟪v, x⟫| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
            _ ≤ ‖v‖ * r := mul_le_mul_of_nonneg_left hnorm (norm_nonneg v)
            _ = r * ‖v‖ := by ring
        have hsquare : ⟪v, x⟫ ^ 2 ≤ (r * ‖v‖) ^ 2 := by
          rw [← sq_abs]
          nlinarith [habs, abs_nonneg ⟪v, x⟫, mul_self_nonneg (r * ‖v‖ - |⟪v, x⟫|)]
        calc
          ⟪v, x⟫ ^ 2 ≤ (r * ‖v‖) ^ 2 := hsquare
          _ = r ^ 2 * ‖v‖ ^ 2 := by ring
    have hv :=
      variance_le_expectation_sq (μ := ν) (X := fun x : E => ⟪v, x⟫)
        (hmem v).aestronglyMeasurable
    have hv' : variance (fun x : E => ⟪v, x⟫) ν ≤ ∫ x, (⟪v, x⟫) ^ 2 ∂ν := by
      simpa only [Pi.pow_apply] using hv
    calc
      variance (fun x : E => ⟪v, x⟫) ν ≤ ∫ x, (⟪v, x⟫) ^ 2 ∂ν := hv'
      _ ≤ ∫ _x, r ^ 2 * ‖v‖ ^ 2 ∂ν := hle
      _ = r ^ 2 * ‖v‖ ^ 2 := by simp
  have hcov (v w : E) : |⟪A v, w⟫| ≤ r ^ 2 * ‖v‖ * ‖w‖ := by
    have hcs := Probability.covariance_sq_le_variance_mul_variance (hmem v) (hmem w)
    have hsq : |⟪A v, w⟫| ^ 2 ≤ (r ^ 2 * ‖v‖ * ‖w‖) ^ 2 := by
      rw [Covariance.operator_inner]
      rw [covarianceBilin_apply_eq_cov (compactPosterior_memLp_id_two μ hc c Q)]
      calc
        |covariance (fun x : E => ⟪v, x⟫) (fun x : E => ⟪w, x⟫) ν| ^ 2 =
            covariance (fun x : E => ⟪v, x⟫) (fun x : E => ⟪w, x⟫) ν ^ 2 := by
          rw [sq_abs]
        _ ≤ variance (fun x : E => ⟪v, x⟫) ν * variance (fun x : E => ⟪w, x⟫) ν := hcs
        _ ≤ (r ^ 2 * ‖v‖ ^ 2) * (r ^ 2 * ‖w‖ ^ 2) := by
          exact mul_le_mul (hvar v) (hvar w) (variance_nonneg _ _) (by positivity)
        _ = (r ^ 2 * ‖v‖ * ‖w‖) ^ 2 := by ring
    have hnonneg : 0 ≤ r ^ 2 * ‖v‖ * ‖w‖ := by positivity
    by_contra h
    have hlt : r ^ 2 * ‖v‖ * ‖w‖ < |⟪A v, w⟫| := lt_of_not_ge h
    nlinarith [hsq, abs_nonneg ⟪A v, w⟫]
  apply ContinuousLinearMap.opNorm_le_bound A
  · exact pow_nonneg hr 2
  · intro v
    have hsq : ‖A v‖ ^ 2 ≤ r ^ 2 * ‖v‖ * ‖A v‖ := by
      calc
        ‖A v‖ ^ 2 = ⟪A v, A v⟫ := by
          symm
          exact real_inner_self_eq_norm_sq _
        _ ≤ |⟪A v, A v⟫| := le_abs_self _
        _ ≤ r ^ 2 * ‖v‖ * ‖A v‖ := hcov v (A v)
    by_cases hz : ‖A v‖ = 0
    · simp only [hz, ge_iff_le]
      positivity
    · have hpos : 0 < ‖A v‖ :=
        norm_pos_iff.mpr
          (by
            intro hav
            apply hz
            simp [hav])
      nlinarith

end CovarianceRadius

end FunctionalInequalities.KLS

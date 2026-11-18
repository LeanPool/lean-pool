/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.CompactQuadratic
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Positivity
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport

/-!
# The BKL posterior of a compactly supported prior as a probability law

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (67): the posterior `μ_{c,Q} = μ e^{⟪c,x⟫ − ½⟪Qx,x⟫}/Z` of
a
compactly supported prior, for every finite parameter pair (including the initial pair and negative
`Q`),
as a probability law with the null sets, a.e. filter, support and affine support of the prior,
finite
second moment, and, when the prior has full affine support, strictly positive covariance. The
isotropic
source adapter (unit covariance with a self-adjoint positive canonical inverse) is in
`KLS/BKL/Posterior/Covariance.lean`. No square root, transported-law whitening, stochastic
equation or
coefficient
regularity is provided.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Posterior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
The BKL posterior `μ.tilted (⟪c,·⟫ − ½⟪Q·,·⟫)` of a compactly supported prior, as a probability law
(every finite `(c, Q)`, including `0` and negative `Q`). -/
def compactPosterior (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (c : E)
    (Q : E →L[ℝ] E) : ProbabilityMeasure E :=
  ⟨(μ : Measure E).tilted (quadraticExponent c Q),
    isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q⟩

/-- The posterior has the same null sets as the prior. -/
theorem compactPosterior_null_iff (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (s : Set E) :
    (compactPosterior μ hc c Q : Measure E) s = 0 ↔ (μ : Measure E) s = 0 := by
  exact
    Probability.tilted_null_iff _
      (integrable_exp_of_compact μ hc (by unfold quadraticExponent; fun_prop)) s

/-- The posterior has the same a.e. filter as the prior. -/
theorem compactPosterior_ae (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (c : E) (Q : E →L[ℝ] E) : ae (compactPosterior μ hc c Q : Measure E) = ae (μ : Measure E) := by
  exact
    Probability.ae_tilted_eq _
      (integrable_exp_of_compact μ hc (by unfold quadraticExponent; fun_prop))

/-- The posterior has the same support as the prior. -/
theorem compactPosterior_support (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    (compactPosterior μ hc c Q : Measure E).support = (μ : Measure E).support := by
  exact
    Probability.support_tilted_eq _
      (integrable_exp_of_compact μ hc (by unfold quadraticExponent; fun_prop))

/-- The posterior has the same affine support as the prior. -/
theorem compactPosterior_affineSupport (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    Probability.affineSupport (compactPosterior μ hc c Q) = Probability.affineSupport μ := by
  unfold Probability.affineSupport
  rw [compactPosterior_support]

/-- The posterior has finite second moment. -/
theorem compactPosterior_memLp_id_two (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    MemLp id 2 (compactPosterior μ hc c Q : Measure E) := by
  change MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q))
  have hn : MemLp (fun x : E => ‖x‖) 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    memLp_two_tilted_quadraticExponent_of_compact μ hc c Q continuous_norm
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn

/-- At the initial parameters the posterior is the prior. -/
theorem compactPosterior_zero (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) : compactPosterior μ hc 0 0 = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change (μ : Measure E).tilted (quadraticExponent (0 : E) 0) = _
  have he : quadraticExponent (0 : E) (0 : E →L[ℝ] E) = 0 := by funext x; simp [quadraticExponent]
  rw [he, tilted_zero]

/-- For a prior with full affine support every posterior has strictly positive covariance. -/
theorem compactPosterior_covariance_pos_of_affineSupport_eq_top (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hfull : Probability.affineSupport μ = ⊤)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ := by
  apply Covariance.inner_operator_self_pos_of_affineSupport_eq_top (compactPosterior μ hc c Q)
    (compactPosterior_memLp_id_two μ hc c Q) ?_ hv
  rw [compactPosterior_affineSupport, hfull]

/--
The posterior of a compactly supported prior is a.e. supported in a closed ball around any point. -/
theorem compactPosterior_exists_ae_norm_sub_le {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (c : EuclideanSpace ℝ (Fin n)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)) :
    ∃ R : ℝ,
      ∀ᵐ x ∂(compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))), ‖x - a‖ ≤ R := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall a
  refine ⟨R, ?_⟩
  filter_upwards [Measure.support_mem_ae (μ :=
      (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))] with
    x hx
  rw [compactPosterior_support μ hc c Q] at hx
  have h := hR hx
  rwa [Metric.mem_closedBall, dist_eq_norm] at h

end FunctionalInequalities.Probability.Posterior

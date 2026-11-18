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
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Posterior.Covariance

/-!
# Joint regularity of compact-posterior localization coefficients
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
section JointCoefficients

/--
**Joint smoothness of the rate** `A⁻¹ = Cov(μ_{c,Q})⁻¹` of (67): isotropy makes the posterior
covariance a
unit at every finite `(c, Q)`, and the Banach-algebra inverse is analytic there. -/
theorem Isotropic.contDiff_ringInverse_covariance_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    ContDiff ℝ ∞
      (fun p : E × (E →L[ℝ] E) =>
        Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hs := (contDiff_posteriorCovariance_joint μ hc).contDiffAt (x := p)
  obtain ⟨u, hu⟩ := Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hi :
    ContDiffAt ℝ ∞ Ring.inverse
      (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact hi.comp p hs

/-- **Joint smoothness of the drift** `A⁻¹ a` of (67). -/
theorem Isotropic.contDiff_covarianceDrift_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
        (posteriorMean μ p.1 p.2)) :=
  (Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).clm_apply
    (contDiff_posteriorMean_joint μ hc)

/--
**Local Lipschitz property of the diffusion coefficient** `A^{-1/2} = inverseSqrt (Cov μ_{c,Q})` of
(67)
on the whole parameter space (operator norm); positivity, invertibility and `C¹` of the inverse are
derived
from compactness and isotropy. -/
theorem Isotropic.locallyLipschitz_inverseSqrt_covariance_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    LocallyLipschitz
      (fun p : E × (E →L[ℝ] E) =>
        inverseSqrt (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))) := by
  apply locallyLipschitz_inverseSqrt_of_contDiff_ringInverse
  · intro p
    have hs := Isotropic.compactPosterior_ringInverse_covariance μ hc hiso p.1 p.2
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨hs.2.2.1, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst v
      change
        0 ≤
          ⟪Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
              (0 : E),
            (0 : E)⟫
      simp
    · exact (hs.2.2.2 v hv).le
  · intro p
    exact Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  · exact (Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).of_le (by simp)

/--
**Coefficient regularity of (67)** (BKL p. 19): the coefficient map `(c, Q) ↦ (A^{-1/2}, A⁻¹ a,
A⁻¹)` of the
localization equations, built from `compactPosterior`, is locally Lipschitz on all of `E × (E →L[ℝ]
E)` for a
compactly supported isotropic prior (all finite `(c, Q)`, including `Q = 0`, non-symmetric `Q` and
dimension
zero). Deterministic: no process, strong solution or non-explosion statement. -/
theorem Isotropic.locallyLipschitz_coefficients67 (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    LocallyLipschitz
      (fun p : E × (E →L[ℝ] E) =>
        (inverseSqrt (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)),
          (Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
              (posteriorMean μ p.1 p.2),
            Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))))) :=
  (Isotropic.locallyLipschitz_inverseSqrt_covariance_joint μ hc hiso).prodMk
    (((Isotropic.contDiff_covarianceDrift_joint μ hc hiso).of_le
          (by simp)).locallyLipschitz.prodMk
      ((Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).of_le
          (by simp)).locallyLipschitz)

end JointCoefficients

end FunctionalInequalities.KLS

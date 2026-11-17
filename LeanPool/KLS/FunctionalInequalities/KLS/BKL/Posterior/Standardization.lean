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
# Canonical covariance standardization of compact posteriors
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
section CanonicalStandardisation

/--
**Canonical standardisation of the posterior**: the principal inverse square root of the posterior
covariance,
as a continuous linear equivalence `W`, transports the centred posterior to an isotropic law. -/
theorem Isotropic.exists_inverseSqrt_equiv_isotropic_standardized (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ W : E ≃L[ℝ] E,
      (W : E →L[ℝ] E) =
          inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)) ∧
        KLS.Isotropic
          (Probability.mapContinuousLinearEquiv
            (Probability.translateLaw (compactPosterior μ hc c Q) (-posteriorMean μ c Q)) W) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let ν : ProbabilityMeasure E := compactPosterior μ hc c Q
  let A : E →L[ℝ] E := Covariance.operator (ν : Measure E)
  let σ : E →L[ℝ] E := inverseSqrt A
  have hpos := Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hunit := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  have hσ : IsUnit σ := by
    change IsUnit (inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
    exact inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
  let W : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hσ.unit
  have hW : (W : E →L[ℝ] E) = σ := by
    change (↑hσ.unit : E →L[ℝ] E) = σ
    exact hσ.unit_spec
  have hνlp : MemLp id 2 (ν : Measure E) := by
    simpa [ν] using compactPosterior_memLp_id_two μ hc c Q
  have hint : Integrable id (ν : Measure E) := hνlp.integrable (by norm_num)
  have ht : MemLp id 2 (Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E) :=
    Probability.memLp_id_two_translateLaw ν _ hνlp
  let η : ProbabilityMeasure E :=
    Probability.mapContinuousLinearEquiv (Probability.translateLaw ν (-posteriorMean μ c Q)) W
  have hηcoe :
    (η : Measure E) = ((Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E).map W) := by
    change
      (Probability.mapContinuousLinearEquiv (Probability.translateLaw ν (-posteriorMean μ c Q))
            W :
          Measure E) =
        ((Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E).map W)
    rfl
  have hηlp : MemLp id 2 (η : Measure E) := by
    rw [hηcoe, memLp_map_measure_iff measurable_id.aestronglyMeasurable]
    · simpa [Function.comp_def] using (W : E →L[ℝ] E).comp_memLp' ht
    · exact W.continuous.aemeasurable
  have hzero : ∫ x, x ∂(Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E) = 0 := by
    have hzero' :
      ∫ x, x ∂(Probability.translateLaw ν (-(∫ y, y ∂(ν : Measure E))) : Measure E) = 0 :=
      Probability.integral_id_translateLaw_neg_integral ν hint
    exact hzero'
  have hmean : ∫ x, x ∂(η : Measure E) = 0 := by
    rw [hηcoe]
    change
      ∫ x, id x ∂((Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E).map W) = 0
    rw [integral_map W.continuous.aemeasurable hηlp.aestronglyMeasurable]
    simp only [id_eq]
    rw [W.integral_comp_comm]
    simpa using congrArg W hzero
  have hself : (σ.adjoint : E →L[ℝ] E) = σ := by
    change ContinuousLinearMap.adjoint (inverseSqrt A) = inverseSqrt A
    exact (inverseSqrt_spec A hpos hunit).2.1
  have halg : (σ.comp A).comp σ = 1 := by
    ext x
    simpa [σ, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T x) (inverseSqrt_mul_mul_inverseSqrt A hpos hunit)
  refine ⟨W, ?_, ?_⟩
  · simpa [A, σ, ν] using hW
  · refine
      { memLp_two := hηlp
        mean_zero := hmean
        covariance_identity := ?_ }
    rw [hηcoe]
    rw [Covariance.operator_map_continuousLinearEquiv]
    rw [Covariance.operator_translateLaw]
    rw [hW, hself]
    exact halg

end CanonicalStandardisation

end FunctionalInequalities.KLS

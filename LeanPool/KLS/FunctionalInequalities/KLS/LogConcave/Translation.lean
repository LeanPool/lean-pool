/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Covariance
public import LeanPool.KLS.FunctionalInequalities.Poincare.CovarianceGradient.Translation

/-!
# Log-concave laws under ambient translation

Source: Blueprint `lem:affine-poincare-translation-invariance`, the sentences "`(τ_b)_# μ` is
log-concave" and "translating by the negative barycenter produces a centered law". Read
`LogConcave.translateLaw`, `LogConcave.memLp_id_two`, `LogConcave.integrable_id` and
`LogConcave.integral_id_translateLaw_neg_integral`.

For a compact-set log-concave law `μ` on a finite-dimensional Euclidean space `E` and `b ∈ E`, the
translated law `Probability.translateLaw μ b` is log-concave: the inverse translation is an
affine isometry carrying the translated law back to `μ`, and images of compact sets are the exact
test sets. The ambient law has a finite second moment, because the intrinsic law has one and
reconstruction is an affine isometry; hence its barycenter exists and translating by the negative
barycenter gives a law with zero mean. The affine covariance Poincaré constant itself is
translation invariant for every Borel law, see
`Poincare.CovarianceGradient.Intrinsic.constant_translateLaw`;
log-concavity is not needed for that identity.

What this module does not claim: any Poincaré inequality, finiteness of the constant, the
isotropic reduction, or KLS. The zero-dimensional direction space is included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.KLS.LogConcave

open Energy.Euclidean Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E}


omit [CompleteSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- Translating a log-concave law in the ambient space keeps it log-concave. -/
theorem translateLaw (hμ : LogConcave μ) (b : E) :
    LogConcave (Probability.translateLaw μ b) := by
  refine hμ.of_affineIsometry_map (Probability.translateLaw μ b)
    (AffineIsometryEquiv.constVAdd ℝ E (-b)).toAffineIsometry ?_
  have hf : ⇑(AffineIsometryEquiv.constVAdd ℝ E (-b)).toAffineIsometry = fun x ↦ -b + x := by
    funext x
    rfl
  rw [hf]
  exact (Probability.measurePreserving_translate_symm μ b).map_eq

section TranslatedMoments

omit [CompleteSpace E]
/-- A log-concave law has a finite ambient second moment: the intrinsic law has one and
reconstruction is an affine isometry. -/
theorem memLp_id_two (hμ : LogConcave μ) : MemLp id 2 (μ : Measure E) := by
  have hν := hμ.intrinsic_memLp_id_two
  have h1 : MemLp (fun v ↦ reconstruct μ v) 2
      (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction) := by
    refine MemLp.of_le ((memLp_const ‖reconstruct μ 0‖).add hν.norm)
      (continuous_reconstruct μ).aestronglyMeasurable (Eventually.of_forall fun v ↦ ?_)
    change ‖reconstruct μ v‖ ≤ ‖‖reconstruct μ 0‖ + ‖v‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc ‖reconstruct μ v‖ = ‖(reconstruct μ v - reconstruct μ 0) + reconstruct μ 0‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖reconstruct μ v - reconstruct μ 0‖ + ‖reconstruct μ 0‖ := norm_add_le _ _
      _ = ‖v‖ + ‖reconstruct μ 0‖ := by
          rw [← dist_eq_norm, (reconstruct μ).dist_map, dist_zero_right]
      _ = ‖reconstruct μ 0‖ + ‖v‖ := add_comm _ _
  have h2 : MemLp (fun x ↦ reconstruct μ (intrinsicMap μ x)) 2 (μ : Measure E) := by
    rw [← (measurePreserving_intrinsicMap μ).map_eq] at h1
    exact (memLp_map_measure_iff (continuous_reconstruct μ).aestronglyMeasurable
      (measurable_intrinsicMap μ).aemeasurable).mp h1
  exact h2.ae_eq (reconstruct_intrinsicMap_ae μ)

/-- The identity is integrable against a log-concave law, so the barycenter exists. -/
theorem integrable_id (hμ : LogConcave μ) : Integrable id (μ : Measure E) :=
  hμ.memLp_id_two.integrable (by norm_num)

end TranslatedMoments

/-- Translating a log-concave law by the negative barycenter gives a centered law. -/
theorem integral_id_translateLaw_neg_integral (hμ : LogConcave μ) :
    ∫ x, x ∂(Probability.translateLaw μ (-∫ x, x ∂(μ : Measure E)) : Measure E) = 0 :=
  Probability.integral_id_translateLaw_neg_integral μ hμ.integrable_id

end FunctionalInequalities.KLS.LogConcave

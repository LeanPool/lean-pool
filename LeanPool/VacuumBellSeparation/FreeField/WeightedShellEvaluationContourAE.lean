/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.AveragedWedgeContourAE
public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationContourNorm

/-!
# The extended contour bound under actual almost-everywhere geometry

The compactly supported parameter probability need not satisfy the
containing-wedge estimate outside its support. Inner Bochner integrals
are therefore converted to nonnegative integrals only almost everywhere.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem averaged_complexTestContour_lintegral_le_sourceWeight_ae
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν]
    {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ a, IsLorentzMap (Λ a)) (hfuture : ∀ a, IsOrthochronousMap (Λ a))
    (hcont : ∀ x : Spacetime, Continuous fun a => Λ a x)
    (hbound : ∀ᵐ a ∂ν, Real.sqrt 2 * spacetimeEuclideanOperatorNorm (Λ a).symm < ℓ)
    {U : Set (EuclideanSpace ℝ (Fin 3))} {T : ℝ} (hT : 0 < T)
    (hU : U ⊆ Metric.ball 0 T) (u v : SourceTestSpace hm U)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∫⁻ a, ∫⁻ p, ENNReal.ofReal
      (complexTestContourIntegrand m (ℓ * T) (2 * Real.pi * c) (Λ a) u.1 v.1 p)
        ∂oneParticleMeasure m ∂ν) ≤
      ENNReal.ofReal (‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
          Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))‖ ^ 2) := by
  obtain ⟨hi, hb⟩ := averaged_complexTestContour_le_sourceWeight_ae ν hm ℓ Λ hΛ hfuture
    hcont hbound hT hU u v hc hc2
  have hnonneg (a : A) : 0 ≤ ∫ p,
      complexTestContourIntegrand m (ℓ * T) (2 * Real.pi * c) (Λ a) u.1 v.1 p
        ∂oneParticleMeasure m :=
    integral_nonneg (complexTestContourIntegrand_nonneg _ _ _ _ _ _)
  have h := ENNReal.ofReal_le_ofReal hb
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg)] at h
  convert h using 1
  apply lintegral_congr_ae
  filter_upwards [hbound] with a ha
  have hin := integrable_complexTestContour hm (ℓ * T) (Λ a) (hΛ a) (hfuture a)
    hT hU (doubleCone_subset_transformed_leftWedge (Λ a) hT ha) u v hc.le hc2
  exact (ofReal_integral_eq_lintegral_ofReal hin
    (Filter.Eventually.of_forall
      (complexTestContourIntegrand_nonneg _ _ _ _ _ _))).symm

end VacuumBellSeparation

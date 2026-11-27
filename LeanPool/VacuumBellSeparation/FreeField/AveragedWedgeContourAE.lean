/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.AveragedWedgeContour

/-!
# Probability averaging with almost-everywhere containing geometry

The actual compactly supported parameter density may live on an
unbounded parameter carrier. Only the geometry on its support enters
the average; no pointwise estimate is asserted outside that support.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

theorem averaged_complexTestContour_le_sourceWeight_ae
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
 (ν : Measure A) [IsProbabilityMeasure ν]
    {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ a, IsLorentzMap (Λ a)) (hfuture : ∀ a, IsOrthochronousMap (Λ a))
    (hcont : ∀ x : Spacetime, Continuous fun a => Λ a x)
    (hbound : ∀ᵐ a ∂ν, Real.sqrt 2 * spacetimeEuclideanOperatorNorm (Λ a).symm < ℓ)
    {U : Set (EuclideanSpace ℝ (Fin 3))} {R : ℝ} (hR : 0 < R)
    (hU : U ⊆ Metric.ball 0 R) (u v : SourceTestSpace hm U)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    Integrable (fun a => ∫ p,
      complexTestContourIntegrand m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1 p
      ∂oneParticleMeasure m) ν ∧
    (∫ a, ∫ p, complexTestContourIntegrand m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1 p
      ∂oneParticleMeasure m ∂ν) ≤
      ‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
          Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))‖ ^ 2 := by
  let : SigmaFinite (oneParticleMeasure m) := by
    unfold oneParticleMeasure
    infer_instance
  let B := ‖sourceModularWeight hm U c
    (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
      Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))‖ ^ 2
  let f := fun a => ∫ p,
    complexTestContourIntegrand m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1 p
    ∂oneParticleMeasure m
  have hmeas : StronglyMeasurable f :=
    (continuous_complexTestContourIntegrand Λ hcont m (ℓ * R) (2 * Real.pi * c)
      u.1 v.1).stronglyMeasurable.integral_prod_right'
  have hnonneg (a : A) : 0 ≤ f a := integral_nonneg
    (complexTestContourIntegrand_nonneg m (ℓ * R) (2 * Real.pi * c) (Λ a) u.1 v.1)
  have hle : ∀ᵐ a ∂ν, f a ≤ B := hbound.mono fun a ha =>
    complexTest_lorentzContour_le_sourceWeight hm (ℓ * R) (Λ a) (hΛ a) (hfuture a)
      hR hU (doubleCone_subset_transformed_leftWedge (Λ a) hR ha) u v hc hc2
  have hint : Integrable f ν := (integrable_const B).mono_nonneg hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hnonneg) hle
  refine ⟨hint, ?_⟩
  have h := integral_mono_ae hint (integrable_const B) hle
  simpa only [integral_const, probReal_univ, one_smul] using h


end VacuumBellSeparation

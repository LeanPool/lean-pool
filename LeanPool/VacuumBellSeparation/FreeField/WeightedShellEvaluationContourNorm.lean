/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.AveragedWedgeContour
public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationMassScaling
public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationScaling

/-!
# The actual nonnegative averaged contour bound

The already established Bochner integral estimate is converted only
after its genuine inner and outer integrability has been supplied. The
literal scaled contour and the E² mass-shell factor are then identified.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem complexShellBoost_dilation (t : ℝ) {E : ℝ} (hE : 0 ≤ E)
    (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    complexShellBoost (t * E) ζ (E • p) = (E : ℂ) • complexShellBoost t ζ p := by
  apply Prod.ext
  · simp only [complexShellBoost, dispersion_smul t hE, PiLp.smul_apply,
      Complex.ofReal_mul, Prod.smul_fst, smul_eq_mul]
    ring
  · funext i
    fin_cases i <;> norm_num [complexShellBoost, dispersion_smul t hE,
      PiLp.smul_apply, Complex.ofReal_mul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    ring

/-- Scaled complex test contour integrand. -/
noncomputable def scaledComplexTestContourIntegrand (t E L θ : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (u v : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.exp (-2 * L * E * dispersion t p * Real.sin θ) *
    ‖scaledComplexTestWave E u v (complexifiedSpacetimeMap Λ
      (complexShellBoost t ((θ : ℂ) * Complex.I) p))‖ ^ 2

theorem complexTestContourIntegrand_dilation (t : ℝ) {E : ℝ} (hE : 0 < E)
    (L θ : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) (u v : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) :
    complexTestContourIntegrand (t * E) L θ Λ u v (E • p) =
      scaledComplexTestContourIntegrand t E L θ Λ u v p := by
  unfold complexTestContourIntegrand scaledComplexTestContourIntegrand scaledComplexTestWave
  rw [complexShellBoost_dilation t hE.le, map_smul, dispersion_smul t hE.le]
  congr 2
  ring

theorem averaged_complexTestContour_lintegral_le_sourceWeight
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν]
    {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
    (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ a, IsLorentzMap (Λ a)) (hfuture : ∀ a, IsOrthochronousMap (Λ a))
    (hcont : ∀ x : Spacetime, Continuous fun a => Λ a x)
    (hbound : ∀ a, Real.sqrt 2 * spacetimeEuclideanOperatorNorm (Λ a).symm < ℓ)
    {U : Set (EuclideanSpace ℝ (Fin 3))} {T : ℝ} (hT : 0 < T)
    (hU : U ⊆ Metric.ball 0 T) (u v : SourceTestSpace hm U)
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∫⁻ a, ∫⁻ p, ENNReal.ofReal
      (complexTestContourIntegrand m (ℓ * T) (2 * Real.pi * c) (Λ a) u.1 v.1 p)
        ∂oneParticleMeasure m ∂ν) ≤
      ENNReal.ofReal (‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U) +
          Complex.I • Gaussian.HilbertComplexification.ofReal (v : SourceHilbert hm U))‖ ^ 2) := by
  obtain ⟨hi, hb⟩ := averaged_complexTestContour_le_sourceWeight ν hm ℓ Λ hΛ hfuture
    hcont hbound hT hU u v hc hc2
  have hin (a : A) : Integrable
      (complexTestContourIntegrand m (ℓ * T) (2 * Real.pi * c) (Λ a) u.1 v.1)
      (oneParticleMeasure m) :=
    integrable_complexTestContour hm (ℓ * T) (Λ a) (hΛ a) (hfuture a) hT hU
      (doubleCone_subset_transformed_leftWedge (Λ a) hT (hbound a)) u v hc.le hc2
  have hnonneg (a : A) : 0 ≤ ∫ p,
      complexTestContourIntegrand m (ℓ * T) (2 * Real.pi * c) (Λ a) u.1 v.1 p
        ∂oneParticleMeasure m :=
    integral_nonneg (complexTestContourIntegrand_nonneg _ _ _ _ _ _)
  have h := ENNReal.ofReal_le_ofReal hb
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg)] at h
  convert h using 1
  apply lintegral_congr
  intro a
  exact (ofReal_integral_eq_lintegral_ofReal (hin a)
    (Filter.Eventually.of_forall
      (complexTestContourIntegrand_nonneg _ _ _ _ _ _))).symm

theorem averaged_scaledComplexTestContour_lintegral (t : ℝ) {E : ℝ} (hE : 0 < E)
    {A : Type*} [MeasurableSpace A] (ν : Measure A)
    (Λ : A → Spacetime ≃L[ℝ] Spacetime) (L θ : ℝ) (u v : TimeZeroSource) :
    ENNReal.ofReal (E ^ 2) * (∫⁻ a, ∫⁻ p,
      ENNReal.ofReal (scaledComplexTestContourIntegrand t E L θ (Λ a) u v p)
        ∂oneParticleMeasure t ∂ν) =
      ∫⁻ a, ∫⁻ p, ENNReal.ofReal
        (complexTestContourIntegrand (t * E) L θ (Λ a) u v p)
          ∂oneParticleMeasure (t * E) ∂ν := by
  have h := averaged_lintegral_oneParticle_dilation ν t hE
    (fun a p => ENNReal.ofReal (complexTestContourIntegrand (t * E) L θ (Λ a) u v p))
    (fun a => ENNReal.measurable_ofReal.comp
      ((continuous_complexTestContourIntegrand (fun _ : Unit => Λ a)
        (fun _ => continuous_const) (t * E) L θ u v).comp
          ((continuous_const (y := ())).prodMk continuous_id)).measurable)
  simpa only [complexTestContourIntegrand_dilation t hE] using h

end VacuumBellSeparation

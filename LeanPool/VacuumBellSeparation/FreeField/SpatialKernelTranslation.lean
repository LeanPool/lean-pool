/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialBesselMomentExpansion
public import LeanPool.VacuumBellSeparation.FreeField.SpatialTestTranslation

/-!
# Original translated tests and the displaced covariance kernel
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory
open scoped ComplexConjugate

theorem spatialAxisDisplacement_eq_add (s : ℝ) (δ : EuclideanSpace ℝ (Fin 3)) :
    spatialAxisDisplacement s δ = spatialAxisDisplacement s 0 + δ := by
  ext j
  simp [spatialAxisDisplacement]

theorem spatialAxisDisplacement_zero_apply (s : ℝ) :
    spatialAxisDisplacement s 0 0 = s := by
  simp [spatialAxisDisplacement]

theorem spatialFieldBesselKernel_neg (μ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialFieldBesselKernel μ (-x) = spatialFieldBesselKernel μ x := by
  simp only [spatialFieldBesselKernel, norm_neg]

theorem spatialMomentumBesselKernel_neg (μ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialMomentumBesselKernel μ (-x) = spatialMomentumBesselKernel μ x := by
  simp only [spatialMomentumBesselKernel, norm_neg]

theorem integral_spatialKernel_translate
    (K : EuclideanSpace ℝ (Fin 3) → ℂ) (hK : ∀ w, K (-w) = K w)
    (s : ℝ) (f g : SpatialTestFunction) :
    (∫ xy, K (xy.1 - xy.2) * (f.1 xy.1 : ℂ) *
      ((spatialTestTranslate (spatialAxisDisplacement s 0) g).1 xy.2 : ℂ)
      ∂volume.prod volume) =
    ∫ xy, K (spatialAxisDisplacement s (xy.2 - xy.1)) *
      (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume := by
  rw [← integral_add_right_eq_self (μ := volume.prod volume)
    (fun xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      K (xy.1 - xy.2) * (f.1 xy.1 : ℂ) *
        ((spatialTestTranslate (spatialAxisDisplacement s 0) g).1 xy.2 : ℂ))
    (0, spatialAxisDisplacement s 0)]
  apply integral_congr_ae
  filter_upwards with xy
  simp only [Prod.fst_add, Prod.snd_add, add_zero, spatialTestTranslate, add_sub_cancel_right]
  have harg : xy.1 - (xy.2 + spatialAxisDisplacement s 0) =
      -spatialAxisDisplacement s (xy.2 - xy.1) := by
    rw [spatialAxisDisplacement_eq_add s (xy.2 - xy.1)]
    abel
  rw [harg, hK]

theorem coordinate_support_translated_separation {R s : ℝ}
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    ∀ x y, f.1 x ≠ 0 → (spatialTestTranslate (spatialAxisDisplacement s 0) g).1 y ≠ 0 →
      s - R ≤ ‖x - y‖ := by
  intro x y hx hy
  have hfx := hf x hx 0
  have hgy := hg (y - spatialAxisDisplacement s 0) hy 0
  simp only [PiLp.sub_apply, spatialAxisDisplacement_zero_apply, Real.norm_eq_abs] at hfx hgy
  have hxy := PiLp.norm_apply_le (x - y) (0 : Fin 3)
  simp only [PiLp.sub_apply, Real.norm_eq_abs] at hxy
  have hx' := (abs_le.mp hfx).2
  have hy' := (abs_le.mp hgy).1
  have habs := neg_le_abs (x 0 - y 0)
  linarith

theorem polydisc_separation_positive {R s : ℝ}
    (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s) : 0 < s - R := by
  have h3 : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hmul := mul_le_mul_of_nonneg_right h3 hR.le
  nlinarith

theorem spatialFourier_translated_field_kernel {μ s R : ℝ}
    (hμ : 0 < μ) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    ((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) *
      (∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion μ p)⁻¹ : ℝ) *
        (conj (spatialFourier f p) *
          spatialFourier (spatialTestTranslate (spatialAxisDisplacement s 0) g) p)) =
      ∫ xy, (spatialFieldBesselKernel μ (spatialAxisDisplacement s (xy.2 - xy.1)) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume := by
  rw [spatialFourier_field_covariance_kernel hμ (polydisc_separation_positive hR hsep)
    f (spatialTestTranslate (spatialAxisDisplacement s 0) g)
    (coordinate_support_translated_separation f g hf hg)]
  exact integral_spatialKernel_translate (fun w => (spatialFieldBesselKernel μ w : ℂ))
    (fun w => by rw [spatialFieldBesselKernel_neg]) s f g

theorem spatialFourier_translated_momentum_kernel {μ s R : ℝ}
    (hμ : 0 < μ) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    ((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) *
      (∫ p : EuclideanSpace ℝ (Fin 3), (dispersion μ p : ℂ) *
        (conj (spatialFourier f p) *
          spatialFourier (spatialTestTranslate (spatialAxisDisplacement s 0) g) p)) =
      ∫ xy, (spatialMomentumBesselKernel μ (spatialAxisDisplacement s (xy.2 - xy.1)) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume := by
  rw [spatialFourier_momentum_covariance_kernel hμ (polydisc_separation_positive hR hsep)
    f (spatialTestTranslate (spatialAxisDisplacement s 0) g)
    (coordinate_support_translated_separation f g hf hg)]
  exact integral_spatialKernel_translate (fun w => (spatialMomentumBesselKernel μ w : ℂ))
    (fun w => by rw [spatialMomentumBesselKernel_neg]) s f g

end VacuumBellSeparation

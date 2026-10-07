/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalAE

/-!
# Heat inequality after shifting the initial time

The short-time parabolic change of variables reduces the coefficient in the
weak heat inequality by its spatial scale.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The coefficient in the weak heat inequality gains one factor of the
spatial scale under an affine parabolic change of variables. -/
theorem bu_affine_weak_heat_bound_scaled
    (τ scale c₁ : ℝ) (hscale : 0 < scale)
    (hscale1 : scale ≤ 1) (hc₁ : 0 ≤ c₁)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (hineq : vec3EuclideanNorm
      (ucWeakHeatVector D2w Dtw (buAffinePoint τ scale z)) ≤
      c₁ * (Real.sqrt (spatialGradientSq w Dw (buAffinePoint τ scale z)) +
        vec3EuclideanNorm (w (buAffinePoint τ scale z)))) :
    vec3EuclideanNorm
      (ucWeakHeatVector (buAffineD2w τ scale D2w)
        (buAffineDtw τ scale Dtw) z) ≤
      c₁ * scale * (Real.sqrt (spatialGradientSq
        (buAffineField τ scale w) (buAffineDw τ scale Dw) z) +
        vec3EuclideanNorm ((buAffineField τ scale w) z)) := by
  let q : ParabolicPoint := buAffinePoint τ scale z
  let V : ℝ := vec3EuclideanNorm (w q)
  let G : ℝ := spatialGradientSq w Dw q
  have hV : 0 ≤ V := vec3EuclideanNorm_nonneg _
  have hG : 0 ≤ G := by
    dsimp [G, spatialGradientSq]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hsqrt : Real.sqrt (scale ^ 2 * G) = scale * Real.sqrt G := by
    rw [Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  have hscaled := mul_le_mul_of_nonneg_left hineq (sq_nonneg scale)
  have hgap : 0 ≤ c₁ * scale * (1 - scale) * V := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg hc₁ hscale.le) (sub_nonneg.mpr hscale1)
    · exact hV
  rw [bu_affine_weak_heat, vec3EuclideanNorm_smul,
    abs_of_pos (sq_pos_of_pos hscale), bu_affine_gradient_sq, hsqrt]
  dsimp [buAffineField]
  nlinarith only [hscaled, hgap]

/-- The weak heat inequality on an initial physical interval transfers to
the shifted normalized interval with the scaled coefficient. -/
theorem bu_affine_weak_heat_ae_bound_interval
    (τ scale a b c₁ : ℝ) (hscale : 0 < scale)
    (hscale1 : scale ≤ 1) (hc₁ : 0 ≤ c₁)
    (hsource : Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b) ⊆ Ioo (0 : ℝ) 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z))) :
    ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b))),
      vec3EuclideanNorm
        (ucWeakHeatVector (buAffineD2w τ scale D2w)
          (buAffineDtw τ scale Dtw) z) ≤
        c₁ * scale * (Real.sqrt (spatialGradientSq
          (buAffineField τ scale w) (buAffineDw τ scale Dw) z) +
          vec3EuclideanNorm ((buAffineField τ scale w) z)) := by
  have hSsub : spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) ⊆
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
    intro z hz
    exact ⟨hz.1, hsource hz.2⟩
  have hsourceI := ae_restrict_of_ae_restrict_of_subset hSsub hineq
  have hscaled := bu_affine_ae_pullback_interval τ scale a b hscale _ hsourceI
  filter_upwards [hscaled] with z hz
  exact bu_affine_weak_heat_bound_scaled τ scale c₁ hscale hscale1 hc₁
    w Dw D2w Dtw z hz

end ESS

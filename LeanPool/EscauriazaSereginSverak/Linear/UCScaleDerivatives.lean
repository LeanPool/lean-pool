/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleGeometry

/-!
# Derivative data under parabolic scaling

The weak derivative fields of `lem:uc-gaussian` transform with one or two
powers of the spatial scale.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The specified weak heat vector scales by the square of the parabolic
spatial scale. -/
theorem uc_scaled_weak_heat
    (x₀ : Vec3) (scale : ℝ)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    ucWeakHeatVector (ucScaledD2w x₀ scale D2w)
      (ucScaledDtw x₀ scale Dtw) z =
        scale ^ 2 • ucWeakHeatVector D2w Dtw (ucScaledPoint x₀ scale z) := by
  funext i
  simp only [ucWeakHeatVector, ucScaledD2w, ucScaledDtw, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_add, Finset.mul_sum]

/-- The squared spatial gradient scales by the square of the spatial
scale. -/
theorem uc_scaled_gradient_sq
    (x₀ : Vec3) (scale : ℝ) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    spatialGradientSq (ucScaledField x₀ scale w)
      (ucScaledDw x₀ scale Dw) z =
        scale ^ 2 * spatialGradientSq w Dw (ucScaledPoint x₀ scale z) := by
  simp only [spatialGradientSq, ucScaledDw]
  simp_rw [mul_pow]
  simp_rw [← Finset.mul_sum]

/-- The differential inequality keeps its form under a subunit parabolic
scale, with coefficient multiplied by that scale. -/
theorem uc_scaled_weak_heat_bound
    (x₀ : Vec3) (scale c₁ : ℝ) (hscale : 0 < scale)
    (hscale1 : scale ≤ 1) (hc₁ : 0 ≤ c₁)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (hineq : vec3EuclideanNorm
      (ucWeakHeatVector D2w Dtw (ucScaledPoint x₀ scale z)) ≤
      c₁ * (vec3EuclideanNorm (w (ucScaledPoint x₀ scale z)) +
        Real.sqrt (spatialGradientSq w Dw (ucScaledPoint x₀ scale z)))) :
    vec3EuclideanNorm
      (ucWeakHeatVector (ucScaledD2w x₀ scale D2w)
        (ucScaledDtw x₀ scale Dtw) z) ≤
      c₁ * scale *
        (vec3EuclideanNorm ((ucScaledField x₀ scale w) z) +
          Real.sqrt (spatialGradientSq (ucScaledField x₀ scale w)
            (ucScaledDw x₀ scale Dw) z)) := by
  let q : ParabolicPoint := ucScaledPoint x₀ scale z
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
  rw [uc_scaled_weak_heat, vec3EuclideanNorm_smul,
    abs_of_pos (sq_pos_of_pos hscale), uc_scaled_gradient_sq, hsqrt]
  dsimp [ucScaledField]
  nlinarith only [hscaled, hgap]

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineL2
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleDerivatives

/-!
# The heat inequality in affine parabolic coordinates

The differential inequality in `thm:bu` is preserved on the normalized
half-space cylinder by subunit affine parabolic changes of variables.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The weak heat vector scales by two spatial powers in affine parabolic
coordinates. -/
theorem bu_affine_weak_heat
    (τ scale : ℝ)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    ucWeakHeatVector (buAffineD2w τ scale D2w)
      (buAffineDtw τ scale Dtw) z =
        scale ^ 2 • ucWeakHeatVector D2w Dtw (buAffinePoint τ scale z) := by
  funext i
  simp only [ucWeakHeatVector, buAffineD2w, buAffineDtw, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_add, Finset.mul_sum]

/-- The squared first spatial derivative scales by two spatial powers. -/
theorem bu_affine_gradient_sq
    (τ scale : ℝ) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    spatialGradientSq (buAffineField τ scale w)
      (buAffineDw τ scale Dw) z =
        scale ^ 2 * spatialGradientSq w Dw (buAffinePoint τ scale z) := by
  simp only [spatialGradientSq, buAffineDw]
  simp_rw [mul_pow]
  simp_rw [← Finset.mul_sum]

/-- A pointwise weak heat inequality keeps the same coefficient after a
subunit affine parabolic change of variables. -/
theorem bu_affine_weak_heat_bound
    (τ scale c₁ : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hc₁ : 0 ≤ c₁)
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
      c₁ * (Real.sqrt (spatialGradientSq (buAffineField τ scale w)
        (buAffineDw τ scale Dw) z) +
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
  have hgapV : 0 ≤ c₁ * scale * (1 - scale) * V := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg hc₁ hscale.le) (sub_nonneg.mpr hscale1)
    · exact hV
  have hgapV2 : 0 ≤ c₁ * (1 - scale) * V := by
    apply mul_nonneg
    · exact mul_nonneg hc₁ (sub_nonneg.mpr hscale1)
    · exact hV
  have hgapG : 0 ≤ c₁ * scale * (1 - scale) * Real.sqrt G := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg hc₁ hscale.le) (sub_nonneg.mpr hscale1)
    · exact Real.sqrt_nonneg _
  rw [bu_affine_weak_heat, vec3EuclideanNorm_smul,
    abs_of_pos (sq_pos_of_pos hscale), bu_affine_gradient_sq, hsqrt]
  dsimp [buAffineField]
  nlinarith only [hscaled, hgapV, hgapV2, hgapG]

/-- Almost everywhere statements pull back through the affine parabolic map
on the positive half-space slab. -/
theorem bu_affine_ae_pullback
    (τ scale : ℝ) (hscale : 0 < scale)
    (P : ParabolicPoint → Prop)
    (hP : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)))), P z) :
    ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      P (buAffinePoint τ scale z) := by
  have hΩ : MeasurableSet {x : Vec3 | 0 < x 2} :=
    (isOpen_lt continuous_const (continuous_apply 2)).measurableSet
  have hmap := CKN.map_scalingParabolic_restrict hscale
    ((0 : Vec3), τ) hΩ (measurableSet_Ioo : MeasurableSet (Ioo τ (τ + scale ^ 2)))
  rw [rescaledSpaceTimeSet_eq_preimage scale
      (show ParabolicPoint from ((0 : Vec3), τ))
      {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)),
    ← buAffinePoint_eq_scalingParabolic,
    buAffinePoint_preimage_halfSlab τ scale hscale] at hmap
  have hPmap : ∀ᵐ z ∂(Measure.map (buAffinePoint τ scale)
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)))), P z := by
    rw [hmap]
    exact Measure.ae_smul_measure hP (ENNReal.ofReal (scale⁻¹ ^ 5))
  exact ae_of_ae_map (buAffinePoint_continuous τ scale).measurable.aemeasurable hPmap

/-- The almost everywhere differential inequality in `thm:bu` transfers
through a subunit affine parabolic change of variables. -/
theorem bu_affine_weak_heat_ae_bound
    (τ scale c₁ : ℝ) (hτ : 0 ≤ τ) (hscale : 0 < scale)
    (hupper : τ + scale ^ 2 ≤ 1) (hc₁ : 0 ≤ c₁)
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
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm
        (ucWeakHeatVector (buAffineD2w τ scale D2w)
          (buAffineDtw τ scale Dtw) z) ≤
        c₁ * (Real.sqrt (spatialGradientSq (buAffineField τ scale w)
          (buAffineDw τ scale Dw) z) +
          vec3EuclideanNorm ((buAffineField τ scale w) z)) := by
  have hI : Ioo τ (τ + scale ^ 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨lt_of_le_of_lt hτ ht.1, ht.2.trans_le hupper⟩
  have hSsub : spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo τ (τ + scale ^ 2)) ⊆
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
    intro z hz
    exact ⟨hz.1, hI hz.2⟩
  have hsource : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z)) :=
    ae_restrict_of_ae_restrict_of_subset hSsub hineq
  have hscaled := bu_affine_ae_pullback τ scale hscale _ hsource
  have hscale2le : scale ^ 2 ≤ 1 := by linarith only [hτ, hupper]
  have hscale1 : scale ≤ 1 := by nlinarith only [hscale, hscale2le]
  filter_upwards [hscaled] with z hz
  exact bu_affine_weak_heat_bound τ scale c₁ hscale hscale1 hc₁
    w Dw D2w Dtw z hz

end ESS

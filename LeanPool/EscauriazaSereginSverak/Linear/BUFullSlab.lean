/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUTimeIteration

/-!
# Vanishing on one rescaled time slab

The full small-growth result applies after an affine parabolic rescaling
whenever the rescaled growth exponent is within its permitted range.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A full-cylinder vanishing result for the rescaled field gives vanishing
on its image time slab. -/
theorem bu_affine_full_slab
    (c₁ M A τ scale : ℝ) (hc₁ : 0 < c₁)
    (hτ : 0 ≤ τ) (hscale : 0 < scale)
    (hupper : τ + scale ^ 2 ≤ 1)
    (hAres : M * scale ^ 2 ≤ A)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hzeroτ : ∀ x : Vec3, 0 < x 2 → w (x, τ) = 0)
    (hderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    (hsmall : ∀ (v : ParabolicPoint → Vec3)
      (Dv : ParabolicPoint → Fin 3 → Vec3)
      (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
      (Dtv : ParabolicPoint → Vec3),
      ContinuousOn v ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) →
      (∀ x : Vec3, 0 < x 2 → v (x, 0) = 0) →
      HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
        v Dv D2v Dtv →
      (∀ S : Set ParabolicPoint,
        S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
        Bornology.IsBounded S →
        (∫⁻ z in S, ‖Dv z‖ₑ ^ (2 : ℝ) +
          ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) →
      (∀ᵐ z ∂(volume.restrict
        (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
        vec3EuclideanNorm (fun i => Dtv z i + ∑ j, D2v z i j j) ≤
          c₁ * (Real.sqrt (spatialGradientSq v Dv z) +
            vec3EuclideanNorm (v z))) →
      (∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        vec3EuclideanNorm (v z) ≤
          Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) →
      ∀ x : Vec3, 0 < x 2 → ∀ s : ℝ,
        0 < s → s < 1 → v (x, s) = 0) :
    ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      τ < t → t < τ + scale ^ 2 → w (x, t) = 0 := by
  have hscaledCont := buAffineField_continuousOn τ scale hτ hscale
    hupper w hcont
  have hscaledInit := buAffineField_initial_zero τ scale w hzeroτ hscale
  have hscaledWeak := bu_affine_weak_derivatives τ scale hτ hscale
    hupper w Dw D2w Dtw hderiv
  have hscaledL2 := bu_affine_derivative_l2 τ scale hτ hscale
    hupper w Dw D2w Dtw hderiv hL2
  have hscaledIneq := bu_affine_weak_heat_ae_bound τ scale c₁
    hτ hscale hupper hc₁.le w Dw D2w Dtw hineq
  have hscaledGrowth : ∀ z ∈
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (buAffineField τ scale w z) ≤
        Real.exp (A * vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    exact buAffineField_growth M A τ scale hscale hAres hτ hupper
      w hgrowth hz
  have hscaledZero := hsmall
    (buAffineField τ scale w) (buAffineDw τ scale Dw)
    (buAffineD2w τ scale D2w) (buAffineDtw τ scale Dtw)
    hscaledCont hscaledInit hscaledWeak hscaledL2 hscaledIneq hscaledGrowth
  intro x hx t htτ htend
  let y : Vec3 := scale⁻¹ • x
  let s : ℝ := (t - τ) / scale ^ 2
  have hy : 0 < y 2 := by
    change 0 < scale⁻¹ * x 2
    exact mul_pos (inv_pos.mpr hscale) hx
  have hs0 : 0 < s := by
    dsimp [s]
    exact div_pos (sub_pos.mpr htτ) (sq_pos_of_pos hscale)
  have hs1 : s < 1 := by
    dsimp [s]
    apply (div_lt_iff₀ (sq_pos_of_pos hscale)).2
    linarith only [htend]
  have hpoint : buAffinePoint τ scale (y, s) = (x, t) := by
    apply Prod.ext
    · change scale • (scale⁻¹ • x) = x
      rw [smul_smul]
      field_simp [hscale.ne']
      simp
    · change τ + scale ^ 2 * ((t - τ) / scale ^ 2) = t
      field_simp [hscale.ne']
      ring
  have hzero := hscaledZero y hy s hs0 hs1
  change w (buAffinePoint τ scale (y, s)) = 0 at hzero
  rw [hpoint] at hzero
  exact hzero

end ESS

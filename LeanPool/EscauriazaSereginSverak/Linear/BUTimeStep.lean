/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUZeroTrace
public import LeanPool.EscauriazaSereginSverak.Linear.BUAssembly

/-!
# One time-extension step for backward uniqueness

The affine rescaling in `lem:bu-iterate` turns vanishing before a time
`τ` into vanishing before the next time in the geometric sequence.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Short-time vanishing extends from an earlier interval to the next
geometric time interval by affine parabolic rescaling. -/
theorem bu_time_extension_step
    (c₁ A γ₁ τ : ℝ) (hc₁ : 0 < c₁) (hA : 0 ≤ A)
    (hτ : 0 ≤ τ) (hτone : τ < 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
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
        Real.exp (A * vec3EuclideanNorm z.1 ^ 2))
    (hprev : ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      0 < t → t < τ → w (x, t) = 0)
    (hshort : ∀ (v : ParabolicPoint → Vec3)
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
        0 < s → s < γ₁ → v (x, s) = 0) :
    ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      0 < t → t < τ + (1 - τ) * γ₁ → w (x, t) = 0 := by
  let scale := Real.sqrt (1 - τ)
  have hscale : 0 < scale := Real.sqrt_pos.2 (sub_pos.2 hτone)
  have hscaleSq : scale ^ 2 = 1 - τ := Real.sq_sqrt (sub_nonneg.2 hτone.le)
  have hupper : τ + scale ^ 2 ≤ 1 := by rw [hscaleSq]; nlinarith only []
  have hAres : A * scale ^ 2 ≤ A := by
    rw [hscaleSq]
    have hfactor : 1 - τ ≤ 1 := by linarith only [hτ]
    nlinarith only [hA, hfactor]
  have hzeroτ : ∀ x : Vec3, 0 < x 2 → w (x, τ) = 0 := by
    intro x hx
    rcases eq_or_lt_of_le hτ with hτzero | hτpos
    · rw [← hτzero]
      exact hinit x hx
    · exact bu_zero_at_time_of_left w hcont τ hτpos hτone hprev x hx
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
    exact buAffineField_growth A A τ scale hscale hAres hτ hupper
      w hgrowth hz
  have hscaledZero := hshort
    (buAffineField τ scale w) (buAffineDw τ scale Dw)
    (buAffineD2w τ scale D2w) (buAffineDtw τ scale Dtw)
    hscaledCont hscaledInit hscaledWeak hscaledL2 hscaledIneq hscaledGrowth
  intro x hx t ht0 htend
  by_cases htτ : t < τ
  · exact hprev x hx t ht0 htτ
  by_cases htEq : t = τ
  · subst t
    exact hzeroτ x hx
  have htτpos : τ < t := lt_of_le_of_ne (le_of_not_gt htτ) (Ne.symm htEq)
  let y : Vec3 := scale⁻¹ • x
  let s : ℝ := (t - τ) / scale ^ 2
  have hy : 0 < y 2 := by
    change 0 < scale⁻¹ * x 2
    exact mul_pos (inv_pos.mpr hscale) hx
  have hs0 : 0 < s := by
    dsimp [s]
    exact div_pos (sub_pos.mpr htτpos) (sq_pos_of_pos hscale)
  have hsγ : s < γ₁ := by
    dsimp [s]
    apply (div_lt_iff₀ (sq_pos_of_pos hscale)).2
    rw [hscaleSq]
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
  have hzero := hscaledZero y hy s hs0 hsγ
  change w (buAffinePoint τ scale (y, s)) = 0 at hzero
  rw [hpoint] at hzero
  exact hzero

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleAE

/-!
# Normalized data for the Gaussian estimate

The output-point geometry in `lem:uc-gaussian` produces a normalized weak
solution on the fixed time interval `(0,2)`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Translation and parabolic dilation provide all normalized hypotheses
used in the Gaussian estimate (`lem:uc-gaussian`). -/
theorem uc_gaussian_normalize_and_scale
    (R T γ c₁ : ℝ) (hR : 0 < R) (hT : 0 < T)
    (hγ' : γ < 3 / 16) (hTsmall : T ≤ 1)
    (hc₁ : 0 < c₁) (x₀ x : Vec3) (t : ℝ) (ht : 0 < t)
    (ht' : t ≤ γ * T)
    (hx : vec3EuclideanNorm (x - x₀) ≤
      (3 / 8) * Real.sqrt (2 / 100) * R)
    (hd : (16 / 100) * t ≤ vec3EuclideanNorm (x - x₀) ^ 2)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (vec3Ball x₀ R ×ˢ Ico 0 T))
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball x₀ R) (Ioo 0 T)
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z)))
    (hflat : UCIntegralFlatness x₀ R T w) :
    let scale := Real.sqrt (2 * t)
    let X := (Real.sqrt (2 / 100))⁻¹ • (x - x₀)
    let ρ := 2 * vec3EuclideanNorm X / scale
    let v := ucScaledField x₀ scale w
    let Dv := ucScaledDw x₀ scale Dw
    let D2v := ucScaledD2w x₀ scale D2w
    let Dtv := ucScaledDtw x₀ scale Dtw
    4 ≤ ρ ∧ scale * ρ ≤ 3 * R / 4 ∧
      2 * scale ^ 2 ≤ 3 * T / 4 ∧
      HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
        v Dv D2v Dtv ∧
      (∫⁻ z in ucCylinder ρ,
        ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
          ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      UCIntegralFlatness 0 ρ 2 v ∧
      (∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
        vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
          c₁ * scale * (vec3EuclideanNorm (v z) +
            Real.sqrt (spatialGradientSq v Dv z))) := by
  dsimp
  let scale := Real.sqrt (2 * t)
  let X := (Real.sqrt (2 / 100))⁻¹ • (x - x₀)
  let ρ := 2 * vec3EuclideanNorm X / scale
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hgeom := uc_gaussian_scale_geometry R T γ t hT hγ'
    x₀ x ht ht' hx hd
  change 4 ≤ ρ ∧ scale * ρ ≤ 3 * R / 4 ∧
    2 * scale ^ 2 ≤ 3 * T / 4 at hgeom
  rcases hgeom with ⟨hρ, hball, htime⟩
  have hscale1 : scale ≤ 1 := by
    have hscaleSq : scale ^ 2 ≤ 3 / 8 := by
      linarith only [htime, hTsmall]
    nlinarith only [hscale, hscaleSq]
  have hballR : scale * ρ ≤ R := by
    linarith only [hball, hR]
  have htimeT : 2 * scale ^ 2 ≤ T := by
    linarith only [htime, hT]
  have hcontOpen : ContinuousOn w (vec3Ball x₀ R ×ˢ Ioo 0 T) :=
    hcont.mono (fun _ hz => ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩)
  obtain ⟨_, hweakQ, hL2Q, hineqQ⟩ :=
    uc_restrict_data c₁
      (vec3Ball x₀ (scale * ρ)) (vec3Ball x₀ R)
      (Ioo 0 (scale ^ 2 * 2)) (Ioo 0 T)
      w Dw D2w Dtw (isOpen_vec3Ball _ _) isOpen_Ioo
      (vec3Ball_mono hballR) (fun _ hz =>
        ⟨hz.1, hz.2.trans_le (by simpa only [mul_comm] using htimeT)⟩)
      hcontOpen hweak hL2 hineq
  have hL2w : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
          ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ) := by
            apply lintegral_mono
            intro z
            exact le_add_of_nonneg_right (by positivity) |>.trans
              (le_add_of_nonneg_right (by positivity) |>.trans
                (le_add_of_nonneg_right (by positivity)))
      _ < ⊤ := hL2
  have hscaledWeak := uc_scaled_weak_derivatives x₀ scale ρ hscale hscale1
    w Dw D2w Dtw hweakQ hL2Q
  have hscaledL2 := uc_scaled_l2_data x₀ R T scale ρ hscale hscale1
    hballR htimeT w Dw D2w Dtw hweak hL2
  have hscaledFlat := uc_integral_flatness_scaled x₀ R T scale ρ
    hR hT hscale w hweak.1 hL2w hflat
  have hscaledIneq := uc_scaled_weak_heat_ae_bound x₀ scale ρ c₁
    hscale hscale1 hc₁.le w Dw D2w Dtw hineqQ
  exact ⟨hρ, hball, htime, hscaledWeak, hscaledL2,
    hscaledFlat, hscaledIneq⟩

end ESS

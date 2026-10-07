/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyIntegral

/-!
# Absorption of the scaled weak heat term

A single half-space Carleman constant permits one small rescaling for all
spatial radii and lower-time cutoff widths in `lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- When the scaled lower-order coefficient is small, the weighted cutoff
energy is controlled entirely by the scalar cutoff derivative error. -/
theorem bu_short_cutoff_energy_absorbed :
    ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ (scale R ε c₁ : ℝ) (_hscale : 0 < scale) (_hscale1 : scale ≤ 1)
        (hR : 0 < R) (_hε : 0 < ε) (_hc₁ : 0 ≤ c₁)
        (_hsmall : c * 36 * (c₁ * scale) ^ 2 ≤ 1 / 2)
        (w : ParabolicPoint → Vec3)
        (Dw : ParabolicPoint → Fin 3 → Vec3)
        (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtw : ParabolicPoint → Vec3),
        ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1) →
        HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
          w Dw D2w Dtw →
        (∀ S : Set ParabolicPoint,
          S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
          Bornology.IsBounded S →
          (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
            ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) →
        (∀ᵐ z ∂(volume.restrict
          (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
          vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
            c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
              vec3EuclideanNorm (w z))) →
        ∀ a : ℝ, max a₀ 1 < a →
          let κ := buShortFullCutoff scale R hR ε
          let K := buCutSupportSet κ
          let v := buAffineField (-scale ^ 2 / 2) scale w
          let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
          let W := buCutField κ v
          let DW := buCutDw κ v Dv
          (∫ z in K, buShortCarlemanWeight a z *
            (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)) ≤
          4 * c * (∫ z in K, buShortCarlemanWeight a z *
            buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2) := by
  obtain ⟨a₀, c, ha₀, hc, hCarAll⟩ := bu_short_cutoff_carleman_uniform
  refine ⟨a₀, c, ha₀, hc, ?_⟩
  intro scale R ε c₁ hscale hscale1 hR hε hc₁ hsmall
    w Dw D2w Dtw hcont hweak hL2 hineq a ha
  let κ := buShortFullCutoff scale R hR ε
  let K := buCutSupportSet κ
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let D2W := buCutD2 κ v Dv D2v
  let DtW := buCutDt κ v Dtv
  let μ := volume.restrict K
  let E : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)
  let H : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
      spatialGradientSq W DW z / z.2)
  let F : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2
  let B : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2
  have ha₀' : a₀ < a := lt_of_le_of_lt (le_max_left _ _) ha
  have ha1 : 1 ≤ a := (le_max_right _ _).trans ha.le
  have hCar := hCarAll scale R ε hscale hscale1 hR hε
    w Dw D2w Dtw hcont hweak hL2 a ha₀'
  obtain ⟨hHs, _, hFs⟩ :=
    bu_short_cutoff_carleman_integral_eq_support scale R ε a
      hscale hscale1 hR hε v Dv D2v Dtv
  dsimp only at hCar
  rw [hHs, hFs] at hCar
  have hLow := bu_short_energy_integral_le_left scale R ε a
    hscale hscale1 hR hε ha1
    w Dw D2w Dtw hcont hweak hL2
  have hOp := bu_short_cutoff_heat_integral_le scale R ε c₁ a
    hscale hscale1 hR hε hc₁
    w Dw D2w Dtw hcont hweak hL2 hineq
  change (∫ z, H z ∂μ) ≤ c * (∫ z, F z ∂μ) at hCar
  change (∫ z, E z ∂μ) ≤ (∫ z, H z ∂μ) at hLow
  change (∫ z, F z ∂μ) ≤
    36 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
      2 * (∫ z, B z ∂μ) at hOp
  have hE0 : 0 ≤ ∫ z, E z ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [] with z
    have hG : 0 ≤ spatialGradientSq W DW z := by
      dsimp [spatialGradientSq]
      positivity
    exact mul_nonneg (by dsimp [buShortCarlemanWeight]; positivity)
      (add_nonneg (sq_nonneg _) hG)
  have hstep : (∫ z, E z ∂μ) ≤
      c * (36 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
        2 * (∫ z, B z ∂μ)) :=
    hLow.trans (hCar.trans (mul_le_mul_of_nonneg_left hOp hc.le))
  have hcoef : (c * 36 * (c₁ * scale) ^ 2) *
      (∫ z, E z ∂μ) ≤ (1 / 2 : ℝ) * (∫ z, E z ∂μ) :=
    mul_le_mul_of_nonneg_right hsmall hE0
  change (∫ z, E z ∂μ) ≤ 4 * c * (∫ z, B z ∂μ)
  nlinarith only [hstep, hcoef]

end ESS

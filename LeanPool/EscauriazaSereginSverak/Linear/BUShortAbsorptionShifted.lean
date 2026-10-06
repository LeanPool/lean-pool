/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCoreLower
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAbsorption

/-!
# Phase-shifted absorbed Carleman estimate

The fixed normal phase can be removed from both sides of the absorbed
half-space estimate without changing its coefficient.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Multiplying the Carleman density by a fixed positive factor
preserves an integrated inequality. -/
theorem bu_short_integral_shift_le
    (scale a c : ℝ) (K : Set ParabolicPoint)
    (F G : ParabolicPoint → ℝ)
    (h : (∫ z in K, buShortCarlemanWeight a z * F z
      ∂(volume : Measure ParabolicPoint)) ≤
      c * (∫ z in K, buShortCarlemanWeight a z * G z
        ∂(volume : Measure ParabolicPoint))) :
    (∫ z in K, buShortShiftedWeight scale a z * F z
      ∂(volume : Measure ParabolicPoint)) ≤
      c * (∫ z in K, buShortShiftedWeight scale a z * G z
        ∂(volume : Measure ParabolicPoint)) := by
  let q := Real.exp (-(2 * a * buShortB scale))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have h' := mul_le_mul_of_nonneg_left h hq
  have hleft : (∫ z in K, buShortShiftedWeight scale a z * F z
      ∂(volume : Measure ParabolicPoint)) =
      q * (∫ z in K, buShortCarlemanWeight a z * F z
        ∂(volume : Measure ParabolicPoint)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    dsimp [buShortShiftedWeight, q]
    ring
  have hright : (∫ z in K, buShortShiftedWeight scale a z * G z
      ∂(volume : Measure ParabolicPoint)) =
      q * (∫ z in K, buShortCarlemanWeight a z * G z
        ∂(volume : Measure ParabolicPoint)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    dsimp [buShortShiftedWeight, q]
    ring
  rw [hleft, hright]
  nlinarith only [h']

/-- For a sufficiently small parabolic rescaling, the shifted cutoff
energy is controlled by the shifted scalar cutoff heat error. -/
theorem bu_short_cutoff_energy_absorbed_shifted :
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
          (∫ z in K, buShortShiftedWeight scale a z *
            (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)) ≤
          4 * c * (∫ z in K, buShortShiftedWeight scale a z *
            buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2) := by
  obtain ⟨a₀, c, ha₀, hc, hAbs⟩ := bu_short_cutoff_energy_absorbed
  refine ⟨a₀, c, ha₀, hc, ?_⟩
  intro scale R ε c₁ hscale hscale1 hR hε hc₁ hsmall
    w Dw D2w Dtw hcont hweak hL2 hineq a ha
  let κ := buShortFullCutoff scale R hR ε
  let K := buCutSupportSet κ
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  have h := hAbs scale R ε c₁ hscale hscale1 hR hε hc₁ hsmall
    w Dw D2w Dtw hcont hweak hL2 hineq a ha
  exact bu_short_integral_shift_le scale a (4 * c) K
    (fun z => vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)
    (fun z => buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2)
    h

end ESS

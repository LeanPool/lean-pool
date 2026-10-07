/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedData

/-!
# Integrated weak heat inequality on the cutoff support

The squared differential inequality is integrated with the half-space
Carleman weight over the compact cutoff support.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weighted weak heat energy is bounded by cutoff energy and
cutoff-derivative error on the compact support. -/
theorem bu_short_cutoff_heat_integral_le
    (scale R ε c₁ a : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z))) :
    let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
    let κ := buShortFullCutoff scale R hR ε
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
    let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    let D2W := buCutD2 κ v Dv D2v
    let DtW := buCutDt κ v Dtv
    (∫ z in K, buShortCarlemanWeight a z *
      vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2) ≤
      36 * (c₁ * scale) ^ 2 *
        (∫ z in K, buShortCarlemanWeight a z *
          (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)) +
      2 * (∫ z in K, buShortCarlemanWeight a z *
        buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2) := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let κ := buShortFullCutoff scale R hR ε
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let D2W := buCutD2 κ v Dv D2v
  let DtW := buCutDt κ v Dtv
  let μ := volume.restrict K
  let F : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2
  let E : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)
  let B : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2
  obtain ⟨hKcompact, _, hKsource⟩ :=
    bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε
  obtain ⟨hEInt, hFInt⟩ :=
    bu_short_weighted_data_integrable scale R ε a hscale hscale1 hR hε
      w Dw D2w Dtw hcont hweak hL2
  have hBInt : Integrable B μ :=
    bu_short_weighted_error_integrable scale R ε c₁ a
      hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2
  have hSq := ae_restrict_of_ae_restrict_of_subset hKsource
    (bu_short_cutoff_heat_sq_ae_bound scale R ε c₁
      hscale hscale1 hR hc₁ w Dw D2w Dtw hineq)
  have hPoint : ∀ᵐ z ∂μ,
      F z ≤ 36 * (c₁ * scale) ^ 2 * E z + 2 * B z := by
    filter_upwards [hSq] with z hz
    have hweight : 0 ≤ buShortCarlemanWeight a z := by
      dsimp [buShortCarlemanWeight]
      positivity
    have hmul := mul_le_mul_of_nonneg_left hz hweight
    change F z ≤ 36 * (c₁ * scale) ^ 2 * E z + 2 * B z
    calc
      F z ≤ buShortCarlemanWeight a z *
          (36 * (c₁ * scale) ^ 2 *
            (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z) +
            2 * buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2) :=
        hmul
      _ = _ := by dsimp [E, B]; ring
  have hRhsInt : Integrable
      (fun z => 36 * (c₁ * scale) ^ 2 * E z + 2 * B z) μ :=
    (hEInt.const_mul (36 * (c₁ * scale) ^ 2)).add
      (hBInt.const_mul 2)
  have hI := integral_mono_ae hFInt hRhsInt hPoint
  change (∫ z, F z ∂μ) ≤
    ∫ z, 36 * (c₁ * scale) ^ 2 * E z + 2 * B z ∂μ at hI
  rw [integral_add (hEInt.const_mul (36 * (c₁ * scale) ^ 2))
    (hBInt.const_mul 2), integral_const_mul, integral_const_mul] at hI
  change (∫ z, F z ∂μ) ≤
    36 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
      2 * (∫ z, B z ∂μ)
  exact hI

end ESS

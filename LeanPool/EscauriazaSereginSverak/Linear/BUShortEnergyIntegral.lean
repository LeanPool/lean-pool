/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCarlemanUniform
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortLeftIntegrable

/-!
# Integrated lower bound for the Carleman energy

At parameters at least one, the half-space Carleman left side controls
the weighted quadratic energy of the compact cutoff field.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weighted cutoff energy is bounded by the half-space Carleman
mass and gradient integral on the compact cutoff support. -/
theorem bu_short_energy_integral_le_left
    (scale R ε a : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) (ha : 1 ≤ a)
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
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
    let κ := buShortFullCutoff scale R hR ε
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    (∫ z in K, buShortCarlemanWeight a z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)) ≤
    (∫ z in K, buShortCarlemanWeight a z *
      (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq W DW z / z.2)) := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let κ := buShortFullCutoff scale R hR ε
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let W := buCutField κ v
  let DW := buCutDw κ v Dv
  let μ := volume.restrict K
  let E : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z)
  let H : ParabolicPoint → ℝ := fun z => buShortCarlemanWeight a z *
    (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
      spatialGradientSq W DW z / z.2)
  have hKcompact : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hKdomain : K ⊆ halfSpaceDomain :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).2.1
  have hEInt : Integrable E μ :=
    (bu_short_weighted_data_integrable scale R ε a
      hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2).1
  have hHInt : Integrable H μ :=
    bu_short_carleman_left_integrable scale R ε a
      hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2
  have hPoint : ∀ᵐ z ∂μ, E z ≤ H z := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    have hzt := (hKdomain hz).2
    have hG : 0 ≤ spatialGradientSq W DW z := by
      dsimp [spatialGradientSq]
      positivity
    have hraw := bu_short_carleman_mass_gradient_lower a z.2
      (vec3EuclideanNorm (W z)) (spatialGradientSq W DW z)
      ha hzt.1 hzt.2.le hG
    have hexp : 0 ≤ Real.exp (2 * halfSpacePhase a (3 / 4) z) :=
      Real.exp_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hraw hexp
    change buShortCarlemanWeight a z *
      (vec3EuclideanNorm (W z) ^ 2 + spatialGradientSq W DW z) ≤
      buShortCarlemanWeight a z *
      (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq W DW z / z.2)
    dsimp [buShortCarlemanWeight]
    nlinarith only [hmul]
  exact integral_mono_ae hEInt hHInt hPoint

end ESS

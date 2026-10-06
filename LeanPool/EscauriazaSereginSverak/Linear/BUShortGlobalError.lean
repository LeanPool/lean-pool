/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGlobalIntegral
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedEarlyIntegrable

/-!
# Global phase and shell bound for the short-time cutoff

The compact cutoff error is bounded by a fixed negative-phase Gaussian
integral, a fixed-parameter global weighted energy, and the shrinking
lower-time transition integral.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- The compact cutoff heat error is controlled by the two global
energies and the shrinking lower-time transition error. -/
theorem bu_short_weighted_error_le_global
    (scale R ε c₁ C₁ C₂ a : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 1 ≤ R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
    (ha : 0 ≤ a)
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
    (hJ : IntegrableOn (fun z =>
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        (1 + z.1 2) ^ 4 *
        (vec3EuclideanNorm
            (buAffineField (-scale ^ 2 / 2) scale w z) ^ 2 +
          spatialGradientSq
            (buAffineField (-scale ^ 2 / 2) scale w)
            (buAffineDw (-scale ^ 2 / 2) scale Dw) z))
      (buShortWideGapRegion scale) volume)
    (hWP : IntegrableOn (fun z =>
      buShortShiftedWeight scale a z * (1 + z.1 2) ^ 4 *
        (vec3EuclideanNorm
            (buAffineField (-scale ^ 2 / 2) scale w z) ^ 2 +
          spatialGradientSq
            (buAffineField (-scale ^ 2 / 2) scale w)
            (buAffineDw (-scale ^ 2 / 2) scale Dw) z))
      (buShortHighStrip scale) volume)
    (hWQ : IntegrableOn (fun z =>
      buShortShiftedWeight scale a z *
        (vec3EuclideanNorm
            (buAffineField (-scale ^ 2 / 2) scale w z) ^ 2 +
          spatialGradientSq
            (buAffineField (-scale ^ 2 / 2) scale w)
            (buAffineDw (-scale ^ 2 / 2) scale Dw) z))
      (buShortHighStrip scale) volume) :
    let K := buCutSupportSet
      (buShortFullCutoff scale R (by linarith only [hR]) ε)
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    (∫ z in K, buShortShiftedWeight scale a z *
      buShortCutoffHeatErrorSize scale R (by linarith only [hR])
        ε c₁ v Dv z ^ 2
      ∂(volume : Measure ParabolicPoint)) ≤
      4 * buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
        Real.exp (-(a * buShortD scale)) *
        (∫ z in buShortWideGapRegion scale,
          Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
            (1 + z.1 2) ^ 4 *
            (vec3EuclideanNorm (v z) ^ 2 +
              spatialGradientSq v Dv z)
          ∂(volume : Measure ParabolicPoint)) +
      4 * buShortShellCoeff scale R c₁ ^ 2 *
        (∫ z in buShortHighStrip scale,
          buShortShiftedWeight scale a z *
            (vec3EuclideanNorm (v z) ^ 2 +
              spatialGradientSq v Dv z)
          ∂(volume : Measure ParabolicPoint)) +
      2 * (∫ z in K, buShortShiftedWeight scale a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
        ∂(volume : Measure ParabolicPoint)) := by
  have hR0 : 0 < R := by linarith only [hR]
  let K := buCutSupportSet (buShortFullCutoff scale R hR0 ε)
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let W := buShortShiftedWeight scale a
  let T : ParabolicPoint → ℝ := fun z =>
    Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2))
  let P : ParabolicPoint → ℝ := fun z => (1 + z.1 2) ^ 4
  let Q : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  let B : ParabolicPoint → ℝ := fun z =>
    if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
      8 / ε * vec3EuclideanNorm (v z) else 0
  let G := buShortWideGapRegion scale
  let H := buShortHighStrip scale
  let e := Real.exp (-(a * buShortD scale))
  have hKcompact : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR0 hε).1
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hGmeas : MeasurableSet G := buShortWideGapRegion_measurable scale
  have hHmeas : MeasurableSet H := buShortHighStrip_measurable scale
  have hKH : K ⊆ H := buShortCutSupport_subset_highStrip
    scale R ε hscale hscale1 hR0 hε
  have hGH : G ⊆ H := buShortWideGapRegion_subset_highStrip scale
  have hW : ∀ z ∈ H, 0 ≤ W z := by
    intro z _
    dsimp [W, buShortShiftedWeight, buShortCarlemanWeight]
    positivity
  have hP0 : ∀ z ∈ H, 0 ≤ P z := by
    intro z _
    dsimp [P]
    positivity
  have hQ : ∀ z ∈ H, 0 ≤ Q z := by
    intro z _
    dsimp [Q]
    have hgrad : 0 ≤ spatialGradientSq v Dv z := by
      dsimp [spatialGradientSq]
      positivity
    positivity
  have hgap : ∀ z ∈ G, W z ≤ e * T z := by
    intro z hz
    have h := buShortShiftedWeight_le_on_wideGap hscale hscale1 ha hz
    simpa only [W, e, T, mul_comm] using h
  have hB := bu_short_shifted_early_integrable
    scale R ε a hscale hscale1 hR0 hε
    w Dw D2w Dtw hcont hweak hL2
  have hglobal := bu_short_split_integral_le_global
    K G H hKmeas hGmeas hHmeas hKH hGH W T P Q B
    (buShortUniformErrorCoeff scale c₁ C₁ C₂)
    (buShortShellCoeff scale R c₁) e
    hW hP0 hQ hgap hWP hWQ hJ hB
  have hlocal := bu_short_weighted_error_le_split
    scale R ε c₁ C₁ C₂ a hscale hscale1 hR hε hc₁ hC₁ hN
    hC₂ hP w Dw D2w Dtw hcont hweak hL2
  exact hlocal.trans hglobal

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAbsorptionShifted

/-!
# Quantitative mass bound in the positive-phase plateau

The absorbed half-space estimate and the global cutoff error bound
control every fixed measurable part of the cutoff plateau.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The mass on a fixed cutoff plateau is controlled by the negative
phase gap, spatial shell, and lower-time transition. -/
theorem bu_short_core_mass_bound :
    ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ (scale R ε c₁ C₁ C₂ a : ℝ)
        (hscale : 0 < scale) (hscale1 : scale ≤ 1)
        (hR : 1 ≤ R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
        (hC₁ : 0 ≤ C₁)
        (hN : ∀ scale y : ℝ,
          |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
        (hC₂ : 0 ≤ C₂)
        (hP : ∀ x : ℝ,
          |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
        (hsmall : c * 36 * (c₁ * scale) ^ 2 ≤ 1 / 2)
        (ha : max a₀ 1 < a)
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
              vec3EuclideanNorm (w z)))
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
          (buShortHighStrip scale) volume)
        (S : Set ParabolicPoint) (hSmeas : MeasurableSet S)
        (hScore : ∀ z ∈ S,
          parabolicHomeomorph z ∈ buShortCoreRegion scale R ε),
        let K := buCutSupportSet
          (buShortFullCutoff scale R (by linarith only [hR]) ε)
        let v := buAffineField (-scale ^ 2 / 2) scale w
        let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
        (∫ z in S, buShortShiftedWeight scale a z *
          vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint)) ≤
          4 * c * (
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
              ∂(volume : Measure ParabolicPoint))) := by
  obtain ⟨a₀, c, ha₀, hc, hAbs⟩ :=
    bu_short_cutoff_energy_absorbed_shifted
  refine ⟨a₀, c, ha₀, hc, ?_⟩
  intro scale R ε c₁ C₁ C₂ a hscale hscale1 hR hε hc₁
    hC₁ hN hC₂ hP hsmall ha w Dw D2w Dtw
    hcont hweak hL2 hineq hJ hWP hWQ S hSmeas hScore
  have hR0 : 0 < R := by linarith only [hR]
  have hCore := bu_short_core_mass_le_cutoff_energy
    scale R ε a hscale hscale1 hR0 hε
    w Dw D2w Dtw hcont hweak hL2 S hSmeas hScore
  have hAbs' := hAbs scale R ε c₁ hscale hscale1 hR0 hε hc₁
    hsmall w Dw D2w Dtw hcont hweak hL2 hineq a ha
  have ha0 : 0 ≤ a := by
    have h1 : (1 : ℝ) ≤ max a₀ 1 := le_max_right _ _
    linarith only [h1, ha]
  have hGlobal := bu_short_weighted_error_le_global
    scale R ε c₁ C₁ C₂ a hscale hscale1 hR hε hc₁
    hC₁ hN hC₂ hP ha0
    w Dw D2w Dtw hcont hweak hL2 hJ hWP hWQ
  have hmult := mul_le_mul_of_nonneg_left hGlobal
    (show 0 ≤ 4 * c by positivity)
  exact (hCore.trans hAbs').trans hmult

end ESS

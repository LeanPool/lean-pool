/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCompactGapBound

/-!
# Vanishing in the positive phase

The negative-phase estimate forces the shifted field to vanish wherever
the Carleman phase is positive.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The shifted field vanishes in the positive-phase region once its
Gaussian energy densities are integrable at each fixed parameter. -/
theorem bu_short_positive_phase_zero :
    ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ (M scale c₁ C₁ C₂ : ℝ)
        (_hM : 0 < M) (_hscale : 0 < scale) (_hscale1 : scale ≤ 1)
        (_hc₁ : 0 ≤ c₁) (_hC₁ : 0 ≤ C₁)
        (_hN : ∀ scale y : ℝ,
          |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
        (_hC₂ : 0 ≤ C₂)
        (_hP : ∀ x : ℝ,
          |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
        (_hsmall : c * 36 * (c₁ * scale) ^ 2 ≤ 1 / 2)
        (w : ParabolicPoint → Vec3)
        (Dw : ParabolicPoint → Fin 3 → Vec3)
        (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtw : ParabolicPoint → Vec3)
        (_hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
        (_hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
        (_hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
          w Dw D2w Dtw)
        (_hL2 : ∀ S : Set ParabolicPoint,
          S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
          Bornology.IsBounded S →
          (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
            ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
        (_hineq : ∀ᵐ z ∂(volume.restrict
          (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
          vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
            c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
              vec3EuclideanNorm (w z)))
        (_hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
          vec3EuclideanNorm (w z) ≤
            Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
        (_hJ : IntegrableOn (buShortTangentialDensity scale w Dw)
          (buShortWideGapRegion scale) volume)
        (_hWP : ∀ a : ℝ, max a₀ 1 < a →
          IntegrableOn (buShortWeightedPolynomialDensity scale a w Dw)
            (buShortHighStrip scale) volume)
        (_hWQ : ∀ a : ℝ, max a₀ 1 < a →
          IntegrableOn (buShortWeightedDensity scale a w Dw)
            (buShortHighStrip scale) volume)
        (z : ParabolicPoint)
        (_hz : z ∈ buShortPositivePhaseRegion scale),
        buAffineField (-scale ^ 2 / 2) scale w z = 0 := by
  obtain ⟨a₀, c, ha₀, hc, hCompact⟩ := bu_short_compact_mass_le_gap
  refine ⟨a₀, c, ha₀, hc, ?_⟩
  intro M scale c₁ C₁ C₂ hM hscale hscale1 hc₁ hC₁ hN
    hC₂ hP hsmall w Dw D2w Dtw hcont hinit hweak
    hL2 hineq hgrowth hJ hWP hWQ z hz
  obtain ⟨S, hScompact, hzS, hSpositive, hzInterior, _hSpos⟩ :=
    bu_short_positive_compact_neighborhood hz
  have hSgap : ∀ q ∈ S,
      parabolicHomeomorph q ∈ buShortAboveGap scale := by
    intro q hq
    exact buShortPositivePhaseRegion_subset_aboveGap hscale
      (hSpositive hq)
  have hSdomain : S ⊆
      ({x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) 1) := by
    intro q hq
    have hpos := hSpositive hq
    exact ⟨(by norm_num : (0 : ℝ) < 2).trans hpos.1,
      ⟨hpos.2.1.le, hpos.2.2.1⟩⟩
  have hvcont : ContinuousOn
      (buAffineField (-scale ^ 2 / 2) scale w) S :=
    (bu_short_field_continuousOn scale hscale hscale1 w hcont).mono
      hSdomain
  let J : ℝ := ∫ q in buShortWideGapRegion scale,
    buShortTangentialDensity scale w Dw q
    ∂(volume : Measure ParabolicPoint)
  let C : ℝ := 16 * c *
    buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 * J
  have hbound (a : ℝ) (ha : max a₀ 1 < a) :
      (∫ q in S, buShortShiftedWeight scale a q *
        vec3EuclideanNorm
          (buAffineField (-scale ^ 2 / 2) scale w q) ^ 2
        ∂(volume : Measure ParabolicPoint)) ≤
        C * Real.exp (-(a * buShortD scale)) := by
    have h := hCompact M scale c₁ C₁ C₂ a hM hscale hscale1
      hc₁ hC₁ hN hC₂ hP hsmall ha w Dw D2w Dtw
      hcont hinit hweak hL2 hineq hgrowth hJ
      (hWP a ha) (hWQ a ha) S hScompact ⟨z, hzS⟩ hSgap
    convert h using 1
    simp only [C, J]
    ring
  exact bu_short_zero_of_positive_phase_decay scale S hScompact
    hSpositive (buAffineField (-scale ^ 2 / 2) scale w) hvcont
    C (buShortD scale) (max a₀ 1) (buShortD_pos hscale)
    hbound hzInterior

end ESS

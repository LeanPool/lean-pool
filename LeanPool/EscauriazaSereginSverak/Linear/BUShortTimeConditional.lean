/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortFillHalfSpace

/-!
# Short-time vanishing from Gaussian integrability

The compact-set phase estimate and spatial unique continuation give
vanishing on the initial physical time interval.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The short-time conclusion follows from the three Gaussian energy
integrability bounds used to remove the spatial cutoff (`lem:bu-small-time`). -/
theorem bu_short_time_from_integrable_densities :
    ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ (M scale c₁ C₁ C₂ : ℝ)
        (_hM : 0 < M) (_hscale : 0 < scale)
        (_hscaleHalf : scale ≤ 1 / 2)
        (_hc₁ : 0 < c₁) (_hC₁ : 0 ≤ C₁)
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
            (buShortHighStrip scale) volume),
        ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
          0 < t → t < scale ^ 2 / 2 → w (x, t) = 0 := by
  obtain ⟨a₀, c, ha₀, hc, hpositive⟩ := bu_short_positive_phase_zero
  refine ⟨a₀, c, ha₀, hc, ?_⟩
  intro M scale c₁ C₁ C₂ hM hscale hscaleHalf hc₁
    hC₁ hN hC₂ hP hsmall w Dw D2w Dtw
    hcont hinit hweak hL2 hineq hgrowth hJ hWP hWQ
  have hscale1 : scale ≤ 1 := by linarith only [hscaleHalf]
  have hpos : ∀ z ∈ buShortPositivePhaseRegion scale,
      buAffineField (-scale ^ 2 / 2) scale w z = 0 := by
    intro z hz
    exact hpositive M scale c₁ C₁ C₂ hM hscale hscale1
      hc₁.le hC₁ hN hC₂ hP hsmall
      w Dw D2w Dtw hcont hinit hweak hL2 hineq hgrowth
      hJ hWP hWQ z hz
  have hfill := bu_short_fill_halfspace_from_positive M scale c₁
    hscale hscaleHalf hc₁ w Dw D2w Dtw
    hcont hweak hL2 hineq hgrowth hpos
  intro x hx t ht htUpper
  let y : Vec3 := scale⁻¹ • x
  let s : ℝ := 1 / 2 + t / scale ^ 2
  have hsq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hy : 0 < y 2 := by
    change 0 < scale⁻¹ * x 2
    exact mul_pos (inv_pos.mpr hscale) hx
  have hs : 1 / 2 < s := by
    dsimp [s]
    have hdiv : 0 < t / scale ^ 2 := div_pos ht hsq
    linarith only [hdiv]
  have hs1 : s < 1 := by
    have hdiv : t / scale ^ 2 < 1 / 2 :=
      (div_lt_iff₀ hsq).2 (by nlinarith only [htUpper])
    dsimp [s]
    linarith only [hdiv]
  have hvzero := hfill y hy s hs hs1
  have hpoint : buAffinePoint (-scale ^ 2 / 2) scale (y, s) =
      ((x, t) : ParabolicPoint) := by
    apply Prod.ext
    · dsimp [buAffinePoint, y]
      rw [smul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
    · dsimp [buAffinePoint, s]
      field_simp [ne_of_gt hsq]
      ring
  simpa only [buAffineField, hpoint] using hvzero

end ESS

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGaussianCellBridge
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortThreeDensityAverage
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortExtendedGrowth
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGlobalDensities

/-!
# Short-time densities from Gaussian averages

The Gaussian estimate for the physical field controls the three
weighted densities of its short-time affine rescaling.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The physical Gaussian average estimate makes the tangential and
two fixed Carleman densities integrable above the lower normal cutoff
(`lem:bu-small-time`). -/
theorem bu_short_densities_from_gaussian
    (M scale γ C c₁ a : ℝ)
    (hMmax : M ≤ 1 / (10 : ℝ) ^ 12)
    (hMbar : (1 / (10 : ℝ) ^ 12) / 2 ≤ M)
    (hscale : 0 < scale) (hscaleγ : scale ^ 2 ≤ γ)
    (hγsmall : γ < 1 / 12)
    (hC : 0 < C) (hc₁ : 0 < c₁) (ha : 0 ≤ a)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w
      ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo 0 1) w Dw D2w Dtw)
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
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    (hGaussian : ∀ X : Vec3, 2 < X 2 → ∀ t : ℝ,
      0 < t → t < γ →
      Real.rpow t (-(5 / 2 : ℝ)) *
        (∫ z in spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
          (Ioo t (5 * t / 2)),
          vec3EuclideanNorm (w z) ^ 2
            ∂(volume : Measure ParabolicPoint)) ≤
        C * Real.exp (8 * max M ((1 / (10 : ℝ) ^ 12) / 2) *
          vec3EuclideanNorm X ^ 2) *
          Real.exp (-((1 / (10 : ℝ) ^ 6) * X 2 ^ 2 / (12 * t)))) :
    IntegrableOn (buShortTangentialDensity scale w Dw)
      (buShortHighStrip scale) volume ∧
    IntegrableOn (buShortWeightedPolynomialDensity scale a w Dw)
      (buShortHighStrip scale) volume ∧
    IntegrableOn (buShortWeightedDensity scale a w Dw)
      (buShortHighStrip scale) volume := by
  let β : ℝ := 1 / (10 : ℝ) ^ 6
  let G : ℝ := 8 * M * scale ^ 2
  let c : ℝ := c₁ * scale
  have hβ : 0 < β := by dsimp [β]; positivity
  have hscale1 : scale ≤ 1 := by
    have hsq : scale ^ 2 < 1 := by linarith only [hscaleγ, hγsmall]
    nlinarith only [hsq, hscale]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hMscale : M * scale ^ 2 ≤
      (1 / (10 : ℝ) ^ 12) * γ :=
    mul_le_mul hMmax hscaleγ (sq_nonneg scale)
      (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 12)
  have hGsmall : G ≤ 8 * (1 / (10 : ℝ) ^ 12) / 12 := by
    dsimp [G]
    nlinarith only [hMscale, hγsmall]
  have hGtan : G ≤ 1 / 16 := by linarith only [hGsmall]
  have hGnorm : G ≤ β / 48 := by
    dsimp [β]
    linarith only [hGsmall]
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  have hcontV := bu_short_extended_continuousOn scale hscale hscale1
    w hcont
  have hweakV := bu_short_extended_weak_derivatives scale hscale hscale1
    w Dw D2w Dtw hweak
  have hlocalV := bu_short_extended_local_quadratic_l2 M scale
    hscale hscale1 w Dw D2w Dtw hweak hL2 hgrowth
  have hineqV := bu_short_extended_heat_ae_bound scale c₁
    hscale hscale1 hc₁.le w Dw D2w Dtw hineq
  have hAvg (k : ℤ) (hk : 1 ≤ k) (m : Fin 3 → ℤ)
      (ell : Fin 2048)
      (hCell : (buShortShiftedDyadicCell k m ell ∩
        buShortHighStrip scale).Nonempty) :
      let d := Foundation.buSmallTimeDyadicScale k
      let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
      let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
      (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
        ∂(volume : Measure ParabolicPoint)) ≤
          C * d ^ 2 *
          Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
          Real.exp (-(β * Y 2 ^ 2 / (12 * d))) := by
    obtain ⟨z₀, hz₀⟩ := hCell
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let t := scale ^ 2 * δ / 2
    let X := scale • Y
    have hgeom := bu_short_high_cell_geometry scale hscale hscale1
      k hk m ell z₀ hz₀
    have hδhalf : δ < 1 / 2 := hgeom.2.1
    have hX : 2 < X 2 := hgeom.1
    have hδ : 0 < δ :=
      (half_pos (Foundation.buSmallTimeDyadicScale_pos k)).trans
        (bu_short_dyadic_cell_center_time_bounds k m ell).1
    have ht : 0 < t := by dsimp [t]; positivity
    have htγ : t < γ := by
      have hδsmall : δ / 2 < 1 := by linarith only [hδhalf]
      have hmul := mul_lt_mul_of_pos_left hδsmall (sq_pos_of_pos hscale)
      dsimp [t]
      nlinarith only [hmul, hscaleγ]
    have hGaussianCell := hGaussian X hX t ht htγ
    exact bu_short_gaussian_cell_average_bound M scale γ C β
      hscale hscale1 hscaleγ hγsmall hC.le hβ hMbar
      k hk m ell z₀ hz₀ w Dw D2w Dtw hweak hL2 hgrowth
      (by simpa only [β, X, Y, δ, t] using hGaussianCell)
  have hThree := bu_short_three_densities_integrable_of_average
    scale c a β G C hscale hscale1 hc ha hβ hGtan hGnorm
    hC.le hcontV hweakV hlocalV hineqV hAvg
  exact hThree

end ESS

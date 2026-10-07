/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHighStripAverage
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortDensityContinuity
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedCellFactor

/-!
# The three short-time densities from one Gaussian average

The common cell-center Gaussian bound applies to the tangential
factor and both fixed Carleman factors.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Gaussian velocity averages imply integrability of all three
weighted quadratic densities on the high normal strip
(`lem:bu-small-time`). -/
theorem bu_short_three_densities_integrable_of_average
    (scale c a β G Cg : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hβ : 0 < β)
    (hGtan : G ≤ 1 / 16) (hGnorm : G ≤ β / 48)
    (hCg : 0 ≤ Cg)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hcont : ContinuousOn v
      ({x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) (3 / 2)))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)) v Dv D2v Dtv)
    (hlocal : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)))),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (Real.sqrt (spatialGradientSq v Dv z) +
          vec3EuclideanNorm (v z)))
    (hAvg : ∀ (k : ℤ), 1 ≤ k → ∀ (m : Fin 3 → ℤ) (ell : Fin 2048),
      (buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale).Nonempty →
      let d := Foundation.buSmallTimeDyadicScale k
      let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
      let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
      (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
        ∂(volume : Measure ParabolicPoint)) ≤
          Cg * d ^ 2 *
          Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
          Real.exp (-(β * Y 2 ^ 2 / (12 * d)))) :
    let E := fun z => vec3EuclideanNorm (v z) ^ 2 +
      spatialGradientSq v Dv z
    let W₀ := fun z : ParabolicPoint =>
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        (1 + z.1 2) ^ 4
    let W₁ := fun z : ParabolicPoint =>
      buShortShiftedWeight scale a z * (1 + z.1 2) ^ 4
    let W₂ := buShortShiftedWeight scale a
    IntegrableOn (fun z => W₀ z * E z)
      (buShortHighStrip scale) volume ∧
    IntegrableOn (fun z => W₁ z * E z)
      (buShortHighStrip scale) volume ∧
    IntegrableOn (fun z => W₂ z * E z)
      (buShortHighStrip scale) volume := by
  dsimp
  let b := β / 96
  have hb : 0 < b := by dsimp [b]; positivity
  have hbβ : b ≤ β / 48 := by dsimp [b]; linarith only [hβ]
  obtain ⟨Cw, hCw, hFactors⟩ :=
    bu_short_three_cell_factors_bound scale a b hscale ha hb
  have hAll (W : ParabolicPoint → ℝ)
      (hWcont : ContinuousOn W
        {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2})
      (hW0 : ∀ z, 0 ≤ W z)
      (hWbound : ∀ (k : ℤ), 1 ≤ k →
        ∀ (m : Fin 3 → ℤ) (ell : Fin 2048) (z : ParabolicPoint),
        z ∈ buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale →
        W z ≤ Cw * Real.exp (-(((Foundation.buSmallTimeDyadicCellCenter k m ell).1 0) ^ 2 +
          ((Foundation.buSmallTimeDyadicCellCenter k m ell).1 1) ^ 2) / 8) *
          Real.exp (b * ((Foundation.buSmallTimeDyadicCellCenter k m ell).1 2) ^ 2)) :
      IntegrableOn (fun z => W z *
        (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z))
        (buShortHighStrip scale) volume := by
    apply bu_short_high_strip_integrable_of_average scale c b β G Cw Cg
      hscale hscale1 hc hβ hGtan hGnorm hbβ hCw.le hCg
      hcont hweak hlocal hineq hAvg W hWcont
    intro k hk m ell z hz
    exact ⟨hW0 z, hWbound k hk m ell z hz⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hAll _ bu_short_tangential_factor_continuousOn_positive
      (by
        intro z
        exact mul_nonneg (Real.exp_nonneg _)
          (Even.pow_nonneg (by decide : Even 4) _))
      (by
        intro k hk m ell z hz
        exact (hFactors k (by omega : 0 ≤ k) m ell z hz.1 hz.2).1)
  · exact hAll _ (bu_short_shifted_polynomial_factor_continuousOn_positive scale a)
      (by
        intro z
        dsimp [buShortShiftedWeight, buShortCarlemanWeight]
        exact mul_nonneg
          (mul_nonneg (Real.exp_nonneg _)
            (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)))
          (Even.pow_nonneg (by decide : Even 4) _))
      (by
        intro k hk m ell z hz
        exact (hFactors k (by omega : 0 ≤ k) m ell z hz.1 hz.2).2.1)
  · exact hAll _ (bu_short_shifted_factor_continuousOn_positive scale a)
      (by
        intro z
        dsimp [buShortShiftedWeight, buShortCarlemanWeight]
        exact mul_nonneg (Real.exp_nonneg _)
          (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)))
      (by
        intro k hk m ell z hz
        exact (hFactors k (by omega : 0 ≤ k) m ell z hz.1 hz.2).2.2)

end ESS

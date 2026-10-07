/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortMetricAverageIntegrable
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellGeometryApplied

/-!
# One Gaussian estimate on a short-time cell

The physical Gaussian average at a high-strip cell center yields the
normalized dyadic bound used in the cell summation.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The physical Gaussian estimate transfers to a normalized average
at every high-strip cell center (`lem:bu-small-time`). -/
theorem bu_short_gaussian_cell_average_bound
    (M scale γ C β : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hscaleγ : scale ^ 2 ≤ γ) (hγ : γ < 1 / 12)
    (hC : 0 ≤ C) (hβ : 0 < β)
    (hMbar : (1 / (10 : ℝ) ^ 12) / 2 ≤ M)
    (k : ℤ) (hk : 1 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (z₀ : ParabolicPoint)
    (hz₀ : z₀ ∈ buShortShiftedDyadicCell k m ell ∩
      buShortHighStrip scale)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    (hGaussian :
      let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
      let X := scale • Y
      let t := scale ^ 2 * δ / 2
      Real.rpow t (-(5 / 2 : ℝ)) *
        (∫ z in spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
          (Ioo t (5 * t / 2)),
          vec3EuclideanNorm (w z) ^ 2
            ∂(volume : Measure ParabolicPoint)) ≤
        C * Real.exp (8 * max M ((1 / (10 : ℝ) ^ 12) / 2) *
          vec3EuclideanNorm X ^ 2) *
          Real.exp (-(β * X 2 ^ 2 / (12 * t)))) :
    let d := Foundation.buSmallTimeDyadicScale k
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
    (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
      ∂(volume : Measure ParabolicPoint)) ≤
        C * d ^ 2 *
        Real.exp ((8 * M * scale ^ 2) *
          (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * Y 2 ^ 2 / (12 * d))) := by
  dsimp
  let d := Foundation.buSmallTimeDyadicScale k
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  let X := scale • Y
  let t := scale ^ 2 * δ / 2
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hd1 : d ≤ 1 := by
    dsimp [d, Foundation.buSmallTimeDyadicScale]
    exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2)
      (neg_nonpos.mpr (by omega : 0 ≤ k))
  have hδd : δ ≤ d :=
    (bu_short_dyadic_cell_center_time_bounds k m ell).2.le
  have hδ : 0 < δ :=
    (half_pos hd).trans (bu_short_dyadic_cell_center_time_bounds k m ell).1
  have hX : 2 < X 2 :=
    (bu_short_high_cell_geometry scale hscale hscale1
      k hk m ell z₀ hz₀).1
  have ht : 0 < t := by dsimp [t]; positivity
  have htγ : t < γ := by
    have hδsmall : δ / 2 < 1 := by
      have hδhalf := (bu_short_high_cell_geometry scale hscale hscale1
        k hk m ell z₀ hz₀).2.1
      linarith only [hδhalf]
    have hmul := mul_lt_mul_of_pos_left hδsmall (sq_pos_of_pos hscale)
    dsimp [t]
    nlinarith only [hmul, hscaleγ]
  have htsmall : t < 1 / 12 := htγ.trans hγ
  have hMetricInt := bu_short_metric_average_integrable M X t hX
    ht htsmall w Dw D2w Dtw hweak hL2 hgrowth
  have hR : Real.sqrt (3 * t) =
      scale * Real.sqrt (3 * δ / 2) :=
    bu_short_physical_average_radius scale δ hscale
  have hEuclidInt : IntegrableOn
      (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet
        (vec3Ball X (scale * Real.sqrt (3 * δ / 2)))
        (Ioo (scale ^ 2 * δ / 2) (5 * scale ^ 2 * δ / 4))) volume := by
    have hSub : spaceTimeSet
        (vec3Ball X (scale * Real.sqrt (3 * δ / 2)))
        (Ioo (scale ^ 2 * δ / 2) (5 * scale ^ 2 * δ / 4)) ⊆
        spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
          (Ioo t (5 * t / 2)) := by
      intro z hz
      rw [hR]
      have htime : z.2 ∈ Ioo t (5 * t / 2) := by
        dsimp [t]
        convert hz.2 using 1
        ring_nf
      exact ⟨CKN.vec3Ball_subset_ball X _ hz.1, htime⟩
    exact hMetricInt.mono_set hSub
  have hFm := hEuclidInt.aestronglyMeasurable
  have hEuclidLe := bu_short_euclidean_average_le_metric X t ht w hMetricInt
  have hMax : max M ((1 / (10 : ℝ) ^ 12) / 2) = M :=
    max_eq_left hMbar
  have hPhysical : Real.rpow t (-(5 / 2 : ℝ)) *
      (∫ z in spaceTimeSet
        (vec3Ball X (scale * Real.sqrt (3 * δ / 2)))
        (Ioo t (5 * t / 2)),
        vec3EuclideanNorm (w z) ^ 2
          ∂(volume : Measure ParabolicPoint)) ≤
        C * Real.exp (8 * M * vec3EuclideanNorm X ^ 2) *
          Real.exp (-(β * X 2 ^ 2 / (12 * t))) := by
    rw [← hR, ← hMax]
    exact hEuclidLe.trans hGaussian
  exact bu_short_normalized_average_bound scale β M C δ d Y
    hscale hβ hC hδ hδd hd1 w hFm hPhysical

end ESS

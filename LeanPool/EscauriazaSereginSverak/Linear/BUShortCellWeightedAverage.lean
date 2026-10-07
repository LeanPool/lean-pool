/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellGeometryApplied
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellEnergyApplied
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellFactor
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellWeightedIntegral

/-!
# A high-strip cell bound from its velocity average

Caccioppoli controls the full quadratic energy by the velocity average;
a bounded scalar factor then multiplies the estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A fixed nonnegative weight on a high-strip cell is bounded by the
Gaussian velocity average with one inverse dyadic factor
(`lem:bu-small-time`). -/
theorem bu_short_cell_weighted_average_bound
    (scale c b Cw : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hc : 0 ≤ c) (hCw : 0 ≤ Cw)
    (k : ℤ) (hk : 1 ≤ k) (m : Fin 3 → ℤ) (ell : Fin 2048)
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
    (W : ParabolicPoint → ℝ)
    (hWcont : ContinuousOn W
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2})
    (hW : ∀ z ∈ buShortShiftedDyadicCell k m ell ∩
      buShortHighStrip scale,
      0 ≤ W z ∧
        W z ≤ Cw *
          Real.exp (-(((Foundation.buSmallTimeDyadicCellCenter k m ell).1 0) ^ 2 +
            ((Foundation.buSmallTimeDyadicCellCenter k m ell).1 1) ^ 2) / 8) *
          Real.exp (b * ((Foundation.buSmallTimeDyadicCellCenter k m ell).1 2) ^ 2))
    (z₀ : ParabolicPoint)
    (hz₀ : z₀ ∈ buShortShiftedDyadicCell k m ell ∩
      buShortHighStrip scale) :
    let d := Foundation.buSmallTimeDyadicScale k
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
    let Ce := 1 + 256 * (1 + c ^ 2 + 128)
    (∫ z in buShortShiftedDyadicCell k m ell ∩
      buShortHighStrip scale,
      W z * (vec3EuclideanNorm (v z) ^ 2 +
        spatialGradientSq v Dv z) ∂(volume : Measure ParabolicPoint)) ≤
      (Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
        Real.exp (b * Y 2 ^ 2)) *
        (Ce / d) *
        (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint)) := by
  dsimp
  let d := Foundation.buSmallTimeDyadicScale k
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  let r := Real.sqrt δ / 8
  let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
    (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
  let Cell := buShortShiftedDyadicCell k m ell
  let S := Cell ∩ buShortHighStrip scale
  let E := fun z => vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  let B := Cw * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
    Real.exp (b * Y 2 ^ 2)
  let Ce := 1 + 256 * (1 + c ^ 2 + 128)
  have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos k
  have hd1 : d ≤ 1 := by
    dsimp [d, Foundation.buSmallTimeDyadicScale]
    exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2)
      (neg_nonpos.mpr (by omega : 0 ≤ k))
  have hδlower := (bu_short_dyadic_cell_center_time_bounds k m ell).1
  have hδ : 0 < δ := (half_pos hd).trans hδlower
  obtain ⟨_hY, hδhalf, hAvgBall, hInnerBall⟩ :=
    bu_short_high_cell_geometry scale hscale hscale1 k hk m ell z₀ hz₀
  have hAvgSub := bu_short_average_box_subset_extended Y δ hδ hδhalf hAvgBall
  have hAvgBound := bu_short_average_box_bounded Y δ hδ
  have hInts := bu_short_extended_energy_integrable_on hweak hlocal
    Avg hAvgSub hAvgBound
  have hCellSub : Cell ⊆ Avg := bu_short_shifted_dyadic_cell_average k m ell
  have hEInt : IntegrableOn E Cell volume :=
    (hInts.1.add hInts.2).mono_set hCellSub
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hEWInt : IntegrableOn (fun z => W z * E z) S volume := by
    apply bu_short_cell_fragment_density_integrable scale hscale k m ell
      hweak hlocal W hWcont B
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hW z hz).1]
    exact (hW z hz).2
  have hE0 (z : ParabolicPoint) : 0 ≤ E z := by
    dsimp [E, spatialGradientSq]
    positivity
  have hWeighted := bu_short_weighted_energy_cell_le Cell
    (buShortHighStrip scale)
    (bu_short_shifted_dyadic_cell_measurable k m ell)
    (buShortHighStrip_measurable scale)
    E W B hB hEInt hEWInt hE0 hW
  have hEnergy := bu_short_shifted_cell_energy_bound k m ell c hc
    hδhalf hInnerBall hAvgBall hcont hweak hlocal hineq
  have hFactor := bu_short_cell_energy_factor_le d δ c hd hd1 hδlower
  have hAvg0 : 0 ≤ ∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
      ∂(volume : Measure ParabolicPoint) := by
    apply integral_nonneg
    intro z
    positivity
  have hEnergy' : (∫ z in Cell, E z ∂(volume : Measure ParabolicPoint)) ≤
      Ce / d * (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
        ∂(volume : Measure ParabolicPoint)) := by
    calc
      _ ≤ (1 + 256 * (1 + c ^ 2 + 1 / r ^ 2)) *
          (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2 ∂volume) := hEnergy
      _ ≤ Ce / d * _ := mul_le_mul_of_nonneg_right hFactor hAvg0
  calc
    _ ≤ B * (∫ z in Cell, E z ∂(volume : Measure ParabolicPoint)) := hWeighted
    _ ≤ B * (Ce / d * (∫ z in Avg,
        vec3EuclideanNorm (v z) ^ 2 ∂volume)) :=
      mul_le_mul_of_nonneg_left hEnergy' hB
    _ = _ := by ring

end ESS

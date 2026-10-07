/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellEnergy
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageBox
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageGradient

/-!
# Local energy bound on a short-time dyadic cell

The extended rescaled weak heat equation and the Caccioppoli estimate
control each shifted cell by one Gaussian velocity average.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A short-time dyadic cell's energy is bounded by its Gaussian
velocity average (`lem:bu-small-time`). -/
theorem bu_short_shifted_cell_energy_bound
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
    (c : ℝ) (hc : 0 ≤ c)
    (hδhalf : (Foundation.buSmallTimeDyadicCellCenter k m ell).2 < 1 / 2)
    (hball : vec3Ball
      (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      (2 * (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8)) ⊆
      {x : Vec3 | 0 < x 2})
    (havgBall : vec3Ball
      (Foundation.buSmallTimeDyadicCellCenter k m ell).1
      (Real.sqrt (3 * (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 2)) ⊆
      {x : Vec3 | 0 < x 2})
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
          vec3EuclideanNorm (v z))) :
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let r := Real.sqrt δ / 8
    let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
    (∫ z in buShortShiftedDyadicCell k m ell,
      vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
        ∂(volume : Measure ParabolicPoint)) ≤
      (1 + 256 * (1 + c ^ 2 + 1 / r ^ 2)) *
        (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
          ∂(volume : Measure ParabolicPoint)) := by
  dsimp
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let r := Real.sqrt δ / 8
  let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
    (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
  let Inner := spaceTimeSet (vec3Ball Y r)
    (Ioo (1 / 2 + δ - r ^ 2 / 2)
      (1 / 2 + δ - r ^ 2 / 2 + r ^ 2))
  have hd : 0 < Foundation.buSmallTimeDyadicScale k :=
    Foundation.buSmallTimeDyadicScale_pos k
  have hδ : 0 < δ :=
    (half_pos hd).trans (bu_short_dyadic_cell_center_time_bounds k m ell).1
  have hAvgSub := bu_short_average_box_subset_extended Y δ hδ hδhalf havgBall
  have hAvgBound := bu_short_average_box_bounded Y δ hδ
  have hInts := bu_short_extended_energy_integrable_on hweak hlocal
    Avg hAvgSub hAvgBound
  have hInnerAvg : Inner ⊆ Avg := bu_short_inner_subset_average Y δ hδ
  have hGradInt : IntegrableOn (spatialGradientSq v Dv) Inner volume :=
    hInts.2.mono_set hInnerAvg
  have hCacc := bu_short_average_gradient_bound Y δ c hδ hδhalf hc
    hball havgBall hcont hweak hlocal hineq
  exact bu_short_shifted_cell_energy_le_average k m ell
    (256 * (1 + c ^ 2 + 1 / r ^ 2)) v Dv hInts.1 hGradInt hCacc

end ESS

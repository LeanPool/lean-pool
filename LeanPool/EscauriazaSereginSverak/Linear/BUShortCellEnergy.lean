/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellAverage
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGlobalDensities

/-!
# Energy on shifted dyadic cells

The energy of each shifted cell is bounded by the Gaussian velocity
average and the local Caccioppoli estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Combining the local gradient estimate with containment of a
dyadic cell in its averaging box bounds its quadratic energy
(`lem:bu-small-time`). -/
theorem bu_short_shifted_cell_energy_le_average
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) (C : ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hAvgInt : IntegrableOn
      (fun z => vec3EuclideanNorm (v z) ^ 2)
      (spaceTimeSet
        (vec3Ball (Foundation.buSmallTimeDyadicCellCenter k m ell).1
          (Real.sqrt (3 * (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 2)))
        (Ioo (1 / 2 + (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 2)
          (1 / 2 + 5 * (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 4)))
      volume)
    (hGradInt : IntegrableOn (spatialGradientSq v Dv)
      (spaceTimeSet
        (vec3Ball (Foundation.buSmallTimeDyadicCellCenter k m ell).1
          (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8))
        (Ioo (1 / 2 + (Foundation.buSmallTimeDyadicCellCenter k m ell).2 -
            (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8) ^ 2 / 2)
          (1 / 2 + (Foundation.buSmallTimeDyadicCellCenter k m ell).2 -
              (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8) ^ 2 / 2 +
              (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8) ^ 2)))
      volume)
    (hCacc :
      (∫ z in spaceTimeSet
        (vec3Ball (Foundation.buSmallTimeDyadicCellCenter k m ell).1
          (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8))
        (Ioo (1 / 2 + (Foundation.buSmallTimeDyadicCellCenter k m ell).2 -
            (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8) ^ 2 / 2)
          (1 / 2 + (Foundation.buSmallTimeDyadicCellCenter k m ell).2 -
              (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8) ^ 2 / 2 +
              (Real.sqrt (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 8) ^ 2)),
        spatialGradientSq v Dv z ∂(volume : Measure ParabolicPoint)) ≤
      C * (∫ z in spaceTimeSet
        (vec3Ball (Foundation.buSmallTimeDyadicCellCenter k m ell).1
          (Real.sqrt (3 * (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 2)))
        (Ioo (1 / 2 + (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 2)
          (1 / 2 + 5 * (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 4)),
        vec3EuclideanNorm (v z) ^ 2 ∂(volume : Measure ParabolicPoint))) :
    (∫ z in buShortShiftedDyadicCell k m ell,
      vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
        ∂(volume : Measure ParabolicPoint)) ≤
      (1 + C) * (∫ z in spaceTimeSet
        (vec3Ball (Foundation.buSmallTimeDyadicCellCenter k m ell).1
          (Real.sqrt (3 * (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 2)))
        (Ioo (1 / 2 + (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 2)
          (1 / 2 + 5 * (Foundation.buSmallTimeDyadicCellCenter k m ell).2 / 4)),
        vec3EuclideanNorm (v z) ^ 2 ∂(volume : Measure ParabolicPoint)) := by
  let Cell := buShortShiftedDyadicCell k m ell
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  let r := Real.sqrt δ / 8
  let Inner := spaceTimeSet (vec3Ball Y r)
    (Ioo (1 / 2 + δ - r ^ 2 / 2) (1 / 2 + δ - r ^ 2 / 2 + r ^ 2))
  let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
    (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
  have hCellInner : Cell ⊆ Inner := bu_short_shifted_dyadic_cell_inner k m ell
  have hCellAvg : Cell ⊆ Avg := bu_short_shifted_dyadic_cell_average k m ell
  have hVI : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2) Cell volume :=
    hAvgInt.mono_set hCellAvg
  have hGI : IntegrableOn (spatialGradientSq v Dv) Cell volume :=
    hGradInt.mono_set hCellInner
  have hVle :
      (∫ z in Cell, vec3EuclideanNorm (v z) ^ 2 ∂volume) ≤
        ∫ z in Avg, vec3EuclideanNorm (v z) ^ 2 ∂volume := by
    apply setIntegral_mono_set hAvgInt
    · filter_upwards [] with z
      exact sq_nonneg _
    · exact ae_of_all _ hCellAvg
  have hGle :
      (∫ z in Cell, spatialGradientSq v Dv z ∂volume) ≤
        ∫ z in Inner, spatialGradientSq v Dv z ∂volume := by
    apply setIntegral_mono_set hGradInt
    · filter_upwards [] with z
      unfold spatialGradientSq
      positivity
    · exact ae_of_all _ hCellInner
  rw [integral_add hVI hGI]
  calc
    _ ≤ (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2 ∂volume) +
        (∫ z in Inner, spatialGradientSq v Dv z ∂volume) :=
          add_le_add hVle hGle
    _ ≤ (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2 ∂volume) +
        C * (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2 ∂volume) :=
          add_le_add_right hCacc _
    _ = (1 + C) * (∫ z in Avg,
          vec3EuclideanNorm (v z) ^ 2 ∂volume) := by ring

end ESS

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeDirichletContinuousKNormalizedEnergy
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeDirichletContinuousKSmallOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Small-order normalized continuous K-energy

The expansion factor in the normalized quadratic estimate is fixed by the
dimension.  Continuity of real powers at order zero then selects one positive
fractional order, before the datum and solution, for which the exact loss is
strictly below `101/100`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem exists_fractionalOrder_normalizedContinuousKFactor_lt
    {A : ℝ} (hA : 0 < A) :
    ∃ s : FractionalOrder,
      s.1 < (1 : ℝ) / 12 ∧
        (ENNReal.ofReal A) ^ (2 * s.1) <
          ENNReal.ofReal ((101 : ℝ) / 100) := by
  let target : ℝ := (101 : ℝ) / 100
  have honeTarget : (1 : ℝ) < target := by
    norm_num [target]
  have htargetPos : 0 < target := zero_lt_one.trans honeTarget
  have hcontinuous : Continuous (fun sigma : ℝ => Real.rpow A (2 * sigma)) :=
    (Real.continuous_const_rpow hA.ne').comp
      (continuous_const.mul continuous_id)
  have htendsto :
      Filter.Tendsto (fun sigma : ℝ => Real.rpow A (2 * sigma))
        (nhds 0) (nhds 1) := by
    have hcontinuousAt :
        ContinuousAt (fun sigma : ℝ => Real.rpow A (2 * sigma)) 0 :=
      hcontinuous.continuousAt
    change Filter.Tendsto (fun sigma : ℝ => Real.rpow A (2 * sigma))
      (nhds 0) (nhds (Real.rpow A (2 * 0))) at hcontinuousAt
    have hzero : Real.rpow A (0 : ℝ) = 1 := by
      change A ^ (0 : ℝ) = 1
      exact Real.rpow_zero A
    rw [show (2 : ℝ) * 0 = 0 by norm_num, hzero] at hcontinuousAt
    exact hcontinuousAt
  have heventuallyFactor :
      ∀ᶠ sigma in nhds 0, Real.rpow A (2 * sigma) < target :=
    htendsto.eventually (Iio_mem_nhds honeTarget)
  have heventuallyFactorRight :
      ∀ᶠ sigma in 𝓝[>] (0 : ℝ), Real.rpow A (2 * sigma) < target :=
    heventuallyFactor.filter_mono inf_le_left
  have heventuallyRange :
      ∀ᶠ sigma in 𝓝[>] (0 : ℝ), sigma ∈ Set.Ioo 0 ((1 : ℝ) / 12) :=
    Ioo_mem_nhdsGT (by norm_num)
  rcases (heventuallyFactorRight.and heventuallyRange).exists with
    ⟨sigma, hfactorReal, hsigma⟩
  let s : FractionalOrder :=
    ⟨sigma, hsigma.1, hsigma.2.trans (by norm_num)⟩
  refine ⟨s, by simpa only [s] using hsigma.2, ?_⟩
  have hofRealFactor :
      ENNReal.ofReal (Real.rpow A (2 * sigma)) < ENNReal.ofReal target :=
    (ENNReal.ofReal_lt_ofReal_iff htargetPos).2 hfactorReal
  have hpow :
      (ENNReal.ofReal A) ^ (2 * sigma) =
        ENNReal.ofReal (Real.rpow A (2 * sigma)) :=
    ENNReal.ofReal_rpow_of_pos hA
  simpa only [s, target, hpow] using hofRealFactor

/-- For each positive dimension, one expansion factor and one fractional
order below `1/12` can be fixed before the analytic inputs so that the exact
normalized continuous `K`-energy loss is strictly below `101/100`. -/
theorem exists_unitCubeDirichletContinuousKNormalizedEnergySmallOrder
    (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∃ s : FractionalOrder,
        s.1 < (1 : ℝ) / 12 ∧
          (ENNReal.ofReal A) ^ (2 * s.1) <
            ENNReal.ofReal ((101 : ℝ) / 100) ∧
          ∀ (h : UnitCubeEuclideanL2Field d)
            (w : H10Function (openCubeSet (originCube d 0))),
            CubeDirichletDivergenceProblem (originCube d 0) w h →
              ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
                    (2 : ℝ≥0∞) (unitCubeGradientEuclideanL2Field w)) ^ 2 +
                  ENNReal.ofReal (2 * s.1) *
                    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
                      continuousKSeminormIntegrand s.1
                        (unitCubeGradientEuclideanL2Field w) t) ≤
                (ENNReal.ofReal A) ^ (2 * s.1) *
                  (((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
                        (2 : ℝ≥0∞) h) ^ 2 +
                    ENNReal.ofReal (2 * s.1) *
                      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
                        continuousKSeminormIntegrand s.1 h t) := by
  rcases exists_unitCubeDirichletContinuousKNormalizedEnergyBound d with
    ⟨A, honeA, hbound⟩
  rcases exists_fractionalOrder_normalizedContinuousKFactor_lt
      (zero_lt_one.trans_le honeA) with ⟨s, hs, hfactor⟩
  exact ⟨A, honeA, s, hs, hfactor, hbound s⟩

end

end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.Sklar.Continuous
import LeanPool.Copula.Sklar.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-! # Sklar's theorem for arbitrary real marginals

A strictly increasing embedding moves the joint law to the compact unit cube.
Quantile lifting there supplies a copula even when the marginals have atoms.
Uniqueness on marginal CDF ranges is `IsSklarCopula.cdf_eq_on_ranges`.
-/

public section

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Every probability law on real vectors admits a Sklar copula. -/
theorem exists_sklarCopula (μ : ProbabilityMeasure (Fin d → ℝ)) :
    ∃ C : Copula d, IsSklarCopula μ C := by
  let T : (Fin d → ℝ) → Fin d → I := fun x i => unitInterval.sigmoid (x i)
  have hT : Measurable T := Measurable.of_eval fun i =>
    unitInterval.continuous_sigmoid.measurable.comp (measurable_pi_apply i)
  let ν : ProbabilityMeasure (Fin d → I) := μ.map T
  have hm (i : Fin d) : ν.toMeasure.map (fun z => z i) =
      (marginal μ i).map unitInterval.sigmoid := by
    change (μ.toMeasure.map T).map (fun z => z i) = _
    rw [Measure.map_map (measurable_pi_apply i) hT]
    exact (Measure.map_map unitInterval.continuous_sigmoid.measurable
      (measurable_pi_apply i)).symm
  have hF (i : Fin d) (x : ℝ) : unitMarginalCDF ν i (unitInterval.sigmoid x) =
      cdfUnit (marginal μ i) x := by
    apply Subtype.ext
    change (ν.toMeasure.map (fun z => z i)).real (Iic (unitInterval.sigmoid x)) =
      ProbabilityTheory.cdf (marginal μ i) x
    rw [hm, map_measureReal_apply unitInterval.continuous_sigmoid.measurable measurableSet_Iic]
    have he : unitInterval.sigmoid ⁻¹' Iic (unitInterval.sigmoid x) = Iic x := by
      ext y
      exact unitInterval.sigmoid_strictMono.le_iff_le
    rw [he, ProbabilityTheory.cdf_eq_real]
  obtain ⟨C, hC⟩ := exists_sklarCopula_unit ν
  refine ⟨C, fun x => ?_⟩
  have he : T ⁻¹' Iic (T x) = Iic x := by
    ext z
    change (∀ i, unitInterval.sigmoid (z i) ≤ unitInterval.sigmoid (x i)) ↔ ∀ i, z i ≤ x i
    exact forall_congr' fun _ => unitInterval.sigmoid_strictMono.le_iff_le
  have hfx : (fun i => unitMarginalCDF ν i (T x i)) = marginalTransform μ x :=
    funext fun i => hF i (x i)
  rw [← hfx, hC]
  change (μ.toMeasure.map T).real (Iic (T x)) = _
  rw [map_measureReal_apply hT measurableSet_Iic, he]

end ProbabilityTheory.Copula

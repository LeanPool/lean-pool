/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.CDF
import LeanPool.Copula.Distribution.Quantile
import LeanPool.Copula.Sklar.Lift

/-! # Sklar's theorem for arbitrary laws on the unit cube -/

public section

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The coordinate CDF of a law on the unit cube, with its range bundled in `[0,1]`. -/
@[expose]
noncomputable def unitMarginalCDF (μ : ProbabilityMeasure (Fin d → I)) (i : Fin d) (x : I) : I :=
  ⟨(μ.toMeasure.map (fun z => z i)).real (Iic x), measureReal_nonneg, measureReal_le_one⟩

/-- Every joint law on the unit cube has a Sklar copula, including laws with atoms. -/
theorem exists_sklarCopula_unit (μ : ProbabilityMeasure (Fin d → I)) :
    ∃ C : Copula d, ∀ x : Fin d → I,
      C.cdf (fun i => unitMarginalCDF μ i (x i)) = μ.toMeasure.real (Iic x) := by
  let q : Fin d → I → I := fun i => unitQuantile (μ.toMeasure.map (fun z => z i))
  have hq (i : Fin d) : Measurable (q i) := measurable_unitQuantile _
  obtain ⟨C, hC⟩ := exists_lift μ q hq (fun i => map_unitQuantile _)
  refine ⟨C, fun x => ?_⟩
  have hm : Measurable (fun u : Fin d → I => fun i => q i (u i)) :=
    Measurable.of_eval fun i => (hq i).comp (measurable_pi_apply i)
  have he : (fun u : Fin d → I => fun i => q i (u i)) ⁻¹' Iic x =
      Iic (fun i => unitMarginalCDF μ i (x i)) := by
    ext u
    change (∀ i, q i (u i) ≤ x i) ↔ ∀ i, u i ≤ unitMarginalCDF μ i (x i)
    exact forall_congr' fun i => unitQuantile_le_iff _ _ _
  rw [cdf, ← hC, map_measureReal_apply hm measurableSet_Iic, he]

end ProbabilityTheory.Copula

/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.CDF

/-!
# Fréchet–Hoeffding bounds

Every copula lies between the lower bound `max 0 (∑ i, u i - d + 1)` and the
minimum coordinate. The upper bound uses an infimum in the unit interval, so
its value in dimension zero is one. These are bounds on the CDF; the lower
bound does not in general define a copula in dimensions greater than two.
-/

public section

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The untruncated lower Fréchet–Hoeffding bound, obtained from the union bound. -/
theorem sum_sub_dim_add_one_le_cdf (C : Copula d) (u : Fin d → I) :
    (∑ i, (u i : ℝ)) - d + 1 ≤ C.cdf u := by
  have hcomp : (Iic u)ᶜ = ⋃ i, {x | u i < x i} := by
    ext x
    simp [mem_Iic, Pi.le_def, not_forall, not_le]
  have hcoord (i : Fin d) : C.toMeasure.real {x | u i < x i} = 1 - (u i : ℝ) := by
    change (C.toMeasure ((fun x => x i) ⁻¹' Ioi (u i))).toReal = _
    rw [C.measure_preimage_eval i measurableSet_Ioi, unitInterval.volume_Ioi,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (u i).property.2)]
  have hunion := measureReal_iUnion_fintype_le (μ := C.toMeasure)
    (fun i : Fin d => {x | u i < x i})
  rw [← hcomp, measureReal_compl measurableSet_Iic, probReal_univ] at hunion
  simp_rw [hcoord] at hunion
  have h : 1 - C.cdf u ≤ (d : ℝ) - ∑ i, (u i : ℝ) := by
    simpa [cdf, Finset.sum_sub_distrib] using hunion
  linarith

/-- The lower Fréchet–Hoeffding bound, including dimension zero. -/
theorem frechet_lower_le_cdf (C : Copula d) (u : Fin d → I) :
    max 0 ((∑ i, (u i : ℝ)) - d + 1) ≤ C.cdf u :=
  max_le (C.cdf_nonneg u) (C.sum_sub_dim_add_one_le_cdf u)

/-- The upper Fréchet–Hoeffding bound, with the empty infimum equal to one. -/
theorem cdf_le_frechet_upper (C : Copula d) (u : Fin d → I) :
    C.cdf u ≤ ((⨅ i, u i : I) : ℝ) := by
  have h : (⟨C.cdf u, C.cdf_nonneg u, C.cdf_le_one u⟩ : I) ≤ ⨅ i, u i :=
    le_iInf fun i => C.cdf_le_coord u i
  exact h

end ProbabilityTheory.Copula

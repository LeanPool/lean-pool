/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.CDF

/-!
# Lipschitz continuity of copula distribution functions

The difference between two lower orthants is contained in a union of coordinate
strips. Uniform marginals bound the mass of each strip by its length. This gives
the sharp Lipschitz bound for the sum of coordinate distances. With the default
maximum metric on the cube, the resulting Lipschitz constant is `d`.
-/

public section

open MeasureTheory Set
open scoped unitInterval BigOperators NNReal

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- A one-sided version of the Lipschitz estimate for the sum metric. -/
theorem cdf_sub_le_sum_abs (C : Copula d) (u v : Fin d → I) :
    C.cdf u - C.cdf v ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by
  let strip (i : Fin d) : Set (Fin d → I) :=
    (fun x => x i) ⁻¹' uIoc (v i) (u i)
  have hsub : Iic u \ Iic v ⊆ ⋃ i, strip i := by
    intro x hx
    obtain ⟨i, hi⟩ := not_forall.mp hx.2
    refine mem_iUnion.mpr ⟨i, ?_⟩
    exact mem_uIoc.mpr (Or.inl ⟨lt_of_not_ge hi, hx.1 i⟩)
  have hstrip (i : Fin d) : C.toMeasure.real (strip i) = |(u i : ℝ) - (v i : ℝ)| := by
    change (C.toMeasure ((fun x => x i) ⁻¹' uIoc (v i) (u i))).toReal = _
    rw [C.measure_preimage_eval i measurableSet_uIoc, unitInterval.volume_uIoc,
      edist_dist, ENNReal.toReal_ofReal dist_nonneg, Subtype.dist_eq, Real.dist_eq]
  calc
    C.cdf u - C.cdf v ≤ C.toMeasure.real (Iic u \ Iic v) := le_measureReal_sdiff
    _ ≤ C.toMeasure.real (⋃ i, strip i) := measureReal_mono hsub
    _ ≤ ∑ i, C.toMeasure.real (strip i) := measureReal_iUnion_fintype_le strip
    _ = ∑ i, |(u i : ℝ) - (v i : ℝ)| := Finset.sum_congr rfl (fun i _ => hstrip i)

/-- A copula CDF is 1-Lipschitz for the sum of coordinate distances. -/
theorem abs_cdf_sub_le_sum_abs (C : Copula d) (u v : Fin d → I) :
    |C.cdf u - C.cdf v| ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by
  refine abs_le.mpr ⟨?_, C.cdf_sub_le_sum_abs u v⟩
  have h : C.cdf v - C.cdf u ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by
    simpa only [abs_sub_comm] using C.cdf_sub_le_sum_abs v u
  linarith

/-- For Lean's default maximum metric on the cube, the Lipschitz constant is `d`. -/
theorem lipschitzWith_cdf (C : Copula d) : LipschitzWith (d : ℝ≥0) C.cdf := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  calc
    dist (C.cdf u) (C.cdf v) = |C.cdf u - C.cdf v| := Real.dist_eq _ _
    _ ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := C.abs_cdf_sub_le_sum_abs u v
    _ ≤ ∑ _ : Fin d, dist u v := Finset.sum_le_sum fun i _ => by
      simpa [Subtype.dist_eq, Real.dist_eq] using dist_le_pi_dist u v i
    _ = (d : ℝ≥0) * dist u v := by simp

/-- Copula CDFs are uniformly continuous on the cube. -/
theorem uniformContinuous_cdf (C : Copula d) : UniformContinuous C.cdf :=
  C.lipschitzWith_cdf.uniformContinuous

/-- Copula CDFs are continuous on the cube. -/
@[fun_prop]
theorem continuous_cdf (C : Copula d) : Continuous C.cdf :=
  C.lipschitzWith_cdf.continuous

end ProbabilityTheory.Copula

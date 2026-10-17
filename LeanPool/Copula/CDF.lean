/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.Basic

/-!
# The distribution function of a copula

The CDF is the real-valued mass of a lower orthant. The pointwise order on the
cube lets us use `Set.Iic` directly. Groundedness requires a coordinate; in
dimension zero the CDF is identically one.
-/

public section

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The distribution function of a copula on the unit cube. -/
@[expose]
noncomputable def cdf (C : Copula d) (u : Fin d → I) : ℝ :=
  C.toMeasure.real (Iic u)

theorem cdf_nonneg (C : Copula d) (u : Fin d → I) : 0 ≤ C.cdf u :=
  measureReal_nonneg

theorem cdf_le_one (C : Copula d) (u : Fin d → I) : C.cdf u ≤ 1 :=
  measureReal_le_one

/-- The copula CDF is monotone in the pointwise order. -/
theorem monotone_cdf (C : Copula d) : Monotone C.cdf := by
  intro u v huv
  exact measureReal_mono (Iic_subset_Iic.mpr huv)

@[simp]
theorem cdf_one (C : Copula d) : C.cdf (fun _ => 1) = 1 := by
  have h : Iic (fun _ : Fin d => (1 : I)) = univ := by
    ext x
    simp [mem_Iic, Pi.le_def, unitInterval.le_one']
  simp [cdf, h]

/-- Every coordinate is an upper bound for the CDF. -/
theorem cdf_le_coord (C : Copula d) (u : Fin d → I) (i : Fin d) :
    C.cdf u ≤ (u i : ℝ) := by
  calc
    C.cdf u ≤ C.toMeasure.real {x | x i ≤ u i} :=
      measureReal_mono (fun _ hx => hx i)
    _ = (u i : ℝ) := C.measureReal_eval_le i (u i)

/-- A lower orthant with a zero coordinate has zero mass. -/
theorem cdf_eq_zero_of_coord_eq_zero (C : Copula d) (u : Fin d → I)
    (i : Fin d) (hi : u i = 0) : C.cdf u = 0 := by
  apply le_antisymm _ (C.cdf_nonneg u)
  simpa [hi] using C.cdf_le_coord u i

@[simp]
theorem cdf_zero (C : Copula d) [NeZero d] : C.cdf (fun _ => 0) = 0 :=
  C.cdf_eq_zero_of_coord_eq_zero _ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ rfl

/-- With all other coordinates equal to one, the CDF is the remaining coordinate. -/
@[simp]
theorem cdf_update_one (C : Copula d) (i : Fin d) (u : I) :
    C.cdf (Function.update (fun _ => 1) i u) = (u : ℝ) := by
  have h : Iic (Function.update (fun _ : Fin d => (1 : I)) i u) =
      {x | x i ≤ u} := by
    ext x
    constructor
    · intro hx
      simpa using hx i
    · intro hx j
      by_cases hji : j = i
      · subst j
        simpa using hx
      · simpa [Function.update_of_ne hji] using (unitInterval.le_one' (t := x j))
  rw [cdf, h, C.measureReal_eval_le]

/-- The empty lower orthant is the whole zero-dimensional cube. -/
@[simp]
theorem cdf_dim_zero (C : Copula 0) (u : Fin 0 → I) : C.cdf u = 1 := by
  have h : u = fun _ => 1 := Subsingleton.elim _ _
  rw [h, C.cdf_one]

end ProbabilityTheory.Copula

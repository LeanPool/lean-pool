/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Basic.Real.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Extending a finite coordinate functional

A linear functional on a finite coordinate set determines a state on the
whole index type by evaluating coordinate indicators. Its value on any
finitely supported integral vector depends only on those finite coordinates.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

/-- Extend a functional on a finite coordinate set by zero outside that set. -/
def finiteCoordinateState {S : Type*} (H : Finset S)
    (L : (H → ℝ) →ₗ[ℝ] ℝ) (x : S) : ℝ := by
  classical
  exact L (fun j : H ↦ if (j : S) = x then 1 else 0)

@[simp] theorem finiteCoordinateState_eq_zero_of_not_mem {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) {x : S} (hx : x ∉ H) :
    finiteCoordinateState H L x = 0 := by
  classical
  unfold finiteCoordinateState
  have hz : (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) = 0 := by
    funext j
    simp only [Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h ↦ hx (h ▸ j.property)
  rw [hz, map_zero]

/-- Evaluating a finitely supported integral vector against the extended
state agrees with restricting its coordinates and applying the functional. -/
theorem linearCombination_finiteCoordinateState {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) (v : S →₀ ℤ) :
    Finsupp.linearCombination ℤ (finiteCoordinateState H L) v =
      L (fun j : H ↦ (v j : ℝ)) := by
  classical
  induction v using Finsupp.induction with
  | zero =>
    simp only [map_zero, Finsupp.zero_apply, Int.cast_zero]
    exact (L.map_zero).symm
  | single_add x n v _ _ ih =>
    rw [map_add, Finsupp.linearCombination_single, ih]
    have hsingle :
        (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) =
          n • (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) := by
      funext j
      by_cases hj : (j : S) = x
      · simp [hj]
      · simp [hj]
    have hadd :
        (fun j : H ↦ ((Finsupp.single x n + v) j : ℝ)) =
          (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) +
            (fun j : H ↦ (v j : ℝ)) := by
      funext j
      simp
    rw [hadd, map_add, hsingle, map_zsmul]
    rfl

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields

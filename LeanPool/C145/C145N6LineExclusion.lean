/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145N6LiteralRows

/-!
# Exclusion of additional solutions on the six-vertex tensor line.
-/

@[expose] public section
namespace C145N6Literal
noncomputable section

/-- The two-by-two coefficient matrix for the quadratic and linear line constraints. -/
def liftedMinor : Matrix (Fin 2) (Fin 2) ℝ := !![q0,l0; q1,l1]

theorem liftedMinor_actual_det :
    liftedMinor.det =
      (461469337602175026166685008812416395118620104965845242542112 : ℝ) / 1685159 := by
  norm_num [liftedMinor,Matrix.det_fin_two,q0,l0,q1,l1]

theorem liftedMinor_det_ne_zero : liftedMinor.det ≠ 0 := by
  rw [liftedMinor_actual_det]
  norm_num

/-- Two actual associativity rows exclude every nonzero parameter on the saved line. -/
theorem actual_rows_force_zero (t : ℝ)
    (h0 : assocResidual (tensorLine t) 1 2 1 2 = 0)
    (h1 : assocResidual (tensorLine t) 1 2 1 3 = 0) : t = 0 := by
  rw [first_actual_row] at h0
  rw [second_actual_row] at h1
  have hz : (q0 * l1-q1 * l0) * t = 0 := by
    linear_combination q0 * h1-q1 * h0
  have hd : q0 * l1-q1 * l0 ≠ 0 := by
    simpa [liftedMinor,Matrix.det_fin_two,mul_comm] using liftedMinor_det_ne_zero
  exact (mul_eq_zero.mp hz).resolve_left hd

/-- A full associative tensor on this literal affine line must be the saved base tensor.
No assertion is made that every physical response fiber lies on this line. -/
theorem associative_literal_line_unique (t : ℝ)
    (h : ∀ i j k l, assocResidual (tensorLine t) i j k l = 0) :
    t = 0 ∧ tensorLine t = baseTensor := by
  have ht := actual_rows_force_zero t (h 1 2 1 2) (h 1 2 1 3)
  refine ⟨ht,?_⟩
  subst t
  funext i j k
  simp [tensorLine]

end
end C145N6Literal

end

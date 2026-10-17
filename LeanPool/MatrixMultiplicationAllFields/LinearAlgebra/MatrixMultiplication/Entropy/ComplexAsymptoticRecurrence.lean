/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

theorem affine_recurrence_shifted (x : ℕ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ t, x (t + 1) ≤ a * x t + (a - 1) * c) :
    ∀ t, x t + c ≤ a ^ t * (x 0 + c) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      x (t + 1) + c ≤ a * x t + (a - 1) * c + c := add_le_add_left (hstep t) c
      _ = a * (x t + c) := by ring
      _ ≤ a * (a ^ t * (x 0 + c)) := mul_le_mul_of_nonneg_left ih ha
      _ = a ^ (t + 1) * (x 0 + c) := by rw [pow_succ]; ring

theorem affine_recurrence_bound (x : ℕ → ℝ) (a b : ℝ) (ha : 1 < a) (hb : 0 ≤ b)
    (hstep : ∀ t, x (t + 1) ≤ a * x t + b) :
    ∀ t, x t ≤ a ^ t * (x 0 + b / (a - 1)) := by
  have hpos : 0 < a - 1 := sub_pos.mpr ha
  have hcancel : (a - 1) * (b / (a - 1)) = b := by
    field_simp [ne_of_gt hpos]
  have hshift := affine_recurrence_shifted x a (b / (a - 1)) (by linarith)
    (fun t => by rw [hcancel]; exact hstep t)
  intro t
  have hc : 0 ≤ b / (a - 1) := div_nonneg hb hpos.le
  exact (le_add_of_nonneg_right hc).trans (hshift t)

end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields

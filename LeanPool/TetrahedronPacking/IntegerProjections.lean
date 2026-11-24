/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FinCases

/-! # Integer projections and shift boxes
A nonzero axis with ordered projection intervals certifies separation.
-/

@[expose] public section

namespace TetrahedronPacking

/-- The dot product of two integer triples. -/
def integerDot (u v : Fin 3 → ℤ) : ℤ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The minimum and maximum vertex projections on an integer axis. -/
def integerProjectionBounds (n : Fin 3 → ℤ) (v : Fin 4 → Fin 3 → ℤ) : ℤ × ℤ :=
  let p := fun j => integerDot n (v j)
  (min (min (p 0) (p 1)) (min (p 2) (p 3)),
    max (max (p 0) (p 1)) (max (p 2) (p 3)))

/-- Check one nonzero axis, allowing equality at projected endpoints.
The offset is the projection of the translation applied to the right piece. -/
def integerSeparates (n : Fin 3 → ℤ) (v w : Fin 4 → Fin 3 → ℤ) (offset : ℤ) : Bool :=
  let (lo₁, hi₁) := integerProjectionBounds n v
  let (lo₂, hi₂) := integerProjectionBounds n w
  decide ((n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0) ∧
    (hi₁ ≤ lo₂ + offset ∨ hi₂ + offset ≤ lo₁))

theorem integerProjectionBounds_spec (n : Fin 3 → ℤ) (v : Fin 4 → Fin 3 → ℤ) (a : Fin 4) :
    (integerProjectionBounds n v).1 ≤ integerDot n (v a) ∧
    integerDot n (v a) ≤ (integerProjectionBounds n v).2 := by
  fin_cases a <;> simp [integerProjectionBounds, min_le_iff, le_max_iff]

theorem integerSeparates_sound (n : Fin 3 → ℤ) (v w : Fin 4 → Fin 3 → ℤ) (offset : ℤ)
    (h : integerSeparates n v w offset = true) :
    (∃ j, n j ≠ 0) ∧
      ((∀ a b : Fin 4, integerDot n (v a) ≤ integerDot n (w b) + offset) ∨
       (∀ a b : Fin 4, integerDot n (w b) + offset ≤ integerDot n (v a))) := by
  dsimp [integerSeparates] at h
  obtain ⟨hn, hw⟩ := of_decide_eq_true h
  constructor
  · rcases hn with h₀ | h₁ | h₂
    · exact ⟨0, h₀⟩
    · exact ⟨1, h₁⟩
    · exact ⟨2, h₂⟩
  obtain hw | hw := hw
  · left
    intro a b
    exact (integerProjectionBounds_spec n v a).2.trans
      (hw.trans (add_le_add_left (integerProjectionBounds_spec n w b).1 _))
  · right
    intro a b
    exact (add_le_add_left (integerProjectionBounds_spec n w b).2 _).trans
      (hw.trans (integerProjectionBounds_spec n v a).1)

/-- Enumerate the integer points in an inclusive coordinate box. -/
def integerShiftBox (lo hi : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  Finset.Icc lo hi

theorem mem_integerShiftBox (lo hi k : Fin 3 → ℤ) :
    k ∈ integerShiftBox lo hi ↔ ∀ j, lo j ≤ k j ∧ k j ≤ hi j := by
  simp only [integerShiftBox, Finset.mem_Icc, Pi.le_def, forall_and]

end TetrahedronPacking

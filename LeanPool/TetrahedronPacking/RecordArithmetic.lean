/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import LeanPool.TetrahedronPacking.IntegerProjections
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic for the Chen–Engel–Glotzer record

All vertex and period coordinates are multiplied by 160, so the numerical
checks are over integers. Coordinates come from arXiv:1001.0586v3,
Definition 2 and Theorem 1. For each pair and bounded shift, a list of ten
nonzero normals suffices: the translated projection intervals are disjoint
or touch at an endpoint. Lean checks each required comparison by reduction.
-/

@[expose] public section

namespace TetrahedronPacking

/-- Vertices in units of 1/160, ordered as the two positive and then the two
negative tetrahedra of the double dimer. -/
def recordVertex : Fin 4 → Fin 4 → Fin 3 → ℤ :=
  ![![![320, 320, 320], ![320, -160, -160], ![-160, 320, -160], ![-160, -160, 320]],
    ![![-320, -320, -320], ![320, -160, -160], ![-160, 320, -160], ![-160, -160, 320]],
    ![![134, -157, -343], ![134, 323, 137], ![614, -157, 137], ![614, 323, -343]],
    ![![774, 483, 297], ![134, 323, 137], ![614, -157, 137], ![614, 323, -343]]]

/-- The primitive periods `a+b`, `b+c`, `c+a` in the same units. -/
def recordPeriod : Fin 3 → Fin 3 → ℤ :=
  ![![384, 576, 192], ![90, 291, 573], ![576, 36, 360]]

private def separates (n : Fin 3 → ℤ) (i j : Fin 4) (x y z : ℤ) : Bool :=
  let offset := x * integerDot n (recordPeriod 0) + y * integerDot n (recordPeriod 1) +
    z * integerDot n (recordPeriod 2)
  integerSeparates n (recordVertex i) (recordVertex j) offset

private def axes : List (Fin 3 → ℤ) :=
  [![1, 1, 1], ![1, -5, 1], ![1, 1, -5], ![5, -1, -1], ![1, 1, -1],
    ![1, -1, -3], ![1, -1, 1], ![1, -1, -1], ![1, 3, -1], ![3, -1, 1]]

example : recordVertex 2 0 2 = -343 ∧ recordVertex 2 0 2 ≠ 343 := by decide
example : recordPeriod 2 1 = 36 ∧ recordPeriod 2 1 ≠ 0 := by decide
example : integerDot ![1, 1, 1] ![1, 2, 3] = 6 ∧
    integerDot ![1, 1, 1] ![1, 2, 3] ≠ 0 := by decide
example : integerProjectionBounds ![1, 1, 1] (recordVertex 0) = (0, 960) := by decide
example : integerProjectionBounds ![1, 1, 1] (recordVertex 0) ≠ (1, 960) := by decide
example : integerSeparates ![1, 1, 1] (recordVertex 0) (recordVertex 1) 0 = true := by decide
example : integerSeparates ![0, 0, 0] (recordVertex 0) (recordVertex 1) 0 = false := by decide
example : separates ![1, 1, 1] 0 1 0 0 0 = true := by decide
example : separates ![1, 1, 1] 0 0 0 0 0 = false := by decide
example : axes.any (fun n => separates n 0 1 0 0 0) = true := by decide
example : axes.any (fun n => separates n 0 0 0 0 0) = false := by decide

private theorem record_bounded_separations (i j : Fin 4) (x y z : Fin 5) :
    (i = j ∧ x = 2 ∧ y = 2 ∧ z = 2) ∨
    axes.any (fun n => separates n i j (x.val - (2 : ℤ)) (y.val - (2 : ℤ))
      (z.val - (2 : ℤ))) = true := by
  revert i j x y z
  decide +kernel

theorem record_integer_separator (i j : Fin 4) (x y z : Fin 5)
    (h : ¬ (i = j ∧ x = 2 ∧ y = 2 ∧ z = 2)) :
    ∃ n, integerSeparates n (recordVertex i) (recordVertex j)
      ((x.val - (2 : ℤ)) * integerDot n (recordPeriod 0) +
       (y.val - (2 : ℤ)) * integerDot n (recordPeriod 1) +
       (z.val - (2 : ℤ)) * integerDot n (recordPeriod 2)) = true := by
  obtain ⟨n, _, hs⟩ := List.any_eq_true.mp ((record_bounded_separations i j x y z).resolve_left h)
  exact ⟨n, hs⟩

theorem record_integer_planes (i j : Fin 4) (x y z : Fin 5)
    (h : ¬ (i = j ∧ x = 2 ∧ y = 2 ∧ z = 2)) :
    ∃ n : Fin 3 → ℤ, 0 < n 0 ∧
      let offset := (x.val - (2 : ℤ)) * integerDot n (recordPeriod 0) +
        (y.val - (2 : ℤ)) * integerDot n (recordPeriod 1) +
        (z.val - (2 : ℤ)) * integerDot n (recordPeriod 2)
      (∀ a b : Fin 4, integerDot n (recordVertex i a) ≤ integerDot n (recordVertex j b) + offset) ∨
      (∀ a b : Fin 4, integerDot n (recordVertex j b) + offset ≤
        integerDot n (recordVertex i a)) := by
  obtain ⟨n, hn, hs⟩ := List.any_eq_true.mp ((record_bounded_separations i j x y z).resolve_left h)
  refine ⟨n, ?_, (integerSeparates_sound n (recordVertex i) (recordVertex j) _ hs).2⟩
  simp only [axes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h <;> subst n <;> decide

theorem record_integer_edge_lengths (i a b : Fin 4) (h : a ≠ b) :
    integerDot (fun t => recordVertex i a t - recordVertex i b t)
      (fun t => recordVertex i a t - recordVertex i b t) = 460800 := by
  revert i a b
  decide

end TetrahedronPacking

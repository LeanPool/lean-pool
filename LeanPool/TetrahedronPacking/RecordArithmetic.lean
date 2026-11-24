/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import LeanPool.TetrahedronPacking.IntegerProjections
public import Mathlib.Data.Fin.VecNotation

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

/-- The integer-scaled translation corresponding to the period coordinates `k`. -/
def recordIntegerShift (k : Fin 3 → ℤ) (r : Fin 3) : ℤ :=
  k 0 * recordPeriod 0 r + k 1 * recordPeriod 1 r + k 2 * recordPeriod 2 r

private def separates (n : Fin 3 → ℤ) (i j : Fin 4) (k : Fin 3 → ℤ) : Bool :=
  integerSeparates n (recordVertex i) (recordVertex j) (integerDot n (recordIntegerShift k))

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
example : separates ![1, 1, 1] 0 1 0 = true := by decide
example : separates ![1, 1, 1] 0 0 0 = false := by decide
example : axes.any (fun n => separates n 0 1 0) = true := by decide
example : axes.any (fun n => separates n 0 0 0) = false := by decide

/-- The lower coordinate bound for the shifts requiring a separation check. -/
def recordShiftLower : Fin 3 → ℤ := fun _ => -2

/-- The upper coordinate bound for the shifts requiring a separation check. -/
def recordShiftUpper : Fin 3 → ℤ := fun _ => 2

private theorem record_bounded_separations (i j : Fin 4)
    (k : integerShiftBox recordShiftLower recordShiftUpper) :
    (i = j ∧ (k : Fin 3 → ℤ) = 0) ∨ axes.any (fun n => separates n i j k) = true := by
  revert i j k
  decide +kernel

theorem record_integer_separator (i j : Fin 4) (k : Fin 3 → ℤ)
    (hk : k ∈ integerShiftBox recordShiftLower recordShiftUpper) (h : i ≠ j ∨ k ≠ 0) :
    ∃ n, integerSeparates n (recordVertex i) (recordVertex j)
      (integerDot n (recordIntegerShift k)) = true := by
  have hneq : ¬ (i = j ∧ k = 0) := fun he => h.elim (fun hi => hi he.1) (fun hk => hk he.2)
  have hchecked := (record_bounded_separations i j ⟨k, hk⟩).resolve_left hneq
  obtain ⟨n, _, hn⟩ := List.any_eq_true.mp hchecked
  exact ⟨n, hn⟩

theorem record_integer_edge_lengths (i a b : Fin 4) (h : a ≠ b) :
    integerDot (fun t => recordVertex i a t - recordVertex i b t)
      (fun t => recordVertex i a t - recordVertex i b t) = 460800 := by
  revert i a b
  decide

end TetrahedronPacking

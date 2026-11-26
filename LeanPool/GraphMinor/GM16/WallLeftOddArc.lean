/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallEnclosedCoordinates
import LeanPool.GraphMinor.GM16.WallRowBoundary
import LeanPool.GraphMinor.GM16.RectangularLines
import Mathlib.Tactic.Linarith

/-!
# The outside boundary of a left brick in an odd row

An odd row is strictly between the top and bottom of an even-height
wall. The left brick begins at coordinate one. All its other
points lie in the central open rectangle, so only its left side
can meet the outside boundary. That side is already on the
frontier by the row boundary calculation.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- A left brick in an odd row meets the outside boundary in its
single vertical side. -/
theorem wall_left_odd_brick_outer_intersection_isLine {θ j : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ) (hj : j + 1 < θ) (hjOdd : ¬Even j) :
    ∃ a b : ℝ × ℝ, IsLineWithEnds
      ((Icc (1 : ℝ) 3 ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩ frontier (wallEnclosedSet θ)) a b := by
  have hjPos : 0 < j := by
    obtain ⟨a,ha⟩ := Nat.not_even_iff_odd.mp hjOdd
    omega
  have hjTop : j+1 < θ-1 := by
    obtain ⟨a,ha⟩ := Nat.not_even_iff_odd.mp hjOdd
    obtain ⟨b,hb⟩ := hEven
    omega
  have hM : (3 : ℝ) < 2*(θ : ℝ)-1 := by
    have h : (4 : ℝ) < 2*(θ : ℝ) := by exact_mod_cast (show 4<2*θ by omega)
    linarith
  have hLow : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjPos
  have hHigh : (j : ℝ)+1 < ((θ-1 : ℕ) : ℝ) := by exact_mod_cast hjTop
  have hEq : (Icc (1 : ℝ) 3 ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩
      frontier (wallEnclosedSet θ) = {1} ×ˢ Icc (j : ℝ) ((j : ℝ)+1) := by
    apply subset_antisymm
    · rintro p ⟨hp,hpFr⟩
      have hx : p.1=1 := by
        apply le_antisymm _ hp.1.1
        by_contra hn
        have hpCentral : p ∈ Ioo (1 : ℝ) (2*(θ : ℝ)-1) ×ˢ Ioo (0 : ℝ) ((θ-1 : ℕ) : ℝ) :=
          ⟨⟨lt_of_not_ge hn,hp.1.2.trans_lt hM⟩,hLow.trans_le hp.2.1,hp.2.2.trans_lt hHigh⟩
        exact hpFr.2 (central_open_rectangle_subset_interior_wallEnclosedSet
          (by omega : 2≤θ) hpCentral)
      exact ⟨hx,hp.2⟩
    · intro p hp
      have hSide := (wall_row_vertical_sides_subset_frontier (by omega : 2≤θ) hj).1
      rw [wallRowLeft,ite_eq_right hjOdd] at hSide
      exact ⟨⟨⟨hp.1.ge,by rw [hp.1]; norm_num⟩,hp.2⟩,hSide hp⟩
  refine ⟨(1,(j : ℝ)),(1,(j : ℝ)+1),?_⟩
  rw [hEq]
  exact vertical_interval_isLine 1 (by linarith)

end GraphMinor.GM16

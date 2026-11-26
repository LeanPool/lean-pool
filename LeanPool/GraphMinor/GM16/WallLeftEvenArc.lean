/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
public import LeanPool.GraphMinor.GM16.LeftRectangleArc
import LeanPool.GraphMinor.GM16.WallEnclosedCoordinates
import LeanPool.GraphMinor.GM16.WallBrickCover
import LeanPool.GraphMinor.GM16.WallHorizontalBoundary
import LeanPool.GraphMinor.GM16.WallRowBoundary
import LeanPool.GraphMinor.GM16.LeftBrickArcContainment
import LeanPool.GraphMinor.GM16.FaceSubdisc
import Mathlib.Tactic.Linarith

/-!
# The outside boundary arc of a left brick in an even row

Its left side is on the outer boundary. Its bottom and top sides
extend one unit to the right, or two units when they are the
bottom or top of the whole wall. These three sides form a line.
The central open rectangle excludes all other brick boundary
points from the outside boundary. This checks the left even-row
case of the common-face-line condition in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- A left brick in an even row meets the outside boundary in a line. -/
theorem wall_left_even_brick_outer_intersection_isLine {θ j : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ) (hj : j + 1 < θ) (hjEven : Even j) :
    ∃ a b : ℝ × ℝ, IsLineWithEnds
      ((Icc (0 : ℝ) 2 ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩ frontier (wallEnclosedSet θ)) a b := by
  let bottom : ℝ := if (j : ℝ)=0 then 2 else 1
  let top : ℝ := if (j : ℝ)+1=((θ-1 : ℕ) : ℝ) then 2 else 1
  let K := leftRectangleBoundaryArc 0 bottom top (j : ℝ) ((j : ℝ)+1)
  have hb₂ : bottom ≤ 2 := by dsimp [bottom]; split_ifs <;> norm_num
  have ht₂ : top ≤ 2 := by dsimp [top]; split_ifs <;> norm_num
  have hM : (3 : ℝ) < 2*(θ : ℝ) := by exact_mod_cast (show 3<2*θ by omega)
  have hTwo : (2 : ℝ) ≤ 2*(θ : ℝ) := by linarith
  have hTopY : (j : ℝ)+1 ≤ ((θ-1 : ℕ) : ℝ) := by
    exact_mod_cast (show j+1≤θ-1 by omega)
  have hLine : IsLineWithEnds K (bottom,(j : ℝ)) (top,(j : ℝ)+1) :=
    leftRectangleBoundaryArc_isLine
      (by dsimp [bottom]; split_ifs <;> norm_num)
      (by dsimp [top]; split_ifs <;> norm_num) (by linarith)
  have hKBrick : K ⊆ Icc (0 : ℝ) 2 ×ˢ Icc (j : ℝ) ((j : ℝ)+1) := by
    rintro p ((hp | hp) | hp)
    · exact ⟨⟨hp.1.1,hp.1.2.trans hb₂⟩,⟨hp.2.ge,by rw [hp.2]; linarith⟩⟩
    · exact ⟨⟨hp.1.ge,by rw [hp.1]; norm_num⟩,hp.2⟩
    · exact ⟨⟨hp.1.1,hp.1.2.trans ht₂⟩,⟨by rw [hp.2]; linarith,hp.2.le⟩⟩
  have hKFr : K ⊆ frontier (wallEnclosedSet θ) := by
    rintro p ((hp | hp) | hp)
    · by_cases hBot : (j : ℝ)=0
      · apply wall_bottom_row_subset_frontier (by omega : 2≤θ) hEven
        exact ⟨⟨hp.1.1,(hp.1.2.trans hb₂).trans hTwo⟩,hp.2.trans hBot⟩
      · apply wall_left_horizontal_join_subset_frontier (by omega : 2≤θ) hEven (by omega : j<θ)
        simpa only [bottom,ite_eq_right hBot] using hp
    · have hSide := (wall_row_vertical_sides_subset_frontier (by omega : 2≤θ) hj).1
      rw [wallRowLeft,ite_eq_left hjEven] at hSide
      exact hSide hp
    · by_cases hTop : (j : ℝ)+1=((θ-1 : ℕ) : ℝ)
      · apply wall_top_row_subset_frontier (by omega : 2≤θ) hEven
        exact ⟨⟨hp.1.1,(hp.1.2.trans ht₂).trans hTwo⟩,hp.2.trans hTop⟩
      · apply wall_left_horizontal_join_subset_frontier (by omega : 2≤θ) hEven hj
        simpa only [top,ite_eq_right hTop,Nat.cast_add,Nat.cast_one] using hp
  have hBC : Icc (0 : ℝ) 2 ×ˢ Icc (j : ℝ) ((j : ℝ)+1) ⊆ wallEnclosedSet θ := by
    have h := wall_brick_subset_enclosedSet (by omega : 0+2<2*θ+1) hj
      (show Even (0+j) by simpa only [Nat.zero_add] using hjEven)
    simpa only [Nat.cast_zero,zero_add] using h
  have hIntoK : (Icc (0 : ℝ) 2 ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩
      frontier (wallEnclosedSet θ) ⊆ K := by
    rintro p hp
    have hpFr := inter_frontier_subset_frontier_of_subset hBC hp
    have hpOut : p ∉ Ioo (1 : ℝ) (2*(θ : ℝ)-1) ×ˢ Ioo (0 : ℝ) ((θ-1 : ℕ) : ℝ) :=
      fun h => hp.2.2 (central_open_rectangle_subset_interior_wallEnclosedSet (by omega : 2≤θ) h)
    exact left_brick_boundary_outside_central_subset_arc hM (Nat.cast_nonneg j) hTopY hpFr hpOut
  have hEq : (Icc (0 : ℝ) 2 ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩
      frontier (wallEnclosedSet θ) = K := subset_antisymm hIntoK
        (fun _ hp => ⟨hKBrick hp,hKFr hp⟩)
  exact ⟨_,_,hEq.symm ▸ hLine⟩

end GraphMinor.GM16

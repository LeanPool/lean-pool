/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallEnclosedCoordinates
import LeanPool.GraphMinor.GM16.WallHorizontalBoundary
import LeanPool.GraphMinor.GM16.RectangularLines
import LeanPool.GraphMinor.GM16.SublineBetween
import Mathlib.Tactic.Linarith

/-!
# Common outside-face lines for the middle bricks

A brick away from the left and right boundary lies strictly inside
the central horizontal interval. It can meet the outside boundary
only at the wall's bottom or top. Those sides are lines. A brick
at neither level has no point on the outside boundary. This gives
the middle-brick case of the rigidity criterion in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- Distinct outside boundary points of a middle brick can be joined
inside that common boundary. -/
theorem exists_line_in_middle_brick_outer_intersection {θ i j : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ) (hiLeft : 2 ≤ i) (hiRight : i + 4 ≤ 2 * θ)
    (hj : j + 1 < θ) {a b : ℝ × ℝ} (hab : a ≠ b)
    (ha : a ∈ (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1)) ∩ frontier
      (wallEnclosedSet θ))
    (hb : b ∈ (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1)) ∩ frontier
      (wallEnclosedSet θ)) :
    ∃ K, IsLineWithEnds K a b ∧
      K ⊆ (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩ frontier (wallEnclosedSet θ) := by
  have hiLo : (1 : ℝ) < (i : ℝ) := by exact_mod_cast (show 1 < i by omega)
  have hiHi : (i : ℝ)+4 ≤ 2*(θ : ℝ) := by exact_mod_cast hiRight
  have hHeight : (1 : ℝ) < ((θ-1 : ℕ) : ℝ) := by exact_mod_cast (show 1<θ-1 by omega)
  have hYOut (p : ℝ × ℝ) (hp : p ∈ (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩
      frontier (wallEnclosedSet θ)) : p.2 ≤ 0 ∨ ((θ-1 : ℕ) : ℝ) ≤ p.2 := by
    by_cases hLow : 0 < p.2
    · right
      by_contra hHigh
      have hCentral : p ∈ Ioo (1 : ℝ) (2*(θ : ℝ)-1) ×ˢ Ioo (0 : ℝ) ((θ-1 : ℕ) : ℝ) :=
        ⟨⟨hiLo.trans_le hp.1.1.1,by linarith [hp.1.1.2]⟩,hLow,lt_of_not_ge hHigh⟩
      exact hp.2.2 (central_open_rectangle_subset_interior_wallEnclosedSet
        (by omega : 2≤θ) hCentral)
    · exact Or.inl (le_of_not_gt hLow)
  have hKHorizontal {y : ℝ} (hRow : Icc (0 : ℝ) (2*(θ : ℝ)) ×ˢ {y} ⊆ frontier (wallEnclosedSet θ)) :
      Icc (i : ℝ) ((i : ℝ)+2) ×ˢ {y} ⊆ frontier (wallEnclosedSet θ) := by
    rintro p ⟨hx,hy⟩
    exact hRow ⟨⟨(Nat.cast_nonneg i).trans hx.1,by linarith [hx.2]⟩,hy⟩
  by_cases hj0 : j=0
  · have hy0 : (j : ℝ)=0 := by exact_mod_cast hj0
    have hAY := hYOut a ha
    have hBY := hYOut b hb
    have ha0 : a.2=0 := by rcases hAY with h | h <;> linarith [ha.1.2.1,ha.1.2.2]
    have hb0 : b.2=0 := by rcases hBY with h | h <;> linarith [hb.1.2.1,hb.1.2.2]
    have hLine := horizontal_interval_isLine (show (i : ℝ)<(i : ℝ)+2 by linarith) 0
    obtain ⟨K,hK,hSub⟩ := exists_subline_between hLine ⟨ha.1.1,ha0⟩ ⟨hb.1.1,hb0⟩ hab
    refine ⟨K,hK,fun p hp => ?_⟩
    have hpK := hSub hp
    exact ⟨⟨hpK.1,⟨by rw [hpK.2,hy0],by rw [hpK.2,hy0]; norm_num⟩⟩,
      hKHorizontal (wall_bottom_row_subset_frontier (by omega : 2≤θ) hEven) hpK⟩
  by_cases hjTop : j + 1=θ-1
  · have hyTop : (j : ℝ)+1=((θ-1 : ℕ) : ℝ) := by exact_mod_cast hjTop
    have hjPos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0<j by omega)
    have hAY := hYOut a ha
    have hBY := hYOut b hb
    have haTop : a.2=((θ-1 : ℕ) : ℝ) := by rcases hAY with h | h <;> linarith [ha.1.2.1,ha.1.2.2]
    have hbTop : b.2=((θ-1 : ℕ) : ℝ) := by rcases hBY with h | h <;> linarith [hb.1.2.1,hb.1.2.2]
    have hLine := horizontal_interval_isLine (show (i : ℝ)<(i : ℝ)+2 by linarith) (((θ-1 : ℕ) : ℝ))
    obtain ⟨K,hK,hSub⟩ := exists_subline_between hLine ⟨ha.1.1,haTop⟩ ⟨hb.1.1,hbTop⟩ hab
    refine ⟨K,hK,fun p hp => ?_⟩
    have hpK := hSub hp
    exact ⟨⟨hpK.1,⟨by rw [hpK.2,← hyTop]; linarith,by rw [hpK.2,hyTop]⟩⟩,
      hKHorizontal (wall_top_row_subset_frontier (by omega : 2≤θ) hEven) hpK⟩
  have hjPos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0<j by omega)
  have hjUpper : (j : ℝ)+1 < ((θ-1 : ℕ) : ℝ) := by exact_mod_cast (show j + 1<θ-1 by omega)
  rcases hYOut a ha with h | h <;> linarith [ha.1.2.1,ha.1.2.2]

end GraphMinor.GM16

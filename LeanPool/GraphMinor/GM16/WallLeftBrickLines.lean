/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallLeftEvenArc
import LeanPool.GraphMinor.GM16.WallLeftOddArc
import LeanPool.GraphMinor.GM16.SublineBetween

/-!
# Common outside-face lines for the leftmost bricks

The parity rule puts a leftmost brick at coordinate zero in an
even row and at coordinate one in an odd row. The preceding
calculations give a line as the whole intersection with the outer
boundary. Taking a subline joins any two distinct common points,
as required by the rigidity criterion in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- Distinct outside boundary points of a leftmost brick can be joined
inside their common boundary. -/
theorem exists_line_in_left_brick_outer_intersection {θ i j : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ) (hi : i ≤ 1) (hj : j + 1 < θ) (hParity : Even (i + j))
    {a b : ℝ × ℝ} (hab : a ≠ b)
    (ha : a ∈ (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1)) ∩ frontier
      (wallEnclosedSet θ))
    (hb : b ∈ (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1)) ∩ frontier
      (wallEnclosedSet θ)) :
    ∃ K, IsLineWithEnds K a b ∧
      K ⊆ (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩ frontier (wallEnclosedSet θ) := by
  have hArc : ∃ x y : ℝ × ℝ, IsLineWithEnds
      ((Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩ frontier (wallEnclosedSet θ)) x y
        := by
    by_cases hi0 : i=0
    · subst i
      have hjEven : Even j := by simpa only [Nat.zero_add] using hParity
      simpa only [Nat.cast_zero,zero_add] using wall_left_even_brick_outer_intersection_isLine hθ
        hEven hj hjEven
    · have hi1 : i=1 := by omega
      subst i
      have hjOdd : ¬Even j := by
        intro hjEven
        obtain ⟨x,hx⟩ := hParity
        obtain ⟨y,hy⟩ := hjEven
        omega
      simpa only [Nat.cast_one,show (1 : ℝ)+2=3 by norm_num] using
        wall_left_odd_brick_outer_intersection_isLine hθ hEven hj hjOdd
  obtain ⟨x,y,hLine⟩ := hArc
  exact exists_subline_between hLine ha hb hab

end GraphMinor.GM16

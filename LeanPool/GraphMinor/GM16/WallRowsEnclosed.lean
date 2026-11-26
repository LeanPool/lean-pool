/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallBrickCover
import Mathlib.Tactic.Linarith

/-!
# The retained wall lines lie in the enclosed disc

Every horizontal row borders a full-width even strip when the
height is even. A retained vertical line is a side of one of the
closed bricks. These observations place all wall vertices and
edges in the disc enclosed by its outer boundary, as needed for
the outside face in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set

/-- A point of a full even strip lies in the enclosed row stack. -/
theorem mem_wallEnclosedSet_even_row {θ k : ℕ} (hk : k + 1 < θ) (hEven : Even k)
    {p : ℝ × ℝ} (hx : p.1 ∈ Icc (0 : ℝ) (2 * (θ : ℝ)))
    (hy : p.2 ∈ Icc (k : ℝ) ((k : ℝ) + 1)) : p ∈ wallEnclosedSet θ := by
  apply mem_iUnion₂.mpr
  refine ⟨k,by omega,?_⟩
  simpa only [wallRowRight,wallRowLeft,ite_eq_left hEven,Nat.cast_mul,Nat.cast_ofNat,sub_zero] using
    (show p ∈ Icc (0 : ℝ) (2*(θ : ℝ)) ×ˢ Icc (k : ℝ) ((k : ℝ)+1) from ⟨hx,hy⟩)

/-- Every horizontal row of an even-height wall is in the enclosed disc. -/
theorem wall_horizontal_row_subset_enclosed {θ j : ℕ} (hθ : Even θ) (hj : j < θ) :
    Icc (0 : ℝ) (2*(θ : ℝ)) ×ˢ {(j : ℝ)} ⊆ wallEnclosedSet θ := by
  rintro p ⟨hx,hy⟩
  by_cases hEven : Even j
  · have hk : j+1 < θ := by
      obtain ⟨a,ha⟩ := hθ
      obtain ⟨b,hb⟩ := hEven
      omega
    apply mem_wallEnclosedSet_even_row hk hEven hx
    exact ⟨hy.ge,by rw [hy]; exact le_add_of_nonneg_right zero_le_one⟩
  · obtain ⟨b,hb⟩ := Nat.not_even_iff_odd.mp hEven
    have hk : j-1+1 = j := by omega
    have hkEven : Even (j-1) := ⟨b,by omega⟩
    have hkReal : ((j-1 : ℕ) : ℝ)+1 = (j : ℝ) := by exact_mod_cast hk
    apply mem_wallEnclosedSet_even_row (by omega : j-1+1 < θ) hkEven hx
    exact ⟨by rw [hy,← hkReal]; exact le_add_of_nonneg_right zero_le_one,
      by rw [hy,hkReal]⟩

/-- Each retained vertical side belongs to one of the bricks in the
row stack. -/
theorem wall_vertical_side_subset_enclosed {θ i j : ℕ} (_hθ : 2 ≤ θ)
    (hi : i < 2 * θ + 1) (hj : j + 1 < θ) (hEven : Even (i + j)) :
    {(i : ℝ)} ×ˢ Icc (j : ℝ) ((j : ℝ)+1) ⊆ wallEnclosedSet θ := by
  rintro p ⟨hx,hy⟩
  by_cases hRoom : i+2 < 2*θ+1
  · apply wall_brick_subset_enclosedSet hRoom hj hEven
    exact ⟨⟨hx.ge,by rw [hx]; exact le_add_of_nonneg_right (by norm_num)⟩,hy⟩
  · have hi2 : 2 ≤ i := by omega
    have hPrev : i-2+2=i := by omega
    have hPrevReal : ((i-2 : ℕ) : ℝ)+2 = (i : ℝ) := by exact_mod_cast hPrev
    have hPrevEven : Even ((i-2)+j) := by
      obtain ⟨a,ha⟩ := hEven
      exact ⟨a-1,by omega⟩
    apply wall_brick_subset_enclosedSet (by omega : i-2+2<2*θ+1) hj hPrevEven
    refine ⟨⟨?_,?_⟩,hy⟩
    · rw [hx,← hPrevReal]
      exact le_add_of_nonneg_right (by norm_num)
    · rw [hx,hPrevReal]

end GraphMinor.GM16

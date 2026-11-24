/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallEnclosedCoordinates
import LeanPool.GraphMinor.GM16.WallRowsEnclosed
import LeanPool.GraphMinor.GM16.LocalCoordinateBoundary
import LeanPool.GraphMinor.GM16.LineClosedExtension
import LeanPool.GraphMinor.GM16.RectangularLines
import Mathlib.Tactic.Linarith

/-!
# Horizontal parts of the outside wall boundary

The bottom and top rows are extreme vertical coordinates. At each
intermediate row, the short left join borders an odd strip on
one side. Points to the left of that strip are outside the enclosed
disc. Local coordinate bounds therefore put the join on the
frontier. Closedness adds its two ends.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- The short horizontal join on the left of every row is on the outer boundary. -/
theorem wall_left_horizontal_join_subset_frontier {θ j : ℕ}
    (hθ : 2 ≤ θ) (hEven : Even θ) (hj : j < θ) :
    Icc (0 : ℝ) 1 ×ˢ {(j : ℝ)} ⊆ frontier (wallEnclosedSet θ) := by
  apply line_subset_closed_of_open_part_subset
    (horizontal_interval_isLine (by norm_num : (0 : ℝ)<1) (j : ℝ)) isClosed_frontier
  rintro p ⟨hp,hnEnds⟩
  have hpLt : p.1 < 1 := by
    apply lt_of_le_of_ne hp.1.2
    intro he
    exact hnEnds (Or.inr (mem_singleton_iff.mpr (Prod.ext he hp.2)))
  have hθReal : (1 : ℝ) ≤ 2*(θ : ℝ) := by exact_mod_cast (show 1≤2*θ by omega)
  have hpC : p ∈ wallEnclosedSet θ := wall_horizontal_row_subset_enclosed hEven hj
    ⟨⟨hp.1.1,hp.1.2.trans hθReal⟩,hp.2⟩
  refine ⟨subset_closure hpC,?_⟩
  by_cases hj0 : j = 0
  · subst j
    apply not_mem_interior_of_local_coordinate_min isOpen_univ isOpenMap_snd (mem_univ p) hp.2
    intro q hq
    simpa only [Nat.cast_zero] using (wallEnclosedSet_bounds hq.1).2.2.1
  by_cases hjEven : Even j
  · have hk : j-1+1=j := by omega
    have hkOdd : ¬Even (j-1) := by
      intro h
      obtain ⟨a,ha⟩ := hjEven
      obtain ⟨b,hb⟩ := h
      omega
    have hkReal : ((j-1 : ℕ) : ℝ)+1 = (j : ℝ) := by exact_mod_cast hk
    let O : Set (ℝ × ℝ) := {q | q.1 < 1 ∧ ((j-1 : ℕ) : ℝ) < q.2}
    have hO : IsOpen O := (isOpen_Iio.preimage continuous_fst).inter (isOpen_Ioi.preimage
      continuous_snd)
    have hpO : p ∈ O := ⟨hpLt,by rw [hp.2,← hkReal]; linarith⟩
    apply not_mem_interior_of_local_coordinate_min hO isOpenMap_snd hpO hp.2
    intro q hq
    by_contra hLow
    have hy : q.2 ∈ Ioo ((j-1 : ℕ) : ℝ) (((j-1 : ℕ) : ℝ)+1) :=
      ⟨hq.2.2,by rw [hkReal]; exact lt_of_not_ge hLow⟩
    have hLeft := (wallEnclosedSet_mem_open_strip hq.1 hy).2.1
    simp only [wallRowLeft,ite_eq_right hkOdd] at hLeft
    exact (not_lt_of_ge hLeft) hq.2.1
  · let O : Set (ℝ × ℝ) := {q | q.1 < 1 ∧ q.2 < (j : ℝ)+1}
    have hO : IsOpen O := (isOpen_Iio.preimage continuous_fst).inter (isOpen_Iio.preimage
      continuous_snd)
    have hpO : p ∈ O := ⟨hpLt,by rw [hp.2]; linarith⟩
    apply not_mem_interior_of_local_coordinate_max hO isOpenMap_snd hpO hp.2
    intro q hq
    by_contra hHigh
    have hy : q.2 ∈ Ioo (j : ℝ) ((j : ℝ)+1) := ⟨lt_of_not_ge hHigh,hq.2.2⟩
    have hLeft := (wallEnclosedSet_mem_open_strip hq.1 hy).2.1
    simp only [wallRowLeft,ite_eq_right hjEven] at hLeft
    exact (not_lt_of_ge hLeft) hq.2.1

/-- The bottom horizontal row is on the outer boundary. -/
theorem wall_bottom_row_subset_frontier {θ : ℕ} (hθ : 2 ≤ θ) (hEven : Even θ) :
    Icc (0 : ℝ) (2*(θ : ℝ)) ×ˢ {(0 : ℝ)} ⊆ frontier (wallEnclosedSet θ) := by
  intro p hp
  have hpC := wall_horizontal_row_subset_enclosed hEven (by omega : 0<θ)
    (show p ∈ Icc (0 : ℝ) (2*(θ : ℝ)) ×ˢ {((0 : ℕ) : ℝ)} from by simpa only [Nat.cast_zero] using
      hp)
  refine ⟨subset_closure hpC,?_⟩
  apply not_mem_interior_of_local_coordinate_min isOpen_univ isOpenMap_snd (mem_univ p) hp.2
  intro q hq
  exact (wallEnclosedSet_bounds hq.1).2.2.1

/-- The top horizontal row is on the outer boundary. -/
theorem wall_top_row_subset_frontier {θ : ℕ} (hθ : 2 ≤ θ) (hEven : Even θ) :
    Icc (0 : ℝ) (2*(θ : ℝ)) ×ˢ {((θ-1 : ℕ) : ℝ)} ⊆ frontier (wallEnclosedSet θ) := by
  intro p hp
  have hpC := wall_horizontal_row_subset_enclosed hEven (by omega : θ-1<θ) hp
  refine ⟨subset_closure hpC,?_⟩
  apply not_mem_interior_of_local_coordinate_max isOpen_univ isOpenMap_snd (mem_univ p) hp.2
  intro q hq
  exact (wallEnclosedSet_bounds hq.1).2.2.2

end GraphMinor.GM16

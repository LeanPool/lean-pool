/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4DistinctCrossDirections
public import LeanPool.GraphMinor.GM12.Section4ChordGeometry

/-!
# Coordinates at a crossing of two chords

For XII (4.5), page 253, distinct circle ports give distinct
supporting lines. At a meeting in the open unit disc, the vectors
from the meeting to one port of each chord are nonzero. Use these
vectors as the columns of the real-linear crossing coordinates.
Both complete supporting lines are then the coordinate axes.
-/

public section

namespace GraphMinor.GM12

open Set Metric

/-- Lines through disjoint pairs of unit-circle ports are distinct.
A unit-circle point of the other line would have to be one of its
two ports. -/
theorem lines_ne_of_distinct_unit_ports {a c d : ℂ} (b : ℂ)
    (ha : ‖a‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) :
    line[ℝ, a, b] ≠ line[ℝ, c, d] := by
  intro heq
  have haL : a ∈ line[ℝ, c, d] := heq ▸ left_mem_affineSpan_pair ℝ a b
  exact ((unit_circle_mem_line_iff hc hd hcd ha).mp haL).elim hac had

/-- The two supporting lines at an interior meeting of distinct
chords are exactly the two axes of a translated continuous
real-linear equivalence, as used in XII (4.5), page 253. -/
theorem exists_cross_coordinates_for_chords {a b c d x : ℂ}
    (ha : ‖a‖ = 1) (hc : ‖c‖ = 1)
    (hx : x ∈ ball (0 : ℂ) 1)
    (hxa : x ∈ line[ℝ, a, b]) (hxc : x ∈ line[ℝ, c, d])
    (hne : line[ℝ, a, b] ≠ line[ℝ, c, d]) :
    ∃ A : ℂ ≃L[ℝ] ℂ,
      line[ℝ, x, x + A 1] = line[ℝ, a, b] ∧
      line[ℝ, x, x + A Complex.I] = line[ℝ, c, d] := by
  have hnorm : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hxa' : x ≠ a := by
    intro heq
    rw [heq, ha] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  have hxc' : x ≠ c := by
    intro heq
    rw [heq, hc] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm
  have hab : line[ℝ, x, a] = line[ℝ, a, b] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hxa (left_mem_affineSpan_pair ℝ a b) hxa'
  have hcd : line[ℝ, x, c] = line[ℝ, c, d] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hxc (left_mem_affineSpan_pair ℝ c d) hxc'
  have hax : x + (a - x) = a := by abel
  have hcx : x + (c - x) = c := by abel
  have hline : line[ℝ, x, x + (a - x)] ≠ line[ℝ, x, x + (c - x)] := by
    simpa only [hax, hcx, hab, hcd] using hne
  obtain ⟨A, hA, hA'⟩ := exists_cross_coordinates_of_distinct_lines
    (sub_ne_zero.mpr (Ne.symm hxa')) (sub_ne_zero.mpr (Ne.symm hxc')) hline
  refine ⟨A, ?_, ?_⟩
  · rw [hA, hax]
    exact hab
  · rw [hA', hcx]
    exact hcd

end GraphMinor.GM12

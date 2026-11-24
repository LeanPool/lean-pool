/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CircleAvoidance

/-!
# Choosing a chord off old crossings

The crossing drawing in XII (4.5), page 253, can be built by choosing
circle ports successively. Once the first end is fixed away from the
old crossing points, exclude the finitely many lines from that end
to those points when choosing the second end. The new chord then
misses all the old crossing points. Distinct supporting lines have
at most one common point, so the set of old crossings is finite.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface EuclideanGeometry

/-- Distinct supporting lines of chords meet in at most one point. -/
theorem subsingleton_inter_of_ne_lines {a b c d : ℂ}
    (hne : line[ℝ, a, b] ≠ line[ℝ, c, d]) :
    ((line[ℝ, a, b] : Set ℂ) ∩ (line[ℝ, c, d] : Set ℂ)).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  apply hne
  exact (affineSpan_pair_eq_of_mem_of_mem_of_ne hx.1 hy.1 hxy).symm.trans
    (affineSpan_pair_eq_of_mem_of_mem_of_ne hx.2 hy.2 hxy)

/-- The second port can be placed in a prescribed open circle arc
so that the whole supporting line misses a finite set of points.
This is the exclusion of old crossings in XII (4.5), page 253. -/
theorem exists_chord_line_avoiding_finite_set
    {X : Set ℂ} (hX : X.Finite) {a : ℂ} (ha : ‖a‖ = 1) (haX : a ∉ X)
    {u v : ℝ} (huv : u < v) (hlen : v ≤ u + 1) :
    ∃ t ∈ Ioo u v, (ee t : ℂ) ≠ a ∧
      Disjoint (line[ℝ, a, (ee t : ℂ)] : Set ℂ) X := by
  classical
  let Y := insert a X
  let : Fintype Y := (hX.insert a).fintype
  obtain ⟨t, ht, havoid⟩ := exists_circle_port_avoiding_lines
    (fun _ : Y => a) (fun x : Y => (x : ℂ)) (fun _ => ha) huv hlen
  have hba : (ee t : ℂ) ≠ a := by
    intro h
    apply havoid ⟨a, mem_insert a X⟩
    rw [h]
    exact left_mem_affineSpan_pair _ _ _
  refine ⟨t, ht, hba, disjoint_left.mpr ?_⟩
  intro x hx hxX
  have hxa : x ≠ a := fun h => haX (h ▸ hxX)
  have heq := affineSpan_pair_eq_of_right_mem_of_ne hx hxa
  apply havoid ⟨x, mem_insert_of_mem a hxX⟩
  change (ee t : ℂ) ∈ line[ℝ, a, x]
  rw [heq]
  exact right_mem_affineSpan_pair _ _ _

/-- Add one chord to finitely many distinct supporting lines, with
its ends in prescribed short circle arcs. The new line is distinct
from the old lines and passes through none of their pairwise
intersections. These are the finite-intersection and no-triple-
crossing conditions in XII (4.5), page 253. -/
theorem exists_chord_avoiding_old_crossings {ι : Type*} [Finite ι]
    (a b : ι → ℂ) (ha : ∀ i, ‖a i‖ = 1)
    (hne : ∀ i j, i ≠ j → line[ℝ, a i, b i] ≠ line[ℝ, a j, b j])
    {u v w z : ℝ} (huv : u < v) (huvlen : v ≤ u + 1)
    (hwz : w < z) (hwzlen : z ≤ w + 1) :
    ∃ s ∈ Ioo u v, ∃ t ∈ Ioo w z,
      (ee s : ℂ) ≠ (ee t : ℂ) ∧
      (∀ i, line[ℝ, (ee s : ℂ), (ee t : ℂ)] ≠ line[ℝ, a i, b i]) ∧
      (∀ i, a i ∉ (line[ℝ, (ee s : ℂ), (ee t : ℂ)] : Set ℂ) ∧
        b i ∉ (line[ℝ, (ee s : ℂ), (ee t : ℂ)] : Set ℂ)) ∧
      ∀ i j, i ≠ j → Disjoint
        (line[ℝ, (ee s : ℂ), (ee t : ℂ)] : Set ℂ)
        ((line[ℝ, a i, b i] : Set ℂ) ∩ (line[ℝ, a j, b j] : Set ℂ)) := by
  classical
  let X : Set ℂ := ⋃ i, ⋃ j, if i = j then ∅ else
    (line[ℝ, a i, b i] : Set ℂ) ∩ (line[ℝ, a j, b j] : Set ℂ)
  have hX : X.Finite := by
    refine finite_iUnion fun i => finite_iUnion fun j => ?_
    split_ifs with hij
    · exact finite_empty
    · exact (subsingleton_inter_of_ne_lines (hne i j hij)).finite
  let B : Set ℂ := ⋃ i, sphere (0 : ℂ) 1 ∩ (line[ℝ, a i, b i] : Set ℂ)
  have hB : B.Finite := finite_iUnion fun i => finite_unit_circle_inter_line (ha i)
  obtain ⟨s, hs, hsbad⟩ := exists_circle_port_avoiding_finite_set (hX.union hB) huv huvlen
  have hsX : (ee s : ℂ) ∉ X := fun h => hsbad (Or.inl h)
  have hsline : ∀ i, (ee s : ℂ) ∉ (line[ℝ, a i, b i] : Set ℂ) := by
    intro i hi
    exact hsbad (Or.inr (mem_iUnion.mpr ⟨i, ⟨by simp, hi⟩⟩))
  let Y : Set ℂ := X ∪ range a ∪ range b
  have hY : Y.Finite := (hX.union (finite_range a)).union (finite_range b)
  have hsY : (ee s : ℂ) ∉ Y := by
    rintro ((hx | ⟨i, hi⟩) | ⟨i, hi⟩)
    · exact hsX hx
    · exact hsline i (hi ▸ left_mem_affineSpan_pair ℝ (a i) (b i))
    · exact hsline i (hi ▸ right_mem_affineSpan_pair ℝ (a i) (b i))
  obtain ⟨t, ht, hts, hdisj⟩ := exists_chord_line_avoiding_finite_set hY
    (by simp) hsY hwz hwzlen
  refine ⟨s, hs, t, ht, hts.symm, ?_, ?_, ?_⟩
  · intro i heq
    apply hsline i
    rw [← heq]
    exact left_mem_affineSpan_pair _ _ _
  · intro i
    exact ⟨fun h => disjoint_left.mp hdisj h (Or.inl (Or.inr (mem_range_self i))),
      fun h => disjoint_left.mp hdisj h (Or.inr (mem_range_self i))⟩
  · intro i j hij
    apply hdisj.mono_right
    intro x hx
    exact Or.inl (Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, by simpa [hij] using hx⟩⟩))

end GraphMinor.GM12

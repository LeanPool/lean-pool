/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.ArcErase
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Cutting the leaf edge before a compact circle

In the leaf gluing needed by XII (7.4), pages 262--263, the
circle to be enclosed misses the retained end of the edge.
A short initial segment misses the circle as well, by continuity.
Cut the edge there. Its last segment contains every intersection
with the circle, and the initial and last segments meet only in
the cut point. This gives the closed remainder used in the lens
construction.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric unitInterval

private theorem exists_initial_interval_avoiding_closed
    {S : Type*} [TopologicalSpace S] {a : I → S} (ha : Continuous a)
    {F : Set S} (hF : IsClosed F) (h0 : a 0 ∉ F) :
    ∃ t : I, 0 < t ∧ t < 1 ∧ ∀ s ≤ t, a s ∉ F := by
  have hO : IsOpen (a ⁻¹' Fᶜ) := hF.isOpen_compl.preimage ha
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hO 0 h0
  let t : I := ⟨min (ε / 2) (1 / 2), le_min (by positivity) (by norm_num),
    (min_le_right _ _).trans (by norm_num)⟩
  have htpos : 0 < t := show (0 : ℝ) < min (ε / 2) (1 / 2) from
    lt_min (by positivity) (by norm_num)
  have htone : t < 1 := show min (ε / 2) (1 / 2) < (1 : ℝ) from
    (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨t, htpos, htone, ?_⟩
  intro s hst
  apply hsub
  change dist s (0 : I) < ε
  change |(s : ℝ) - 0| < ε
  rw [sub_zero, abs_of_nonneg s.2.1]
  have hst' : (s : ℝ) ≤ min (ε / 2) (1 / 2) := hst
  have hsε : (s : ℝ) ≤ ε / 2 := hst'.trans (min_le_left _ _)
  linarith

/-- Split a line into an initial segment missing a closed set
and a last segment, at a point different from either end. -/
theorem exists_line_split_with_prefix_avoiding_closed
    {S : Type*} [TopologicalSpace S] [T2Space S] {E F : Set S} {u v : S}
    (hE : IsLineWithEnds E u v) (hF : IsClosed F) (huF : u ∉ F) :
    ∃ (P L : Set S) (w : S), IsLineWithEnds P u w ∧ IsLineWithEnds L w v ∧
      P ∪ L = E ∧ P ∩ L = {w} ∧ Disjoint P F ∧ w ≠ u ∧ w ≠ v := by
  obtain ⟨a, ha, har, ha0, ha1⟩ := hE.exists_arc
  obtain ⟨t, ht0, ht1, havoid⟩ := exists_initial_interval_avoiding_closed ha.1 hF (ha0.symm ▸ huF)
  let P := a '' Icc 0 t
  let L := a '' Icc t 1
  have hP : IsLineWithEnds P u (a t) := by
    have hh := (ha.sub (s := 0) (t := t) ht0.ne).isLineWithEnds
    rwa [range_subArc _ ht0.le, subArc_zero, subArc_one, ha0] at hh
  have hL : IsLineWithEnds L (a t) v := by
    have hh := (ha.sub (s := t) (t := 1) ht1.ne).isLineWithEnds
    rwa [range_subArc _ ht1.le, subArc_zero, subArc_one, ha1] at hh
  have hUnion : P ∪ L = E := by
    change a '' Icc 0 t ∪ a '' Icc t 1 = E
    rw [← image_union, Icc_union_Icc_eq_Icc ht0.le ht1.le, ← har]
    ext x
    simp only [mem_image, mem_Icc, mem_range]
    constructor
    · rintro ⟨s, _, hs⟩; exact ⟨s, hs⟩
    · rintro ⟨s, hs⟩; exact ⟨s, ⟨unitInterval.nonneg s, unitInterval.le_one s⟩, hs⟩
  have hInter : P ∩ L = {a t} := by
    apply Subset.antisymm
    · rintro x ⟨⟨s, hs, hsx⟩, r, hr, hrx⟩
      have hsr : s = r := ha.2 (hsx.trans hrx.symm)
      have hst : s = t := le_antisymm hs.2 (hsr.symm ▸ hr.1)
      exact hsx.symm.trans (congrArg a hst)
    · exact singleton_subset_iff.mpr
        ⟨⟨t, ⟨unitInterval.nonneg t, le_rfl⟩, rfl⟩,
          ⟨t, ⟨le_rfl, unitInterval.le_one t⟩, rfl⟩⟩
  have hdis : Disjoint P F := by
    apply disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ hxF
    exact havoid s hs.2 hxF
  refine ⟨P, L, a t, hP, hL, hUnion, hInter, hdis, ?_, ?_⟩
  · intro h
    exact ht0.ne' (ha.2 (h.trans ha0.symm))
  · intro h
    exact ht1.ne (ha.2 (h.trans ha1.symm))

end GraphMinor.GM12

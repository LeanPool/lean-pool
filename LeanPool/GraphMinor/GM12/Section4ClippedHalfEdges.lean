/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossingVertexDiscs
public import LeanPool.GraphMinor.GM12.Section4ResidualArc
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Clipping the half-edges outside the crossing discs

For XII (4.5), claim (1), page 253, split each subdivided edge
at its crossing and clip each half between its vertex disc and
the crossing-disc set. The residual arcs meet the two closed
sets only at their ends. Every meeting of different half-edges
was either an original vertex or a crossing. Both types of
points lie in the interiors of the sets removed, so the
residual arcs are disjoint.
-/

public section

namespace GraphMinor.GM12

open Set Surface Topology

/-- The half-edges of a crossing drawing give disjoint residual
arcs between their vertex discs and the crossing-disc set.
This proves the residual-arc step of XII (4.5), claim (1),
page 253. -/
theorem exists_clipped_halfedge_family
    {S V ι : Type*} [TopologicalSpace S] [T2Space S] [Finite V] [Finite ι]
    (hS : IsClosedSurface S) (v : V → S) (hinj : Function.Injective v)
    (owner : ι → V) (x : ι → S) (L : ι → Set S)
    (hL : ∀ i, IsLineWithEnds (L i) (v (owner i)) (x i))
    (hLV : ∀ i w, v w ∈ L i → w = owner i)
    (hLL : ∀ i j, i ≠ j → L i ∩ L j ⊆ range v ∪ range x)
    (Z : Set S) (hZ : IsClosed Z) (hvZ : ∀ w, v w ∉ Z)
    (hxZ : ∀ i, x i ∈ interior Z) :
    ∃ (A : V → Set S) (b : ι → unitInterval → S),
      (∀ w, IsClosedDisc (A w)) ∧
      (∀ w z, w ≠ z → Disjoint (A w) (A z)) ∧
      (∀ w, Disjoint (A w) Z) ∧
      (∀ i, IsArcMap (b i)) ∧
      (∀ i j, i ≠ j → Disjoint (range (b i)) (range (b j))) ∧
      (∀ i, b i 0 ∈ discBd (A (owner i))) ∧
      (∀ i, b i 1 ∈ Z) ∧
      (∀ i, range (b i) ∩ (Z ∪ ⋃ w, A w) = {b i 0, b i 1}) ∧
      (∀ i, range (b i) ⊆ L i) ∧ (∀ i, b i 1 ∈ frontier Z) := by
  classical
  obtain ⟨A, hA, hAA, hAZ, hAL⟩ := exists_crossing_vertex_disc_family hS v hinj owner L
    (fun i => (hL i).isCompact.isClosed) hLV Z hZ hvZ
  let C := ⋃ w, A w
  have hC : IsClosed C := isClosed_iUnion_of_finite (fun w => (hA w).1.isClosed)
  have hCZ : Disjoint C Z := disjoint_left.mpr (by
    rintro z hz hzZ
    obtain ⟨w, hw⟩ := mem_iUnion.mp hz
    exact disjoint_left.mp (hAZ w) hw hzZ)
  have hvC : ∀ w, v w ∈ interior C := fun w =>
    interior_mono (subset_iUnion A w) (hA w).2
  have hex : ∀ i, ∃ b : unitInterval → S, IsArcMap b ∧ range b ⊆ L i ∧
      b 0 ∈ frontier C ∧ b 1 ∈ frontier Z ∧
      range b ∩ C = {b 0} ∧ range b ∩ Z = {b 1} := by
    intro i
    obtain ⟨a, ha, har, ha0, ha1⟩ := (hL i).exists_arc
    obtain ⟨b, hb, hba, hb0, hb1, hbC, hbZ⟩ := exists_residual_arc_between_closed_sets ha
      hC hZ hCZ (ha0 ▸ interior_subset (hvC (owner i))) (ha1 ▸ interior_subset (hxZ i))
    exact ⟨b, hb, hba.trans har.subset, hb0, hb1, hbC, hbZ⟩
  choose b hb hsub hb0 hb1 hbC hbZ using hex
  have hb1Z : ∀ i, b i 1 ∈ Z := fun i =>
    ((hbZ i).symm.subset (mem_singleton _)).2
  have hb0A : ∀ i, b i 0 ∈ A (owner i) := by
    intro i
    have hb0C : b i 0 ∈ C := ((hbC i).symm.subset (mem_singleton _)).2
    obtain ⟨w, hw⟩ := mem_iUnion.mp hb0C
    by_cases hwo : w = owner i
    · exact hwo ▸ hw
    · exact False.elim (disjoint_left.mp (hAL w i hwo) hw (hsub i (mem_range_self 0)))
  have hb0bd : ∀ i, b i 0 ∈ discBd (A (owner i)) := by
    intro i
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hS (hA (owner i)).1]
    refine ⟨subset_closure (hb0A i), ?_⟩
    intro hint
    exact (hb0 i).2 (interior_mono (subset_iUnion A (owner i)) hint)
  have hmissV : ∀ i, Disjoint (range (b i)) (range v) := by
    intro i
    apply disjoint_left.mpr
    rintro z hzb ⟨w, hw⟩
    have hzC : z ∈ C := hw ▸ interior_subset (hvC w)
    have hz0 : z = b i 0 := mem_singleton_iff.mp ((hbC i).subset ⟨hzb, hzC⟩)
    exact (hb0 i).2 (hz0 ▸ (hw ▸ hvC w))
  have hmissX : ∀ i, Disjoint (range (b i)) (range x) := by
    intro i
    apply disjoint_left.mpr
    rintro z hzb ⟨j, hj⟩
    have hzZ : z ∈ Z := hj ▸ interior_subset (hxZ j)
    have hz1 : z = b i 1 := mem_singleton_iff.mp ((hbZ i).subset ⟨hzb, hzZ⟩)
    exact (hb1 i).2 (hz1 ▸ (hj ▸ hxZ j))
  have hbb : ∀ i j, i ≠ j → Disjoint (range (b i)) (range (b j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro z hzi hzj
    rcases hLL i j hij ⟨hsub i hzi, hsub j hzj⟩ with hzV | hzX
    · exact disjoint_left.mp (hmissV i) hzi hzV
    · exact disjoint_left.mp (hmissX i) hzi hzX
  refine ⟨A, b, (fun w => (hA w).1), hAA, hAZ, hb, hbb, hb0bd, hb1Z, ?_, hsub, hb1⟩
  intro i
  change range (b i) ∩ (Z ∪ C) = _
  rw [inter_union_distrib_left, hbZ i, hbC i]
  exact pair_comm _ _

end GraphMinor.GM12

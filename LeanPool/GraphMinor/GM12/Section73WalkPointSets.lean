/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Ties

/-!
# Point sets of the replacement paths

For XII (7.3), page 261, the point set of a replacement path is the
union of its old edge closures. Concatenation takes unions and
reversal preserves the point set. These formulas let the lifted walk
be compared with the new walk outside the merged region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The point set of an empty walk is its single vertex. -/
theorem walkDrawing_nil_points
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {x : S} (hx : x ∈ K.V) :
    (walkDrawing K (.nil hx)).U = {x} := by
  ext z
  rw [mem_walkDrawing_U]
  change (z ∈ ([x] : List S) ∨ ∃ e ∈ ([] : List (Set S)), z ∈ closure e) ↔ z = x
  simp

/-- Prepending an edge adds its closure to the walk's point set. -/
theorem walkDrawing_cons_points
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {e : Set S} {x y z : S}
    (he : K.toGraph.IsLink e x y) (W : GraphWalk K.toGraph y z) :
    (walkDrawing K (.cons he W)).U = closure e ∪ (walkDrawing K W).U := by
  ext a
  rw [mem_walkDrawing_U]
  constructor
  · rintro (haV | ⟨g, hg, hag⟩)
    · rcases List.mem_cons.mp haV with hax | haW
      · exact Or.inl (hax ▸ (he.2.2.2.superset (Or.inl rfl)).1)
      · exact Or.inr ((mem_walkDrawing_U K W).mpr (Or.inl haW))
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact Or.inl hag
      · exact Or.inr ((mem_walkDrawing_U K W).mpr (Or.inr ⟨g, hg, hag⟩))
  · rintro (hae | haW)
    · exact Or.inr ⟨e, List.mem_cons_self, hae⟩
    · rcases (mem_walkDrawing_U K W).mp haW with haV | ⟨g, hg, hag⟩
      · exact Or.inl (List.mem_cons_of_mem _ haV)
      · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, hag⟩

/-- A one-edge walk has the closure of that edge as point set. -/
theorem walkDrawing_one_edge_points
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {e : Set S} {x y : S}
    (he : K.toGraph.IsLink e x y) :
    (walkDrawing K (.cons he (.nil he.2.2.1))).U = closure e := by
  rw [walkDrawing_cons_points, walkDrawing_nil_points]
  exact union_eq_left.mpr (singleton_subset_iff.mpr (he.2.2.2.superset (Or.inr rfl)).1)

/-- A two-edge path has the union of the two edge closures as its
point set, as used in XII (7.3), page 261. -/
theorem walkDrawing_two_edges_points
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {e g : Set S} {x y z : S}
    (he : K.toGraph.IsLink e x y) (hg : K.toGraph.IsLink g y z) :
    (walkDrawing K (.cons he (.cons hg (.nil hg.2.2.1)))).U = closure e ∪ closure g := by
  rw [walkDrawing_cons_points, walkDrawing_one_edge_points]

/-- Reversal leaves a walk's point set unchanged. -/
theorem walkDrawing_reverse_points
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {x y : S}
      (W : GraphWalk K.toGraph x y) :
    (walkDrawing K W.reverse).U = (walkDrawing K W).U := by
  ext z
  exact GM11.mem_U_reverse

/-- Concatenation unions the point sets of its two walks. -/
theorem walkDrawing_append_points
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S} {x y z : S}
    (W : GraphWalk K.toGraph x y) (W' : GraphWalk K.toGraph y z) :
    (walkDrawing K (W.append W')).U = (walkDrawing K W).U ∪ (walkDrawing K W').U := by
  ext a
  exact GM11.mem_U_append

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# Walks in disjoint unions of drawings

For the feasibility forest in XII (3.1), page 245, every walk stays
in its starting local forest. An edge in another component would put
its first endpoint in two disjoint vertex sets. Thus acyclicity and
boundary connection classes pass from the local forests to their union.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A walk in a drawing covered by disjoint subdrawings stays in the
component containing its first vertex. -/
theorem walk_stays_in_disjoint_family
    {S ι : Type*} [TopologicalSpace S] (H : ι → Drawing S) (K : Drawing S)
    (hsub : ∀ i, (H i).IsSubdrawing K)
    (hdis : Pairwise (fun i j => Disjoint (H i).V (H j).V))
    (hE : K.E ⊆ ⋃ i, (H i).E) (i : ι)
    {u v : S} (W : GraphWalk K.toGraph u v) (hu : u ∈ (H i).V) :
    (∀ x ∈ W.support, x ∈ (H i).V) ∧ (∀ e ∈ W.edges, e ∈ (H i).E) := by
  revert hu
  induction W with
  | nil huK =>
    intro hu
    constructor
    · intro x hx
      exact (List.mem_singleton.mp hx) ▸ hu
    · intro e he
      exact False.elim (List.not_mem_nil he)
  | @cons u v w e he rest ih =>
    intro hu
    have hei : e ∈ (H i).E := by
      obtain ⟨j, hej⟩ := mem_iUnion.mp (hE he.1)
      by_cases hji : j = i
      · exact hji ▸ hej
      · have hjlink := ((hsub j).isLink_iff hej).mpr he
        exact False.elim (Set.disjoint_left.mp (hdis (Ne.symm hji)) hu hjlink.2.1)
    have hilink := ((hsub i).isLink_iff hei).mpr he
    obtain ⟨hrestV, hrestE⟩ := ih hilink.2.2.1
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with hxu | hxrest
      · exact hxu ▸ hu
      · exact hrestV x hxrest
    · intro f hf
      rcases List.mem_cons.mp hf with hfe | hfrest
      · exact hfe ▸ hei
      · exact hrestE f hfrest

/-- A drawing covered by a disjoint family of forest subdrawings is
itself a forest, because each closed walk stays in one member. -/
theorem isGraphForest_of_disjoint_family_cover
    {S ι : Type*} [TopologicalSpace S] (H : ι → Drawing S) (K : Drawing S)
    (hsub : ∀ i, (H i).IsSubdrawing K)
    (hdis : Pairwise (fun i j => Disjoint (H i).V (H j).V))
    (hV : K.V ⊆ ⋃ i, (H i).V) (hE : K.E ⊆ ⋃ i, (H i).E)
    (hforest : ∀ i, IsGraphForest (H i).toGraph) : IsGraphForest K.toGraph := by
  intro u W hW
  have hu : u ∈ K.V := W.mem_vertexSet_of_mem_support W.start_mem_support
  obtain ⟨i, hui⟩ := mem_iUnion.mp (hV hu)
  obtain ⟨hWV, hWE⟩ := walk_stays_in_disjoint_family H K hsub hdis hE i W hui
  obtain ⟨W', hs, he⟩ := (hsub i).exists_walk_down W hWV hWE
  have hW' : W'.IsSimpleClosed := by
    change W'.support.tail.Nodup ∧ W'.edges.Nodup
    rw [hs, he]
    exact hW
  have hzero := hforest i u W' hW'
  change W.edges.length = 0
  rw [← he]
  exact hzero

/-- A connected member of a disjoint family gives exactly one
boundary connection class in their union drawing. -/
theorem walk_iff_mem_boundary_class_of_disjoint_family
    {S ι : Type*} [TopologicalSpace S] (H : ι → Drawing S) (K : Drawing S)
    (hsub : ∀ i, (H i).IsSubdrawing K)
    (hdis : Pairwise (fun i j => Disjoint (H i).V (H j).V))
    (hE : K.E ⊆ ⋃ i, (H i).E) (i : ι) (hconn : IsConnectedDrawing (H i))
    {x y : S} (hx : x ∈ (H i).V ∩ bd S) (hy : y ∈ K.V ∩ bd S) :
    Nonempty (GraphWalk K.toGraph x y) ↔ y ∈ (H i).V ∩ bd S := by
  constructor
  · rintro ⟨W⟩
    have hWV := (walk_stays_in_disjoint_family H K hsub hdis hE i W hx.1).1
    exact ⟨hWV y W.end_mem_support, hy.2⟩
  · intro hyi
    obtain ⟨W⟩ := hconn x hx.1 y hyi.1
    obtain ⟨W', _, _⟩ := (hsub i).exists_walk_up W
    exact ⟨W'⟩

end GraphMinor.GM12

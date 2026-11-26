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
# Connected subdrawings selected by their vertex classes

The conclusion of XII (3.1), page 245, asks for connected subdrawings
with prescribed boundary vertices. The forest supplied by VII has the
same boundary-connection classes as the feasible forest. This file
constructs the connected subdrawing of a drawing containing a chosen
vertex. Its vertices are exactly the vertices reachable from that point.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The vertices reachable from a chosen vertex form a connected
subdrawing. This supplies the component subdrawings in the reduction
from VII's feasible forest to the conclusion of XII (3.1). -/
theorem exists_connected_subdrawing_of_reachability {S : Type*} [TopologicalSpace S]
    [T1Space S] (H : Drawing S) {z : S} (hz : z ∈ H.V) :
    ∃ C : Drawing S, C.IsSubdrawing H ∧ IsConnectedDrawing C ∧ z ∈ C.V ∧
      C.V = {y | Nonempty (GraphWalk H.toGraph z y)} := by
  let R : Set S := {y | Nonempty (GraphWalk H.toGraph z y)}
  let E : Set (Set S) := {e | ∃ p q, p ∈ R ∧ q ∈ R ∧ H.toGraph.IsLink e p q}
  let C := H.span R E
  have hRV : R ⊆ H.V := by
    rintro x ⟨W⟩
    exact W.mem_vertexSet_of_mem_support W.end_mem_support
  have hEH : E ⊆ H.E := by
    rintro e ⟨p, q, _, _, hl⟩
    exact hl.1
  have hCV : C.V = R := by
    apply Subset.antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, ⟨he, _⟩, hxe, hxV⟩ := mem_iUnion₂.mp hx
        obtain ⟨p, q, hp, hq, hl⟩ := he
        have hm : x ∈ ({p, q} : Set S) := hl.2.2.2 ▸ ⟨hxe, hxV⟩
        rcases hm with h | h
        · exact h ▸ hp
        · exact h ▸ hq
    · intro x hx
      exact Or.inl ⟨hx, hRV hx⟩
  have hCE : C.E = E := (H.span_E R E).trans (inter_eq_left.mpr hEH)
  have hsub : C.IsSubdrawing H := H.span_isSubdrawing R E
  have reach_support : ∀ {x y : S}, x ∈ R → ∀ (W : GraphWalk H.toGraph x y),
      ∀ v ∈ W.support, v ∈ R := by
    rintro x y ⟨P⟩ W v hv
    obtain ⟨Q, _, _⟩ := W.exists_append_of_mem hv
    exact ⟨P.append Q⟩
  refine ⟨C, hsub, ?_, ?_, hCV⟩
  swap
  · rw [hCV]
    exact ⟨.nil hz⟩
  intro x hx y hy
  have hxR : x ∈ R := hCV ▸ hx
  have hyR : y ∈ R := hCV ▸ hy
  let P := Classical.choice hxR
  let Q := Classical.choice hyR
  let W := P.reverse.append Q
  have hV : ∀ v ∈ W.support, v ∈ C.V := fun v hv => hCV.symm ▸ reach_support hxR W v hv
  have hE : ∀ e ∈ W.edges, e ∈ C.E := by
    intro e he
    have heH : e ∈ H.E := (walkDrawing_isSubdrawing H W).2 (by rw [walkDrawing_E]; exact he)
    obtain ⟨p, q, hl⟩ := (H.toGraph.edge_mem_iff_exists_isLink e).mp heH
    rw [hCE]
    exact ⟨p, q, reach_support hxR W p (W.left_mem_support_of_mem_edges he hl),
      reach_support hxR W q (W.left_mem_support_of_mem_edges he hl.symm), hl⟩
  obtain ⟨W', _, _⟩ := hsub.exists_walk_down W hV hE
  exact ⟨W'⟩

/-- Boundary-connection classes in a subdrawing give the disjoint
connected subdrawings required by XII (3.1), page 245. Each prescribed
nonempty class selects one component of the feasible forest. -/
theorem hasConnectingSubdrawings_of_connection_classes {S : Type*} [TopologicalSpace S]
    [T1Space S] {Γ H : Drawing S} (hH : H.IsSubdrawing Γ)
    {p : ℕ} {Z : Set S} {Zs : Fin p → Set S} (hZH : Z ⊆ H.V)
    (hZs : ∀ j, Zs j ⊆ Z) (hne : ∀ j, (Zs j).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hclasses : ∀ j, ∀ x ∈ Zs j, ∀ y ∈ Z,
      Nonempty (GraphWalk H.toGraph x y) ↔ y ∈ Zs j) :
    HasConnectingSubdrawings Γ Z Zs := by
  classical
  choose z hz using hne
  have hex : ∀ j, ∃ C : Drawing S, C.IsSubdrawing H ∧ IsConnectedDrawing C ∧
      z j ∈ C.V ∧ C.V = {y | Nonempty (GraphWalk H.toGraph (z j) y)} := by
    intro j
    exact exists_connected_subdrawing_of_reachability H (hZH (hZs j (hz j)))
  choose C hCH hCc hzC hCV using hex
  refine ⟨C, fun j => (hCH j).trans hH, hCc, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hPi : Nonempty (GraphWalk H.toGraph (z i) x) := by rw [hCV i] at hxi; exact hxi
    have hPj : Nonempty (GraphWalk H.toGraph (z j) x) := by rw [hCV j] at hxj; exact hxj
    obtain ⟨Pi⟩ := hPi
    obtain ⟨Pj⟩ := hPj
    have hzji : z j ∈ Zs i := (hclasses i (z i) (hz i) (z j) (hZs j (hz j))).mp
      ⟨Pi.append Pj.reverse⟩
    exact Set.disjoint_left.mp (hdis i j hij) hzji (hz j)
  · intro j
    ext y
    constructor
    · rintro ⟨hyC, hyZ⟩
      have hyR : Nonempty (GraphWalk H.toGraph (z j) y) := by rw [hCV j] at hyC; exact hyC
      exact (hclasses j (z j) (hz j) y hyZ).mp hyR
    · intro hy
      have hyZ := hZs j hy
      refine ⟨?_, hyZ⟩
      have hyR := (hclasses j (z j) (hz j) y hyZ).mpr hy
      rw [hCV j]
      exact hyR

end GraphMinor.GM12

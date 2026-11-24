/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.GM11.Separate

/-!
# Intersections of maximal circuit insides

The circuit-chain distance calculation of XII (4.1), page 248, can be
witnessed by a closed walk along the circuit boundaries. To join those
walks, retain maximal circuit insides. Two such insides that meet have
boundaries that meet: otherwise XI (7.7) makes them nested. The second
tangle condition rules out their covering the surface. Subdrawings of one drawing
whose point sets meet have a vertex in common.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM10 GM11 GM14

universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
private theorem preconnected_oArc {F : Set S} (hF : IsOArc F) : IsPreconnected F := by
  obtain ⟨f⟩ := hF
  have heq : F = range (fun z : Circle => (f z).val) := by
    ext x
    exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, by simp⟩,
      fun ⟨z, hz⟩ => hz ▸ (f z).property⟩
  rw [heq]
  exact isPreconnected_range (continuous_subtype_val.comp f.continuous)

omit [T2Space S] in
/-- A point of a subdrawing that is an ambient vertex is a vertex of the
subdrawing. An edge closure has the same ends in both drawings. -/
theorem subdrawing_vertex_of_mem_U {C K : Drawing S} (hs : C.IsSubdrawing K)
    {x : S} (hx : x ∈ C.U) (hxK : x ∈ K.V) : x ∈ C.V := by
  rw [C.U_eq] at hx
  rcases hx with hx | hx
  · exact hx
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    have hm : x ∈ closure e ∩ C.V := by
      rw [hs.closure_inter_V he]
      exact ⟨hxe, hxK⟩
    exact hm.2

omit [T2Space S] in
/-- Two subdrawings with a common point have a common vertex. If that
point is in an edge, both drawings contain that edge and its ends. -/
theorem subdrawings_common_vertex {C D K : Drawing S}
    (hC : C.IsSubdrawing K) (hD : D.IsSubdrawing K)
    (h : (C.U ∩ D.U).Nonempty) : (C.V ∩ D.V).Nonempty := by
  obtain ⟨x, hxC, hxD⟩ := h
  by_cases hxK : x ∈ K.V
  · exact ⟨x, subdrawing_vertex_of_mem_U hC hxC hxK,
      subdrawing_vertex_of_mem_U hD hxD hxK⟩
  obtain ⟨e, heC, hxe⟩ := C.exists_edge_of_mem hxC (fun hx => hxK (hC.1 hx))
  obtain ⟨f, hfD, hxf⟩ := D.exists_edge_of_mem hxD (fun hx => hxK (hD.1 hx))
  have hef : e = f := K.edge_eq_of_mem (hC.2 heC) (hD.2 hfD) hxe hxf
  subst f
  obtain ⟨y, z, hl⟩ := C.toGraph.exists_isLink_of_mem_edgeSet heC
  have hy : y ∈ closure e := by
    have : y ∈ closure e ∩ C.V := by rw [hl.2.2.2]; simp
    exact this.1
  have hm : y ∈ closure e ∩ D.V := by
    rw [hD.closure_inter_V hfD]
    exact ⟨hy, hC.1 hl.left_mem⟩
  exact ⟨y, hl.left_mem, hm.2⟩

/-- Overlapping maximal circuit insides have a common boundary vertex.
This supplies insertion points for the closed-walk form of the first
inequality in XII (4.1), page 248. -/
theorem common_vertex_of_maximal_insides [ConnectedSpace S]
    {Γ K C D : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing K) (hCl : C.length < 2 * θ)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K) (hDl : D.length < 2 * θ)
    (hmaxC : ins C ⊆ ins D → ins D ⊆ ins C)
    (hmaxD : ins D ⊆ ins C → ins C ⊆ ins D)
    (hmeet : (ins C ∩ ins D).Nonempty) : (C.V ∩ D.V).Nonempty := by
  obtain ⟨hdiscC, hbdC, hmC⟩ := hd C hC hCs hCl
  obtain ⟨hdiscD, hbdD, hmD⟩ := hd D hD hDs hDl
  have hneq : ins C ∪ ins D ≠ univ := by
    intro heq
    have hfrC : frontier (ins C) ⊆ K.U := by
      rw [← subBd_eq_frontier, hbdC]
      exact hCs.U_subset
    have hfrD : frontier (ins D) ⊆ K.U := by
      rw [← subBd_eq_frontier, hbdD]
      exact hDs.U_subset
    apply not_cover (Γ := .drawing Γ) (Γ' := K) hT hK.2.1.1 hdiscC.isClosed hdiscD.isClosed
      hdiscD.isClosed
      hfrC hfrD hfrD hmC hmD hmD
    rw [Set.union_assoc, Set.union_self, heq]
  apply subdrawings_common_vertex hCs hDs
  by_contra hn
  have hdisj : Disjoint (subBd (ins C)) (subBd (ins D)) := by
    rw [hbdC, hbdD]
    exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
  have hpreC : IsPreconnected (subBd (ins C)) := by
    rw [hbdC]
    exact preconnected_oArc (IsCircuit.isOArc_U hC)
  have hpreD : IsPreconnected (subBd (ins D)) := by
    rw [hbdD]
    exact preconnected_oArc (IsCircuit.isOArc_U hD)
  have heq : ins C = ins D := by
    rcases theorem_7_7_proof hpreC hpreD hmeet hneq hdisj with h | h
    · exact subset_antisymm h (hmaxC h)
    · exact subset_antisymm (hmaxD h) h
  have hUeq : C.U = D.U := hbdC.symm.trans ((congrArg subBd heq).trans hbdD)
  obtain ⟨u, W, _, _, hV, _⟩ := hC
  have hu : u ∈ C.U := C.V_subset_U (hV ▸ W.start_mem_support)
  exact hn ⟨u, hu, hUeq ▸ hu⟩

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.NiceStatements
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM12.Section1

/-!
# A path portion forces its incident edge into a circuit inside

In XII (4.3), claim (1), page 250, a path portion misses the radial
circuit and has one end in its inside. Its whole point set is then in
the interior of that inside. An original edge incident with its other
end also lies inside: it misses the radial circuit and meets the
interior near the common end.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The connected-set containment step of XII (4.3), claim (1), page 250. -/
theorem incident_edge_subset_of_path_inside
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ K C : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hC : C.IsSubdrawing K) {D : Set S} (hD : IsClosed D)
    (hbd : frontier D = C.U) {a b : S} (P : GraphWalk Γ.toGraph a b)
    (hdis : Disjoint (walkDrawing Γ P).U C.U)
    (hb : b ∈ D) {e : Set S} (he : e ∈ Γ.E) (ha : a ∈ closure e) : e ⊆ D := by
  have hpre : IsPreconnected (walkDrawing Γ P).U := by
    have heq : (walkDrawing Γ P).U =
        {x | x ∈ P.support ∨ ∃ e ∈ P.edges, x ∈ closure e} := by
      ext x
      exact mem_walkDrawing_U Γ P
    rw [heq]
    exact (isPathConnected_walk_U P).isConnected.isPreconnected
  have haP : a ∈ (walkDrawing Γ P).U :=
    (mem_walkDrawing_U Γ P).mpr (Or.inl P.start_mem_support)
  have hbP : b ∈ (walkDrawing Γ P).U :=
    (mem_walkDrawing_U Γ P).mpr (Or.inl P.end_mem_support)
  have hdis' : Disjoint (walkDrawing Γ P).U (frontier D) := hbd ▸ hdis
  have hsub : (walkDrawing Γ P).U ⊆ D :=
    subset_of_disjoint_frontier hpre hD hdis' hbP hb
  have hai : a ∈ interior D := by
    rw [← self_sdiff_frontier]
    exact ⟨hsub haP, fun h => Set.disjoint_left.mp hdis' haP h⟩
  have hedis : Disjoint e (frontier D) := by
    rw [hbd]
    apply Set.disjoint_left.mpr
    intro x hxe hxC
    have hxΓ : x ∈ Γ.U := (PaintingOrDrawing.edge_props (Γ := .drawing Γ) he).2.2.1 hxe
    have hxK : x ∈ K.U := hC.U_subset hxC
    have hxV : x ∈ Γ.V := by
      have hx : x ∈ (PaintingOrDrawing.drawing Γ).U ∩ K.U := ⟨hxΓ, hxK⟩
      rw [hK.2.1.1] at hx
      exact hx
    exact Set.disjoint_left.mp (PaintingOrDrawing.edge_props (Γ := .drawing Γ) he).2.1 hxe hxV
  obtain ⟨x, hxi, hxe⟩ := mem_closure_iff.mp ha (interior D) isOpen_interior hai
  exact subset_of_disjoint_frontier (PaintingOrDrawing.edge_props (Γ := .drawing Γ) he).1 hD hedis
    hxe
    (interior_subset hxi)

end GraphMinor.GM12

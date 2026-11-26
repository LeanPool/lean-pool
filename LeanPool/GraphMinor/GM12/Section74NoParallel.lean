/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73NoParallel
public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM07.Section3

/-!
# The radial star in the base case of XII (7.4)

The induction base on pages 262--263 excludes selected normal
one-vertex discs containing an edge. Such a disc contains no
other old vertex either: an edge at that vertex would meet the
disc interior and could not cross the normal boundary. Thus a
pair of parallel spokes at the deleted vertex would bound a
disc contained in one old region with the vertex restored,
contrary to the pre-radial condition. This argument does not
presuppose that vertex deletion is two-cell.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14

/-- A normal one-vertex disc containing no old edge contains no
other old vertex, when the drawing has an edge. -/
theorem vertices_in_normal_vertex_disc_of_no_edges
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) (hE : Γ.E.Nonempty)
    {D F : Set S} {v : S} (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hno : ∀ e ∈ Γ.E, ¬ e ⊆ D) : Γ.V ∩ D = {v} := by
  have hfront : frontier D = F := (subBd_eq_frontier D).symm.trans hbd
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨hvFV.2,
    hD.isClosed.closure_subset_iff.mpr subset_rfl (hfront.symm ▸ hvFV.1).1⟩)
  intro w hw
  by_contra hwv
  have hwint : w ∈ interior D := by
    by_contra h
    exact hwv (hFV ▸ (⟨hfront ▸ (⟨subset_closure hw.2, h⟩ : w ∈ frontier D), hw.1⟩ : w ∈ F ∩ Γ.V))
  obtain ⟨e, he, hwe⟩ := exists_edge_at hK hS hE hw.1
  obtain ⟨x, hxint, hxe⟩ := mem_closure_iff.mp hwe _ isOpen_interior hwint
  have hdis : Disjoint e (frontier D) := by
    apply disjoint_left.mpr
    intro y hye hyF
    exact (he.2.1 hye).2 (hn ⟨hfront ▸ hyF, (he.2.1 hye).1⟩)
  exact hno e he (subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected
    hD.isClosed hdis hxe (interior_subset hxint))

/-- In the no-selected-edge base case of XII (7.4), a radial
star at the deleted vertex has no parallel spokes. Unlike the
corresponding preprocessing lemma for (7.3), this does not assume
that the deletion is two-cell. -/
theorem no_parallel_spokes_in_theorem_7_4_base
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {v : S} (hv : v ∈ Γ.V)
    (hno : ∀ D F : Set S, IsClosedDisc D → IsOArc F → subBd D = F →
      (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {v} →
      ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ∀ e ∈ Γ.E, ¬ e ⊆ D)
    {g h r : Set S} {u : S} (hg : g ∈ K.E) (hh : h ∈ K.E) (hgh : g ≠ h)
    (hr : r ∈ Γ.R) (hur : u ∈ r) (huK : u ∈ K.V)
    (hcapg : closure g ∩ K.V = {v, u}) (hcaph : closure h ∩ K.V = {v, u}) : False := by
  apply parallel_spokes_contradiction hS hθ hT hK hv hg hh hgh hr hur huK hcapg hcaph
  intro D F hD hF hbd hn hFV _ hm
  have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hT.2.1 hθ
  have hnone := hno D F hD hF hbd hn hFV hm
  exact ⟨vertices_in_normal_vertex_disc_of_no_edges hS ⟨hT.1, hK⟩ hE hD hbd hn hFV hnone, hnone⟩

end GraphMinor.GM12

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM16.GraphDrawingSpanEmbedding
import LeanPool.GraphMinor.GM16.GraphDrawingForwardMaps
import LeanPool.GraphMinor.GM16.ControlFromInducedTangle
import LeanPool.GraphMinor.GM16.GraphIsoImage
import LeanPool.GraphMinor.GM16.HypergraphSupportedTangle
import LeanPool.GraphMinor.GM16.DrawingSkeletonPaths

/-!
# A controlled tangle on a drawn subgraph

Transport the subgraph tangle through the graph drawing's
isomorphism, using maps injective only on actual names. Invert
the same isomorphism to obtain the span embedding. The forward
and inverse edge maps cancel on the subgraph edges, so conformity
of the induced tangle gives the control condition. This supplies
the controlled drawing tangle for the sphere span in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph Surface GM10 GM14 GM15
universe u v w

/-- A conformal subgraph tangle transfers to a controlled tangle
in any graph drawing of that subgraph. -/
theorem exists_controlled_drawing_tangle
    {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {S : Type w} [TopologicalSpace S] [Nonempty S]
    {G N : Graph α β} {θstar θ : ℕ} {Tstar : Set (Hypergraph α β × Hypergraph α β)}
    (hTstar : IsGraphTangle G θstar Tstar) (hθ : θ ≤ θstar) (hNG : N ≤ G)
    (hVN : V(N).Finite) (hEN : E(N).Finite)
    (Γ : GraphDrawing N S) (TN : Set (Hypergraph α β × Hypergraph α β))
    (hTN : IsTangle (Hypergraph.ofGraph N hVN hEN) θ TN)
    (hConformal : inducedTangle (Hypergraph.ofGraph G hTstar.finite_V hTstar.finite_E)
      (Hypergraph.ofGraph N hVN hEN) TN θ ⊆ Tstar) :
    ∃ (η : SpanEmbedding Γ.drawing G)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
      η.imageGraph=N ∧ IsControllingTangle G Γ.drawing η θstar θ Tstar T := by
  obtain ⟨η,hImage,hηV,hηE⟩ := exists_spanEmbedding_of_graphDrawing hNG Γ
  obtain ⟨f,g,hf,hg,hfInj,hgInj⟩ := exists_graphDrawing_forward_maps Γ
  have hHyp : imageHypergraph f g (Hypergraph.ofGraph N hVN hEN)=Γ.drawing.toHypergraph :=
    (imageHypergraph_of_iso hVN hEN Γ.drawing.finite_V Γ.drawing.finite_edges Γ.iso f g
      (fun x => (hf x).symm) (fun e => (hg e).symm)).trans (drawing_ofGraph_toGraph Γ.drawing)
  have hTD : IsTangle Γ.drawing.toHypergraph θ (imageHypergraphTangle f g TN) := by
    rw [← hHyp]
    exact isTangle_imageHypergraphTangle_on f g hfInj hgInj hTN
  have hInv : LeftInvOn η.eMap g E(N) := by
    intro e he
    rw [hg ⟨e,he⟩,hηE (Γ.iso.edgeEquiv ⟨e,he⟩)]
    exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm_apply_apply ⟨e,he⟩)
  exact ⟨η,imageHypergraphTangle f g TN,hImage,
    controllingTangle_of_induced_subset η hImage hTstar hθ hVN hEN TN hTN f g hInv hTD hConformal⟩

end GraphMinor.GM16

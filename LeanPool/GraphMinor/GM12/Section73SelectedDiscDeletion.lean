/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73Separator
public import LeanPool.GraphMinor.GM12.Section73Tangle
import LeanPool.GraphMinor.GM12.Section73DiscPreprocess
import LeanPool.GraphMinor.GM12.Section72Tangle

/-!
# Selected disc separations survive vertex deletion

In XII (7.3), Claim (1), page 262, an old selected disc gives
a selected separation in the deleted tangle. First add the deleted
vertex to both sides and apply X (2.9). Deleting the vertex then
recovers exactly the intersections of the new drawing with the
same disc and its closed outside.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM10 Hypergraph

/-- Closed-set intersection commutes with vertex deletion at the
level of the separation hypergraphs. This identifies the two sides
in XII (7.3), Claim (1), page 262. -/
theorem drawing_inter_deleteVertices
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) (Z : Set S) {X : Set S} (hX : IsClosed X) :
    (PaintingOrDrawing.drawing (deleteVertices Γ Z)).inter X =
      ((PaintingOrDrawing.drawing Γ).inter X).deleteVertices Z := by
  rw [← interSet_toHypergraph _ hX, ← deleteVertices_interSet hX,
    deleteVertices_toHypergraph, interSet_toHypergraph Γ hX]

/-- A selected old disc still selects its inside after deletion,
provided putting the deleted vertex on both sides keeps the order
below the old tangle order. This is the separation-transfer step
of XII (7.3), Claim (1), page 262. -/
theorem selected_disc_mem_deleted_tangle
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) {v : S} (hv : v ∈ Γ.V)
    {D : Set S} (hD : IsClosed D)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hord : separationOrder
      ((PaintingOrDrawing.drawing Γ).inter D ∪ vertexHypergraph v)
      ((PaintingOrDrawing.drawing Γ).interOutside D ∪ vertexHypergraph v) < θ) :
    ((PaintingOrDrawing.drawing (deleteVertices Γ {v})).inter D,
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).interOutside D) ∈
        deleteVerticesTangle Γ.toHypergraph {v} T θ := by
  have hm' := delete_pair_mem_tangle_of_adjoin_order hT hm hv hord
  change (((PaintingOrDrawing.drawing Γ).inter D).deleteVertices {v},
    ((PaintingOrDrawing.drawing Γ).inter (closure (univ \ D))).deleteVertices {v}) ∈ _ at hm'
  rw [← drawing_inter_deleteVertices Γ {v} hD,
    ← drawing_inter_deleteVertices Γ {v} isClosed_closure] at hm'
  exact hm'

end GraphMinor.GM12

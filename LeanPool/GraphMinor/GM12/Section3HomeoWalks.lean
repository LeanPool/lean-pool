/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# Graph walks under homeomorphisms of drawings

In the reduction of XII (3.1), page 245, VII supplies a forest up to
homoplasty. Its boundary-fixing homeomorphism preserves connectivity.
Map every edge and vertex of a walk through the homeomorphism. Mapping
back by the inverse gives the converse, so the boundary connection
classes are unchanged.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM07 GM11

/-- The edges of the homeomorphic image are the images of the edges. -/
theorem mapDrawingHomeo_edges {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (α : S ≃ₜ T) (H : Drawing S) :
    (mapDrawingHomeo α H).E = (image α) '' H.E := by
  change arcComponentsIn (α '' H.U \ α '' H.V) = (image α) '' arcComponentsIn (H.U \ H.V)
  rw [← image_sdiff α.injective, arcComponentsIn_image_homeo]

/-- A graph link maps to a link of the image drawing. -/
theorem isLink_mapDrawingHomeo {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (α : S ≃ₜ T) (H : Drawing S) {e : Set S} {x y : S} (hl : H.toGraph.IsLink e x y) :
    (mapDrawingHomeo α H).toGraph.IsLink (α '' e) (α x) (α y) := by
  refine ⟨?_, ⟨x, hl.2.1, rfl⟩, ⟨y, hl.2.2.1, rfl⟩, ?_⟩
  · rw [mapDrawingHomeo_edges]
    exact ⟨e, hl.1, rfl⟩
  · change closure (α '' e) ∩ α '' H.V = {α x, α y}
    rw [← α.image_closure, ← Set.image_inter α.injective, hl.2.2.2, image_pair]

/-- A walk maps to a walk of the image drawing with the image vertex
list. In particular, graph connectivity is preserved. -/
theorem exists_walk_mapDrawingHomeo {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (α : S ≃ₜ T) (H : Drawing S) {x y : S} (W : GraphWalk H.toGraph x y) :
    ∃ W' : GraphWalk (mapDrawingHomeo α H).toGraph (α x) (α y),
      W'.support = W.support.map α := by
  induction W with
  | nil hx =>
    exact ⟨.nil ⟨_, hx, rfl⟩, rfl⟩
  | cons hl rest ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨.cons (isLink_mapDrawingHomeo α H hl) R,
      congrArg (List.cons _) hR⟩

/-- Mapping a drawing by a homeomorphism and its inverse recovers it. -/
theorem mapDrawingHomeo_symm {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (α : S ≃ₜ T) (H : Drawing S) :
    mapDrawingHomeo α.symm (mapDrawingHomeo α H) = H := by
  apply Drawing.ext_of_V_E
  · change α.symm '' (α '' H.V) = H.V
    rw [image_image]
    simp only [α.symm_apply_apply]
    exact Set.image_id _
  · rw [mapDrawingHomeo_edges, mapDrawingHomeo_edges, image_image]
    have hset : ∀ E : Set S, α.symm '' (α '' E) = E := by
      intro E
      rw [image_image]
      simp only [α.symm_apply_apply]
      exact Set.image_id _
    simp only [hset]
    exact Set.image_id _

/-- Connectivity of vertices is equivalent to connectivity of their
images under a homeomorphism of drawings. This is the homeomorphism
part of the boundary-class transfer in XII (3.1). -/
theorem walk_mapDrawingHomeo_iff {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (α : S ≃ₜ T) (H : Drawing S) {x y : S} :
    Nonempty (GraphWalk (mapDrawingHomeo α H).toGraph (α x) (α y)) ↔
      Nonempty (GraphWalk H.toGraph x y) := by
  constructor
  · rintro ⟨W⟩
    obtain ⟨R, _⟩ := exists_walk_mapDrawingHomeo α.symm (mapDrawingHomeo α H) W
    have hR : Nonempty (GraphWalk (mapDrawingHomeo α.symm (mapDrawingHomeo α H)).toGraph
        (α.symm (α x)) (α.symm (α y))) := ⟨R⟩
    rw [mapDrawingHomeo_symm, α.symm_apply_apply, α.symm_apply_apply] at hR
    exact hR
  · rintro ⟨W⟩
    obtain ⟨R, _⟩ := exists_walk_mapDrawingHomeo α H W
    exact ⟨R⟩

end GraphMinor.GM12

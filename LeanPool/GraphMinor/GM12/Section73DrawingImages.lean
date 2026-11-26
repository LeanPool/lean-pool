/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks

/-!
# Determining the image of a circuit from its vertices and edges

For XII (7.3), Claim (1), page 262, identify the collapsed old
circuit with the new circuit. It suffices to check vertices and
open edges. Continuity handles the old edge closures, and the
compactness of the old drawing makes its image closed, so the
new edge closures are included as well.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- To map one drawing's point set into another, it suffices to
map its vertices and open edges there. This checks the forward
inclusion for the collapsed circuit in XII (7.3), Claim (1). -/
theorem drawing_image_subset_of_vertex_edge_images
    {S : Type*} [TopologicalSpace S] {D C : Drawing S} (f : C(S, S))
    (hV : f '' D.V ⊆ C.U) (hE : ∀ e ∈ D.E, f '' e ⊆ C.U) :
    f '' D.U ⊆ C.U := by
  rintro z ⟨x, hx, rfl⟩
  rw [D.U_eq] at hx
  rcases hx with hxV | hxE
  · exact hV ⟨x, hxV, rfl⟩
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
    have hximg : f x ∈ closure (f '' e) := image_closure_subset_closure_image f.continuous
      ⟨x, hxe, rfl⟩
    exact closure_minimal (hE e he) C.isClosed_U hximg

/-- On a compact Hausdorff surface the collapsed drawing equals
the new drawing once the forward vertex and edge images and the
reverse vertex and edge containments are known. This identifies
the circuit image in XII (7.3), Claim (1), page 262. -/
theorem drawing_image_eq_of_vertex_edge_images
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    {D C : Drawing S} (f : C(S, S))
    (hV : f '' D.V ⊆ C.U) (hE : ∀ e ∈ D.E, f '' e ⊆ C.U)
    (hV' : C.V ⊆ f '' D.U) (hE' : ∀ e ∈ C.E, e ⊆ f '' D.U) :
    f '' D.U = C.U := by
  apply Subset.antisymm (drawing_image_subset_of_vertex_edge_images f hV hE)
  have hclosed : IsClosed (f '' D.U) := (D.isClosed_U.isCompact.image f.continuous).isClosed
  intro x hx
  rw [C.U_eq] at hx
  rcases hx with hxV | hxE
  · exact hV' hxV
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
    exact closure_minimal (hE' e he) hclosed hxe

end GraphMinor.GM12

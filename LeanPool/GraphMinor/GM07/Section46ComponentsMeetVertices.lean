/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section2Euler
import LeanPool.GraphMinor.GM07.Section46SeamEdgeCounts
import LeanPool.GraphMinor.GM07.Section46OldVertices
import LeanPool.GraphMinor.GM07.Section46DrawingContactCount
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Each boundary component before cutting contains an old seam vertex

The cuff bound in VII (4.6), page 226, counts components of `U(L) ∪ bd(Σ)`
using vertices of `J`. Every closed retained edge contains an old seam
vertex, since it is short or linking. Each original cuff also contains
a seam vertex. Connectedness puts such a vertex in the component of
any chosen point, so every component is counted by `V(J)`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

private theorem preconnected_subset_component_of_meets {S : Type*} [TopologicalSpace S]
    {A B C : Set S} (hA : IsPreconnected A) (hAB : A ⊆ B) (hC : C ∈ componentsIn B)
    (hmeet : (A ∩ C).Nonempty) : A ⊆ C := by
  obtain ⟨y, _, rfl⟩ := hC
  obtain ⟨x, hxA, hxC⟩ := hmeet
  rw [connectedComponentIn_eq hxC]
  exact hA.subset_connectedComponentIn hxA hAB

/-- Every component of `U(L) ∪ bd(Σ)` contains a vertex of `J`,
as used for the cuff bound in VII (4.6), page 226. -/
theorem boundary_components_meet_old_vertices {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J J' L : Drawing S}
    (hJ : N.IsSeamGraphFor J) {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t))
    (hLn : HasNoIsolatedVertices L) :
    ∀ C ∈ componentsIn (L.U ∪ bd S), (C ∩ J.V).Nonempty := by
  have : T2Space S := hS.2.1
  have hsubE := L_edges_subset_short_union_linking hγ s t W hcuts hU hV hLE
  have hcpos : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e :=
    fun e => ⟨(hcuts e).1, (hcuts e).2.1, (hcuts e).2.2.1⟩
  have hclV : ∀ f ∈ L.E, (closure f ∩ J.V).Nonempty := by
    intro f hf
    rcases hsubE hf with hshort | hlink
    · rcases J.edge_cond f hshort.1 with ⟨a, b, _, hcap, _⟩ | ⟨a, hcap, _⟩
      · exact ⟨a, hcap ▸ mem_insert a {b}⟩
      · exact ⟨a, hcap ▸ mem_singleton a⟩
    · exact linking_closure_meets_old_vertices hγ s t hcpos hlink
  intro C hC
  obtain ⟨x, hxB, hCx⟩ := hC
  have hxC : x ∈ C := hCx ▸ mem_connectedComponentIn hxB
  have hCmem : C ∈ componentsIn (L.U ∪ bd S) := ⟨x, hxB, hCx⟩
  rcases hxB with hxL | hxbd
  · have hxCover : x ∈ ⋃ f ∈ L.E, closure f := by
      rw [← U_eq_closed_edges_of_no_isolated L hLn]
      exact hxL
    obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxCover
    have hconn : IsPreconnected (closure f) := hf.2.2.1.isConnected.isPreconnected.closure
    have hclSub : closure f ⊆ L.U ∪ bd S := (L.closure_subset_U hf).trans subset_union_left
    have hclC := preconnected_subset_component_of_meets hconn hclSub hCmem ⟨x, hxf, hxC⟩
    obtain ⟨v, hvcl, hvV⟩ := hclV f hf
    exact ⟨v, hclC hvcl, hvV⟩
  · obtain ⟨D, hD, hxD⟩ := (congrArg (fun A => x ∈ A) (sUnion_cuffs (S := S))).mpr hxbd
    have hDconn := ((cuff_statement S hS).2.2 D hD).isConnected'.isPreconnected
    have hDsub : D ⊆ L.U ∪ bd S := fun y hy =>
      .inr (sUnion_cuffs (S := S) ▸ ⟨D, hD, hy⟩)
    have hDC := preconnected_subset_component_of_meets hDconn hDsub hCmem ⟨x, hxD, hxC⟩
    obtain ⟨v, hvD, hvV⟩ := N.cuff_inter_seamV_nonempty hS hJ.1 hD
    exact ⟨v, hDC hvD, hJ.2.2 ▸ hvV⟩

end GraphMinor.GM07

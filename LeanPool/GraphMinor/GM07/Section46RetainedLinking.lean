/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46LongPieces
import LeanPool.GraphMinor.GM07.Section46OldVertices

/-!
# Linking edges are retained in `L`

In VII (4.6), page 226, every linking edge is off the cuffs, because it
lies in a long old edge. Its closure has an old seam vertex, whereas
central edge closures have none. Thus deleting central and cuff edges
retains every linking edge.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- Linking edges belong to the edge set defining `L` in VII (4.6),
page 226. -/
theorem linking_edge_mem_forestSeamEdges {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J J' : Drawing S}
    (hJ : N.IsSeamGraphFor J) {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hsmall : (G.V ∩ bd S).ncard < 2 * μ + w + 2)
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    {f : Set S} (hf : f ∈ linkingEdges G J μ w γ s t) :
    f ∈ forestSeamEdges J' (centralEdges G J μ w γ s t) := by
  have : T2Space S := hS.2.1
  have hcpos : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e :=
    fun e => ⟨(hcuts e).1, (hcuts e).2.1, (hcuts e).2.2.1⟩
  have hW : ∀ e : longSeamEdges G J μ w, W e ⊆ e.1 := by
    intro e x hx
    rw [(hcuts e).2.2.2] at hx
    rcases hx with rfl | rfl
    · exact (congrArg (fun A => γ e.1 (s e) ∈ A) (hγ.image e.1 e.2.1)).mp
        ⟨s e, (hcuts e).1, rfl⟩
    · exact (congrArg (fun A => γ e.1 (t e) ∈ A) (hγ.image e.1 e.2.1)).mp
        ⟨t e, (hcuts e).2.1, rfl⟩
  have hnotcentral : f ∉ centralEdges G J μ w γ s t := by
    intro hc
    obtain ⟨x, hxcl, hxV⟩ := linking_closure_meets_old_vertices hγ s t hcpos hf
    exact disjoint_left.mp (central_closure_disjoint_old_vertices hγ s t hcpos hc) hxcl hxV
  have hnew : f ∈ J'.E ∧ Disjoint f (bd S) := by
    rcases hf with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · have hc := hcuts e
      have hm := long_edge_pieces_mem_J_plus hγ W hW hU hV e hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      have hsub : γ e.1 '' Ioo 0 (s e) ⊆ e.1 := by
        rintro x ⟨u, hu, rfl⟩
        exact (congrArg (fun A => γ e.1 u ∈ A) (hγ.image e.1 e.2.1)).mp
          ⟨u, ⟨hu.1, hu.2.trans hc.1.2⟩, rfl⟩
      exact ⟨hm.1, (longSeamEdge_disjoint_bd_of_ncard_lt hS N hJ hsmall e.2).mono_left hsub⟩
    · have hc := hcuts e
      have hm := long_edge_pieces_mem_J_plus hγ W hW hU hV e hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      have hsub : γ e.1 '' Ioo (t e) 1 ⊆ e.1 := by
        rintro x ⟨u, hu, rfl⟩
        exact (congrArg (fun A => γ e.1 u ∈ A) (hγ.image e.1 e.2.1)).mp
          ⟨u, ⟨hc.2.1.1.trans hu.1, hu.2⟩, rfl⟩
      exact ⟨hm.2.2, (longSeamEdge_disjoint_bd_of_ncard_lt hS N hJ hsmall e.2).mono_left hsub⟩
  refine ⟨hnew.1, hnotcentral, ?_⟩
  intro hsub
  obtain ⟨x, hx⟩ := hnew.1.1
  exact disjoint_left.mp hnew.2 hx (hsub hx)

end GraphMinor.GM07

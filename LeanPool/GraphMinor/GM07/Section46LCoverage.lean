/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM07.Section46OldVertexCoverage
import LeanPool.GraphMinor.GM07.Section46RetainedLinking
import LeanPool.GraphMinor.GM07.Section46EdgeSegments

/-!
# Every vertex of `L` is on a retained edge

Each old seam vertex is incident with a pasted seam edge, and retains
an incident short or linking edge. Each new vertex `W(e)` is an end
of a linking edge. Hence `L` has no isolated vertices, the coverage
needed for the contact count and cutting construction on page 226
of VII (4.6).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The graph `L` of VII (4.6), page 226, has no isolated vertices. -/
theorem hasNoIsolatedVertices_L {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J J' L : Drawing S}
    (hJ : N.IsSeamGraphFor J) {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hsmall : (G.V ∩ bd S).ncard < 2 * μ + w + 2)
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hLV : L.V = J'.V) (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t)) :
    HasNoIsolatedVertices L := by
  have : T2Space S := hS.2.1
  intro v hvL
  have hv : v ∈ J.V ∪ ⋃ e, W e := by rw [← hV, ← hLV]; exact hvL
  have hex : ∃ f ∈ forestSeamEdges J' (centralEdges G J μ w γ s t), v ∈ closure f := by
    rcases hv with hvold | hvnew
    · have hvseam : v ∈ N.seamV := by rw [← hJ.2.2]; exact hvold
      obtain ⟨i, hi⟩ := hvseam
      have he := N.e_int_mem_E hJ i
      have hcap := (N.e_int_isLink hJ i).2.2.2
      have hvpair : v ∈ ({N.φ (N.f i 0), N.φ (N.f i 1)} : Set S) := by
        rcases hi with h | h
        · exact .inl h.symm
        · exact .inr h.symm
      have hvcl : v ∈ closure (N.interiorSeamEdge i) := (hcap ▸ hvpair : v ∈ closure
        (N.interiorSeamEdge i) ∩ J.V).1
      exact exists_retained_edge_at_old_vertex hS N hJ hγ s t W hcuts hsmall hU hV
        hvold he (N.disjoint_e_int_bd hS i) hvcl
    · obtain ⟨e, hve⟩ := mem_iUnion.mp hvnew
      have hc := hcuts e
      rw [hc.2.2.2] at hve
      rcases hve with rfl | rfl
      · refine ⟨γ e.1 '' Ioo 0 (s e),
          linking_edge_mem_forestSeamEdges hS N hJ hγ s t W hcuts hsmall hU hV (.inl ⟨e, rfl⟩), ?_⟩
        rw [closure_image_Ioo_eq_Icc hγ e.2.1 hc.1.1 (.inr hc.1.2)]
        exact ⟨s e, ⟨hc.1.1.le, le_rfl⟩, rfl⟩
      · refine ⟨γ e.1 '' Ioo (t e) 1,
          linking_edge_mem_forestSeamEdges hS N hJ hγ s t W hcuts hsmall hU hV (.inr ⟨e, rfl⟩), ?_⟩
        rw [closure_image_Ioo_eq_Icc hγ e.2.1 hc.2.1.2 (.inl hc.2.1.1)]
        exact ⟨t e, ⟨le_rfl, hc.2.1.2.le⟩, rfl⟩
  obtain ⟨f, hf, hvcl⟩ := hex
  have hfL : f ∈ L.E := by rw [hLE]; exact hf
  exact ⟨f, hfL, hvL, .inl hfL, hvcl⟩

end GraphMinor.GM07

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46SplitEdges
import LeanPool.GraphMinor.GM07.Section46EdgeSegments

/-!
# Vertex contacts on the retained edges

For VII (4.6), page 226, an edge of `L` is short or linking.
A short edge has at most `w + 2μ + 1` contacts. A linking edge has
exactly `μ + 1` contacts on its closure. Central edges are excluded
by the definition of `L`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The contact bound for every edge of `L`, in VII (4.6), page 226. -/
theorem L_edge_contact_bound {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J J' L : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hleft : ∀ e, (γ e.1 '' Iic (s e) ∩ G.V).ncard = μ + 1)
    (hright : ∀ e, (γ e.1 '' Ici (t e) ∩ G.V).ncard = μ + 1)
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t)) :
    ∀ f ∈ L.E, (closure f ∩ G.V).ncard ≤ w + 2 * μ + 1 := by
  have hE := J_plus_edges hγ s t W hcuts hU hV
  intro f hf
  rw [hLE] at hf
  have hfNew := hf.1
  rw [hE] at hfNew
  rcases hfNew with hshort | hpieces
  · exact shortSeamEdge_ncard_le hshort
  · obtain ⟨e, he⟩ := mem_iUnion.mp hpieces
    have hc := hcuts e
    rcases he with rfl | rfl | rfl
    · have hIcc : Icc (0 : unitInterval) (s e) = Iic (s e) := by ext x; simp
      rw [closure_image_Ioo_eq_Icc hγ e.2.1 hc.1.1 (.inr hc.1.2), hIcc, hleft e]
      omega
    · exact (hf.2.1 ⟨e, rfl⟩).elim
    · have hIcc : Icc (t e) (1 : unitInterval) = Ici (t e) := by
        ext x
        exact ⟨fun h => h.1, fun h => ⟨h, le_top⟩⟩
      rw [closure_image_Ioo_eq_Icc hγ e.2.1 hc.2.1.2 (.inl hc.2.1.1), hIcc, hright e]
      omega

end GraphMinor.GM07

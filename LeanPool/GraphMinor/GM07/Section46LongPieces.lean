/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeSegments
import LeanPool.GraphMinor.GM07.Section46ThreePieces
import LeanPool.GraphMinor.GM07.Section46RefinedEdges
import LeanPool.GraphMinor.GM07.Section46WIntersections

/-!
# Linking and central edges belong to `J⁺`

The three-piece drawing on a closed long edge has the same marked vertices
there as the global drawing `J⁺`. Its three edges are therefore actual
edges of `J⁺`. This proves the division into two linking edges and one
central edge on page 225 of VII (4.6).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The local three-edge drawing has exactly the new vertices on the
closed old edge, in VII (4.6), page 225. -/
theorem exists_marked_long_edge_drawing {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (W : longSeamEdges G J μ w → Set S) (hW : ∀ f, W f ⊆ f.1)
    (e : longSeamEdges G J μ w) {s t : unitInterval}
    (hs : s ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) (hst : s < t)
    (hWe : W e = {γ e.1 s, γ e.1 t}) :
    ∃ P : Drawing S, P.U = closure e.1 ∧
      P.V = (J.V ∪ ⋃ f, W f) ∩ closure e.1 ∧
      P.E = {γ e.1 '' Ioo 0 s, γ e.1 '' Ioo s t, γ e.1 '' Ioo t 1} := by
  obtain ⟨P, hPU, hPV, hPE⟩ := exists_three_piece_drawing hγ e.2.1 hs ht hst
  have hmarked := marked_vertices_closed_long_edge W hW e
  rw [edge_parameter_old_vertices hγ e.2.1, hWe] at hmarked
  have hPV' : P.V = (J.V ∪ ⋃ f, W f) ∩ closure e.1 := by
    rw [hPV, hmarked]
    ext x
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (((h | h) | (h | h)) | (h | h))
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inr (.inr h)
      · exact .inl (.inr h)
    · rintro ((h | h) | (h | h))
      · exact .inl (.inl (.inl h))
      · exact .inr (.inr h)
      · exact .inl (.inl (.inr h))
      · exact .inr (.inl h)
  exact ⟨P, hPU, hPV', hPE⟩

/-- The two linking edges and central edge of a long seam edge are edges
of `J⁺`, in VII (4.6), page 225. -/
theorem long_edge_pieces_mem_J_plus {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J J' : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (W : longSeamEdges G J μ w → Set S) (hW : ∀ f, W f ⊆ f.1)
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ f, W f)
    (e : longSeamEdges G J μ w) {s t : unitInterval}
    (hs : s ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) (hst : s < t)
    (hWe : W e = {γ e.1 s, γ e.1 t}) :
    γ e.1 '' Ioo 0 s ∈ J'.E ∧ γ e.1 '' Ioo s t ∈ J'.E ∧ γ e.1 '' Ioo t 1 ∈ J'.E := by
  obtain ⟨P, hPU, hPV', hPE⟩ := exists_marked_long_edge_drawing hγ W hW e hs ht hst hWe
  have hm : ∀ f ∈ P.E, f ∈ J'.E :=
    fun f hf => local_marked_edge_mem_refinement hU hV e.2.1 hPU hPV' hf
  rw [hPE] at hm
  exact ⟨hm _ (.inl rfl), hm _ (.inr (.inl rfl)), hm _ (.inr (.inr rfl))⟩

end GraphMinor.GM07

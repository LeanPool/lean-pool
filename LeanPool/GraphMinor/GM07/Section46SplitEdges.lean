/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46ShortEdges
import LeanPool.GraphMinor.GM07.Section46LongPieces
import LeanPool.GraphMinor.GM07.Section46RefinedEdges
import LeanPool.GraphMinor.GM07.PullForest

/-!
# All edges of the refined seam graph

In VII (4.6), page 225, the edges of `J⁺` are the unchanged short edges
and the three pieces of each long edge. Every refined edge lies in one
old edge. On a long edge the local three-piece drawing has the same
marked vertices, so it accounts for every refined edge there.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The complete edge set of `J⁺` in VII (4.6), page 225. -/
theorem J_plus_edges {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J J' : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e) :
    J'.E = shortSeamEdges G J μ w ∪ ⋃ e : longSeamEdges G J μ w,
      {γ e.1 '' Ioo 0 (s e), γ e.1 '' Ioo (s e) (t e), γ e.1 '' Ioo (t e) 1} := by
  have hW : ∀ e : longSeamEdges G J μ w, W e ⊆ e.1 := by
    intro e x hx
    rw [(hcuts e).2.2.2] at hx
    rcases hx with rfl | rfl
    · exact (congrArg (fun A => γ e.1 (s e) ∈ A) (hγ.image e.1 e.2.1)).mp
        ⟨s e, (hcuts e).1, rfl⟩
    · exact (congrArg (fun A => γ e.1 (t e) ∈ A) (hγ.image e.1 e.2.1)).mp
        ⟨t e, (hcuts e).2.1, rfl⟩
  apply Subset.antisymm
  · intro f hf
    obtain ⟨e, he, hfe⟩ := refined_edge_subset_old_edge hU hV hf
    obtain ⟨x, hxf⟩ := hf.1
    by_cases helong : e ∈ longSeamEdges G J μ w
    · let e' : longSeamEdges G J μ w := ⟨e, helong⟩
      have hc := hcuts e'
      obtain ⟨P, hPU, hPV, hPE⟩ := exists_marked_long_edge_drawing hγ W hW e'
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      have hxcl : x ∈ closure e'.1 := subset_closure (hfe hxf)
      have hxP : x ∈ P.U := by rw [hPU]; exact hxcl
      have hxPV : x ∉ P.V := by
        intro hxV
        rw [hPV] at hxV
        have hxNew := (hf.2.1 hxf).2
        rw [hV] at hxNew
        exact hxNew hxV.1
      obtain ⟨g, hg, hxg⟩ := exists_edge_of_mem hxP hxPV
      have hgNew := local_marked_edge_mem_refinement hU hV he hPU hPV hg
      have hfg := J'.edge_eq_of_mem hf hgNew hxf hxg
      refine .inr (mem_iUnion.mpr ⟨e', ?_⟩)
      rw [hfg, ← hPE]
      exact hg
    · have heShort : e ∈ shortSeamEdges G J μ w := ⟨he, helong⟩
      have heNew := short_edge_mem_J_plus W hW hU hV heShort
      have hfeq := J'.edge_eq_of_mem hf heNew hxf (hfe hxf)
      exact .inl (hfeq.symm ▸ heShort)
  · intro f hf
    rcases hf with hshort | hlong
    · exact short_edge_mem_J_plus W hW hU hV hshort
    · obtain ⟨e, he⟩ := mem_iUnion.mp hlong
      have hc := hcuts e
      have hm := long_edge_pieces_mem_J_plus hγ W hW hU hV e
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      rcases he with rfl | rfl | rfl
      · exact hm.1
      · exact hm.2.1
      · exact hm.2.2

end GraphMinor.GM07

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
import LeanPool.GraphMinor.GM07.Section46CentralEnds
import LeanPool.GraphMinor.GM11.Defs

/-!
# Constructing `K` and `L`

In VII (4.6), page 226, `K` has the central edges and vertices `W`.
The graph `L` keeps all vertices of `J⁺` and deletes the central edges
and the edges on cuffs. The central-end calculation ensures that these
specified vertices and edges give actual subdrawings of `J⁺`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

private theorem exists_subdrawing_with_sets {S : Type*} [TopologicalSpace S] [T1Space S]
    {D : Drawing S} {V : Set S} {E : Set (Set S)} (hV : V ⊆ D.V) (hE : E ⊆ D.E)
    (hc : ∀ e ∈ E, closure e ∩ D.V ⊆ V) :
    ∃ D' : Drawing S, D'.IsSubdrawing D ∧ D'.V = V ∧ D'.E = E := by
  refine ⟨D.span V E, D.span_isSubdrawing V E, ?_, ?_⟩
  · rw [D.span_V]
    unfold Drawing.spanV
    refine Subset.antisymm
      (union_subset inter_subset_left (iUnion₂_subset fun e he => hc e he.1))
      (fun x hx => .inl ⟨hx, hV hx⟩)
  · rw [D.span_E, inter_eq_left.mpr hE]

/-- The two subgraphs `K` and `L` defined in VII (4.6), page 226. -/
theorem exists_K_and_L {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J J' : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e) :
    ∃ K L : Drawing S,
      K.IsSubdrawing J' ∧ K.V = ⋃ e, W e ∧ K.E = centralEdges G J μ w γ s t ∧
      L.IsSubdrawing J' ∧ L.V = J'.V ∧ L.E = forestSeamEdges J' (centralEdges G J μ w γ s t) := by
  have hW : ∀ e : longSeamEdges G J μ w, W e ⊆ e.1 := by
    intro e x hx
    rw [(hcuts e).2.2.2] at hx
    rcases hx with rfl | rfl
    · exact (congrArg (fun A => γ e.1 (s e) ∈ A) (hγ.image e.1 e.2.1)).mp
        ⟨s e, (hcuts e).1, rfl⟩
    · exact (congrArg (fun A => γ e.1 (t e) ∈ A) (hγ.image e.1 e.2.1)).mp
        ⟨t e, (hcuts e).2.1, rfl⟩
  have hWE : (⋃ e, W e) ⊆ J'.V := by rw [hV]; exact subset_union_right
  have hCE : centralEdges G J μ w γ s t ⊆ J'.E := by
    rintro f ⟨e, rfl⟩
    have hc := hcuts e
    exact (long_edge_pieces_mem_J_plus hγ W hW hU hV e
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).2.1
  have hends : ∀ f ∈ centralEdges G J μ w γ s t, closure f ∩ J'.V ⊆ ⋃ e, W e := by
    rintro f ⟨e, rfl⟩
    have hc := hcuts e
    rw [central_edge_ends hγ W hW hV e hc.1 hc.2.1 hc.2.2.1 hc.2.2.2]
    exact subset_iUnion W e
  obtain ⟨K, hK, hKV, hKE⟩ := exists_subdrawing_with_sets (D := J') (V := ⋃ e, W e)
    (E := centralEdges G J μ w γ s t) hWE hCE hends
  have hLE : forestSeamEdges J' (centralEdges G J μ w γ s t) ⊆ J'.E := fun e he => he.1
  obtain ⟨L, hL, hLV, hLE'⟩ := exists_subdrawing_with_sets (D := J') (V := J'.V)
    subset_rfl hLE (fun _ _ => inter_subset_right)
  exact ⟨K, L, hK, hKV, hKE, hL, hLV, hLE'⟩

end GraphMinor.GM07

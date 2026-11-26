/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46RetainedLinking
import LeanPool.GraphMinor.GM07.Section46ShortEdges
import LeanPool.GraphMinor.GM07.Section46OldVertices
import LeanPool.GraphMinor.GM07.Section46EdgeSegments

/-!
# Old seam vertices remain incident with `L`

An old seam vertex at an edge off the cuffs remains on an edge of `L`:
a short edge is retained, and a long edge contributes the linking edge
at that end. This is the old-vertex part of the coverage count used on
page 226 of VII (4.6).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- An old vertex incident with an old edge off the cuffs is incident
with a retained edge, in VII (4.6), page 226. -/
theorem exists_retained_edge_at_old_vertex {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J J' : Drawing S}
    (hJ : N.IsSeamGraphFor J) {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hsmall : (G.V ∩ bd S).ncard < 2 * μ + w + 2)
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    {v : S} (hvV : v ∈ J.V) {e : Set S} (he : e ∈ J.E)
    (hoff : Disjoint e (bd S)) (hvcl : v ∈ closure e) :
    ∃ f ∈ forestSeamEdges J' (centralEdges G J μ w γ s t), v ∈ closure f := by
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
  by_cases hlong : e ∈ longSeamEdges G J μ w
  · let e' : longSeamEdges G J μ w := ⟨e, hlong⟩
    have hc := hcuts e'
    have hp : v ∈ ({γ e'.1 0, γ e'.1 1} : Set S) := by
      rw [← edge_parameter_old_vertices hγ he]
      exact ⟨hvcl, hvV⟩
    rcases hp with rfl | rfl
    · refine ⟨γ e'.1 '' Ioo 0 (s e'),
        linking_edge_mem_forestSeamEdges hS N hJ hγ s t W hcuts hsmall hU hV (.inl ⟨e', rfl⟩), ?_⟩
      rw [closure_image_Ioo_eq_Icc hγ he hc.1.1 (.inr hc.1.2)]
      exact ⟨0, ⟨le_rfl, hc.1.1.le⟩, rfl⟩
    · refine ⟨γ e'.1 '' Ioo (t e') 1,
        linking_edge_mem_forestSeamEdges hS N hJ hγ s t W hcuts hsmall hU hV (.inr ⟨e', rfl⟩), ?_⟩
      rw [closure_image_Ioo_eq_Icc hγ he hc.2.1.2 (.inl hc.2.1.1)]
      exact ⟨1, ⟨hc.2.1.2.le, le_rfl⟩, rfl⟩
  · have heShort : e ∈ shortSeamEdges G J μ w := ⟨he, hlong⟩
    have heNew := short_edge_mem_J_plus W hW hU hV heShort
    have hnotcentral : e ∉ centralEdges G J μ w γ s t := fun hc =>
      disjoint_left.mp (central_closure_disjoint_old_vertices hγ s t hcpos hc) hvcl hvV
    have hnotbd : ¬e ⊆ bd S := by
      intro hsub
      obtain ⟨x, hx⟩ := he.1
      exact disjoint_left.mp hoff hx (hsub hx)
    exact ⟨e, ⟨heNew, hnotcentral, hnotbd⟩, hvcl⟩

end GraphMinor.GM07

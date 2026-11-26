/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM11.GlueDiscs
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Enclosing a circle across a leaf neighbourhood

For the final gluing at the leaf in XII (7.4), pages 262--263,
let `A` be the old open-disc region and `N` a closed disc around
the removed end of the edge. The part of a circle outside the
interior of `N` is compact in `A`. XI's disc gluing lemma puts
that compact set in a closed disc of `A` meeting `N` in one
boundary line. Their union is a closed disc. The circle bounds
a smaller disc within this union.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- A circle whose part outside a suitable leaf disc lies in an
old disc region bounds a disc in the union of those two sets.
The geometric boundary and connectivity conditions describe the
local disc at the leaf, before applying the gluing construction. -/
theorem exists_disc_bounding_circle_by_leaf_gluing
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {A N F : Set S}
    (hA : IsOpenDisc A) (hN : IsClosedDisc N) (hF : IsOArc F)
    {ℓ : I → S} (hℓ : Continuous ℓ) (h0 : ℓ 0 ∉ A) (h1 : ℓ 1 ∉ A)
    (hinj : InjOn ℓ (Ioo 0 1)) (hbd : discBd N ∩ A = ℓ '' Ioo 0 1)
    (hT : IsPreconnected (discInt N ∩ A)) (hTne : (discInt N ∩ A).Nonempty)
    (hFA : F \ discInt N ⊆ A) :
    ∃ D : Set S, D ⊆ A ∪ N ∧ IsClosedDisc D ∧ discBd D = F := by
  have hbound : ∀ (E : Set S), IsClosedDisc E → E ⊆ A ∪ N → F ⊆ E →
      ∃ D : Set S, D ⊆ A ∪ N ∧ IsClosedDisc D ∧ discBd D = F := by
    intro E hE hEsub hFE
    obtain ⟨D, hD, _⟩ := disc_oArc E F hE hFE hF
    exact ⟨D, hD.1.trans hEsub, hD.2.1, hD.2.2.1⟩
  by_cases hFN : F ⊆ N
  · exact hbound N hN subset_union_right hFN
  let C := F \ discInt N
  have hCc : IsCompact C := (isCompact_of_isOArc hF).inter_right
    (hN.isOpen_discInt (fun x => (hS.2.2 x).isManifoldPoint)).isClosed_compl
  have hCne : C.Nonempty := by
    obtain ⟨x, hxF, hxN⟩ := not_subset.mp hFN
    exact ⟨x, hxF, fun hx => hxN (discInt_subset N hx)⟩
  have hCdis : Disjoint C (discInt N) := disjoint_sdiff_left
  obtain ⟨ρ, L, s, t, hρ, hρA, hCρ, hmeet, hL, hLρ, hLN⟩ :=
    exists_disc_off hS hA hN hℓ h0 h1 hinj hbd hT hTne hCc hFA hCdis hCne
  have hUnion : IsClosedDisc (ρ ∪ N) := (disc_union ρ N L s t hρ hN hL hmeet hLρ hLN).1
  apply hbound (ρ ∪ N) hUnion (union_subset_union_left N hρA)
  intro x hxF
  by_cases hxN : x ∈ discInt N
  · exact Or.inr (discInt_subset N hxN)
  · exact Or.inl (hCρ ⟨hxF, hxN⟩)

end GraphMinor.GM12

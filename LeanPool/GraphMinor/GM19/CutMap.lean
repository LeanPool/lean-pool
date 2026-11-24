/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TopologyStatements

/-!
# The map of a cutting

Sections 5, 10, 11 and 14 of Graph Minors XIX cut a surface along an arc `F` and pull a painting
back
along the associated surjection `ψ`. This file has the facts about `ψ` that do not depend on the
painting. On compact Hausdorff spaces `ψ` is a closed map. It is a homeomorphism off `F`
(`isOpen_image_of_isCutMap`, `isPreconnected_preimage_of_isCutMap`). A set `A` off `F` that is
connected near a point `v` of
`F` comes to `v` from one side only, so the closure of its lift has one point over `v`
(`eq_of_mem_closure_preimage_of_isCutMap`). This last fact is why an edge of a painting lifts to an
edge.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

universe u

variable {S' S : Type u} [TopologicalSpace S'] [TopologicalSpace S] [CompactSpace S'] [T2Space S]
  {ψ : S' → S} {F : Set S}

/-- A map that undoes a cut along `F`. It is one to one off `F`, and over `F` it has finite fibres,
and the
lift of `F` lies in the boundary. Unlike `IsCutting`, it allows more than two points over a point of
`F`, which
happens at a vertex of `F` of degree three, or where `F` touches the boundary. -/
def IsCutMap {S' S : Type u} [TopologicalSpace S'] [TopologicalSpace S] (ψ : S' → S)
  (F : Set S) : Prop :=
  Continuous ψ ∧ Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' Fᶜ) ∧ (∀ x, (ψ ⁻¹' {x}).Finite)
    ∧ ψ ⁻¹' F ⊆ bd S'

omit [CompactSpace S'] [T2Space S] in
theorem IsCutting.isCutMap (h : IsCutting ψ F) : IsCutMap ψ F := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x ↦ ?_, h.2.2.2.2⟩
  by_cases hx : x ∈ F
  · exact finite_of_ncard_ne_zero (by rw [h.2.2.2.1 x hx]; norm_num)
  · refine Set.Subsingleton.finite fun a ha b hb ↦ ?_
    exact h.2.2.1 (show ψ a ∈ Fᶜ by rw [ha]; exact hx) (show ψ b ∈ Fᶜ by rw [hb]; exact hx)
      (ha.trans hb.symm)

/-- A cutting map is a closed map, since `S'` is compact and `S` is Hausdorff. -/
theorem isClosedMap_of_isCutMap (h : IsCutMap ψ F) : IsClosedMap ψ :=
  h.1.isClosedMap

omit [CompactSpace S'] [T2Space S] in
/-- Over a set off `F`, the preimage and the image of a part of it determine each other. -/
theorem image_compl_of_isCutMap (h : IsCutMap ψ F) {W : Set S'} (hW : W ⊆ ψ ⁻¹' Fᶜ) :
    ψ '' Wᶜ = (ψ '' W)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨u, hu, hxu⟩
    have hyF : ψ x ∉ F := hxu ▸ hW hu
    exact hx (h.2.2.1 hyF (hW hu) hxu.symm ▸ hu)
  · intro hy
    obtain ⟨x, rfl⟩ := h.2.1 y
    exact ⟨x, fun hx ↦ hy (mem_image_of_mem ψ hx), rfl⟩

/-- `ψ` maps open sets off `F` to open sets. -/
theorem isOpen_image_of_isCutMap (h : IsCutMap ψ F) {W : Set S'} (hW : W ⊆ ψ ⁻¹' Fᶜ)
    (hWo : IsOpen W) : IsOpen (ψ '' W) := by
  rw [← isClosed_compl_iff, ← image_compl_of_isCutMap h hW]
  exact isClosedMap_of_isCutMap h _ hWo.isClosed_compl

/-- The lift of a preconnected set off the closed set `F` is preconnected, since `ψ` is a
homeomorphism
off `F`. -/
theorem isPreconnected_preimage_of_isCutMap (h : IsCutMap ψ F) (hF : IsClosed F) {A : Set S}
    (hA : A ⊆ Fᶜ) (hAc : IsPreconnected A) : IsPreconnected (ψ ⁻¹' A) := by
  have hoffo : IsOpen (ψ ⁻¹' Fᶜ) := hF.isOpen_compl.preimage h.1
  intro U V hU hV hcov hUn hVn
  have hU' := isOpen_image_of_isCutMap h (W := U ∩ ψ ⁻¹' Fᶜ) inter_subset_right (hU.inter hoffo)
  have hV' := isOpen_image_of_isCutMap h (W := V ∩ ψ ⁻¹' Fᶜ) inter_subset_right (hV.inter hoffo)
  have hcov' : A ⊆ ψ '' (U ∩ ψ ⁻¹' Fᶜ) ∪ ψ '' (V ∩ ψ ⁻¹' Fᶜ) := by
    intro y hy
    obtain ⟨x, rfl⟩ := h.2.1 y
    rcases hcov hy with hx | hx
    · exact Or.inl ⟨x, ⟨hx, hA hy⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, hA hy⟩, rfl⟩
  obtain ⟨u, huP, huU⟩ := hUn
  obtain ⟨v, hvP, hvV⟩ := hVn
  obtain ⟨y, hyA, ⟨a, ⟨haU, hao⟩, rfl⟩, ⟨b, ⟨hbV, hbo⟩, hba⟩⟩ := hAc _ _ hU' hV' hcov'
    ⟨ψ u, huP, u, ⟨huU, hA huP⟩, rfl⟩ ⟨ψ v, hvP, v, ⟨hvV, hA hvP⟩, rfl⟩
  have hab : b = a := h.2.2.1 hbo hao hba
  exact ⟨a, hyA, haU, hab ▸ hbV⟩

end GraphMinor.GM19

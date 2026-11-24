/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.NetSeparateAssembly
import LeanPool.GraphMinor.GM07.NetSeparateCount
import LeanPool.GraphMinor.GM07.NetSwapCut
import LeanPool.GraphMinor.GM07.NetSwapNormal
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# The separating exchange of VII (2.6)

This is the new net of VII (2.6), page 218: paste `f = g` and cut along `F`, for a pair with one
side
in each piece of the cut. The new net is normal, and `Net.exists_separating_exchange` gives its
exact
count. `Net.pair_contacts_le_of_separating` is the inequality that replaces the printed one.
-/

public section
namespace GraphMinor.GM07
open Set Topology Metric Surface
universe u

/-- See the module docstring. -/
theorem Net.exists_separating_exchange {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    (N : Net S) (i : Fin N.r) {G : Drawing S} (hN : N.IsNormalFor G)
    {F A B : Set N.D} {s t : N.D} (hF : IsLineWithEnds F s t) (hst : s ≠ t)
    (hFbd : F ∩ bd N.D = {s, t})
    (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t)
    (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F) (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (hfA : range (N.f i) ⊆ discBd A) (hgB : range (N.g i) ⊆ discBd B)
    (hNormal : G.IsNormal (N.φ '' F)) :
    ∃ M : Net S, M.IsNormalFor G ∧
      M.bdVertexPreimageCard G + 2 * (N.φ '' (N.f i '' Ioo (0 : unitInterval) 1) ∩ G.V).ncard +
          ({N.φ (N.f i 0)} ∩ G.V).ncard + ({N.φ (N.f i 1)} ∩ G.V).ncard =
        N.bdVertexPreimageCard G + 2 * (N.φ '' (F \ {s, t}) ∩ G.V).ncard +
          ({N.φ s} ∩ G.V).ncard + ({N.φ t} ∩ G.V).ncard := by
  let : T2Space S := hS.2.1
  obtain ⟨ψ₀, φ₀, hψ₀, hφ₀, hφA, hφB, hiA, hiB, hcross, hαbd, hβbd⟩ :=
    N.exists_separating_pair_disc i hA hB hAB hfA hgB
  obtain ⟨e₀⟩ := isClosedDisc_closedBall.1
  obtain ⟨eN⟩ := N.isClosedDisc_D
  let e : closedBall (0 : ℂ) 1 ≃ₜ N.D :=
    e₀.symm.trans (eN.trans (Homeomorph.Set.univ N.D))
  let α : A → N.D := e ∘ ψ₀ ∘ Sum.inl
  let β : B → N.D := e ∘ ψ₀ ∘ Sum.inr
  let φ : N.D → S := φ₀ ∘ e.symm
  have hcα : Continuous α := e.continuous.comp (hψ₀.continuous.comp continuous_inl)
  have hcβ : Continuous β := e.continuous.comp (hψ₀.continuous.comp continuous_inr)
  have heBd : ∀ z, e z ∈ bd N.D ↔ z ∈ bd (closedBall (0 : ℂ) 1) := by
    intro z
    have he := image_bd_homeomorph e
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := he.symm ▸ hz
      exact e.injective hwz ▸ hw
    · intro hz
      exact he ▸ mem_image_of_mem e hz
  have hT : range α ∪ range β = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨w, hw⟩ := hψ₀.surjective (e.symm z)
    cases w with
    | inl x => exact Or.inl ⟨x, (congrArg e hw).trans (e.apply_symm_apply z)⟩
    | inr y => exact Or.inr ⟨y, (congrArg e hw).trans (e.apply_symm_apply z)⟩
  have hcross' : ∀ (x : A) (y : B), α x = β y ↔ ∃ r, x.val = N.f i r ∧ y.val = N.g i r :=
    fun x y => e.injective.eq_iff.trans (hcross x y)
  have hαbd' : ∀ x : A, α x ∈ bd N.D ↔ x.val ∈ discBd A ∧
      x.val ∉ N.f i '' Ioo (0 : unitInterval) 1 := fun x => (heBd _).trans (hαbd x)
  have hβbd' : ∀ y : B, β y ∈ bd N.D ↔ y.val ∈ discBd B ∧
      y.val ∉ N.g i '' Ioo (0 : unitInterval) 1 := fun y => (heBd _).trans (hβbd y)
  have hφA' : ∀ x : A, φ (α x) = N.φ x.val := by
    intro x
    change φ₀ (e.symm (e (ψ₀ (Sum.inl x)))) = _
    rw [e.symm_apply_apply]
    exact hφA x
  have hφB' : ∀ y : B, φ (β y) = N.φ y.val := by
    intro y
    change φ₀ (e.symm (e (ψ₀ (Sum.inr y)))) = _
    rw [e.symm_apply_apply]
    exact hφB y
  obtain ⟨M, eM, hr, hMap, hU⟩ := N.exists_separating_net_of_maps N.isSurface_D N.isClosedDisc_D
    i hF hFbd hs ht hA hB hAB hI hAd hBd hfA hgB α β hcα hcβ
    (e.injective.comp hiA) (e.injective.comp hiB) hT hcross' hαbd' hβbd'
    φ (hφ₀.comp e.symm.isQuotientMap) hφA' hφB'
  have hEBd : ∀ z, eM z ∈ bd M.D ↔ z ∈ bd N.D := by
    intro z
    have he := image_bd_homeomorph eM
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := he.symm ▸ hz
      exact eM.injective hwz ▸ hw
    · intro hz
      exact he ▸ mem_image_of_mem eM hz
  have hmap : ∀ z, M.φ (eM z) = φ z := fun z => congrFun hMap z
  have hT' : range (eM ∘ α) ∪ range (eM ∘ β) = univ := by
    apply eq_univ_of_forall
    intro z
    rcases hT.symm ▸ mem_univ (eM.symm z) with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, (congrArg eM hx).trans (eM.apply_symm_apply z)⟩
    · exact Or.inr ⟨y, (congrArg eM hy).trans (eM.apply_symm_apply z)⟩
  have hCount := N.separating_contact_balance M i hst hFbd hs ht hAB hI hAd hBd hfA hgB
    (eM ∘ α) (eM ∘ β) (eM.injective.comp (e.injective.comp hiA))
    (eM.injective.comp (e.injective.comp hiB)) hT'
    (fun x y => eM.injective.eq_iff.trans (hcross' x y))
    (fun x => (hEBd _).trans (hαbd' x)) (fun y => (hEBd _).trans (hβbd' y))
    (fun x => (hmap _).trans (hφA' x)) (fun y => (hmap _).trans (hφB' y)) G.V G.finite_V
  refine ⟨M, N.isNormalFor_of_swap_seam_subset hS M hN hr hU hNormal, ?_⟩
  change (M.φ ⁻¹' G.V ∩ bd M.D).ncard + _ + _ + _ = (N.φ ⁻¹' G.V ∩ bd N.D).ncard + _ + _ + _
  rw [inter_comm (M.φ ⁻¹' G.V) (bd M.D), inter_comm (N.φ ⁻¹' G.V) (bd N.D)]
  exact hCount

/-- The inequality from the exact count. It replaces the inequality printed in the proof of VII
(2.6),
page 218 (see the correction to the proof of (2.6) in `corrections/GM07.md`). The hypothesis `hmin`
is condition (ii) of a minimal net. -/
theorem Net.pair_contacts_le_of_separating {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    (N : Net S) (i : Fin N.r) {G : Drawing S} (hN : N.IsNormalFor G)
    (hmin : ∀ M : Net S, M.IsNormalFor G → N.bdVertexPreimageCard G ≤ M.bdVertexPreimageCard G)
    {F A B : Set N.D} {s t : N.D} (hF : IsLineWithEnds F s t) (hst : s ≠ t)
    (hFbd : F ∩ bd N.D = {s, t})
    (hs : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ s ∧ N.g j r ≠ s)
    (ht : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ t ∧ N.g j r ≠ t)
    (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F) (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (hfA : range (N.f i) ⊆ discBd A) (hgB : range (N.g i) ⊆ discBd B)
    (hNormal : G.IsNormal (N.φ '' F)) :
    2 * (N.φ '' (N.f i '' Ioo (0 : unitInterval) 1) ∩ G.V).ncard +
        ({N.φ (N.f i 0)} ∩ G.V).ncard + ({N.φ (N.f i 1)} ∩ G.V).ncard ≤
      2 * (N.φ '' (F \ {s, t}) ∩ G.V).ncard + ({N.φ s} ∩ G.V).ncard + ({N.φ t} ∩ G.V).ncard := by
  obtain ⟨M, hM, hCount⟩ := N.exists_separating_exchange hS i hN hF hst hFbd hs ht hA hB hAB hI
    hAd hBd hfA hgB hNormal
  have := hmin M hM
  omega

end GraphMinor.GM07

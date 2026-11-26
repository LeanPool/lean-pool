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
  obtain ⟨e, hcα, hcβ, hiα, hiβ, hT, hcross', hαbd', hβbd', hφ, hφA', hφB'⟩ :=
    N.exists_transported_cut_maps hψ₀ hφ₀ hφA hφB hiA hiB hcross hαbd hβbd
  let α : A → N.D := e ∘ ψ₀ ∘ Sum.inl
  let β : B → N.D := e ∘ ψ₀ ∘ Sum.inr
  let φ : N.D → S := φ₀ ∘ e.symm
  obtain ⟨M, eM, hr, hMap, hU⟩ := N.exists_separating_net_of_maps N.isSurface_D N.isClosedDisc_D
    i hF hFbd hs ht hA hB hAB hI hAd hBd hfA hgB α β hcα hcβ
    hiα hiβ hT hcross' hαbd' hβbd'
    φ hφ hφA' hφB'
  have hmap : ∀ z, M.φ (eM z) = φ z := fun z => congrFun hMap z
  have hT' : range (eM ∘ α) ∪ range (eM ∘ β) = univ := by
    apply eq_univ_of_forall
    intro z
    rcases hT.symm ▸ mem_univ (eM.symm z) with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, (congrArg eM hx).trans (eM.apply_symm_apply z)⟩
    · exact Or.inr ⟨y, (congrArg eM hy).trans (eM.apply_symm_apply z)⟩
  have hCount := N.separating_contact_balance M i hst hFbd hs ht hAB hI hAd hBd hfA hgB
    (eM ∘ α) (eM ∘ β) (eM.injective.comp hiα)
    (eM.injective.comp hiβ) hT'
    (fun x y => eM.injective.eq_iff.trans (hcross' x y))
    (fun x => (mem_bd_homeomorph_iff eM _).trans (hαbd' x))
    (fun y => (mem_bd_homeomorph_iff eM _).trans (hβbd' y))
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

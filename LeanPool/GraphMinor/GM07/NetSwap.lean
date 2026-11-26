/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.NetSwapBasic
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapCut
import LeanPool.GraphMinor.GM07.NetSwapAssembly
import LeanPool.GraphMinor.GM07.NetSwapNormal
import LeanPool.GraphMinor.GM07.NetSwapContactBalance
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Exchanging a paired boundary subarc of a net

The exchange used in VII (2.6), page 218, pastes a subarc
of one paired side to its mate and cuts along a proper line.
Construct the cut pieces, their pasted disc, and all new paired
sides. Relabel the pasted disc by the original disc to keep its
universe, then package the result as a net for the same surface.
-/

public section
namespace GraphMinor.GM07
open Set Topology Metric Surface

/-- The actual net obtained by cutting along a proper line and
pasting the subarc between its endpoints to its mate. The number
of pairs and the seam vertices are unchanged. The returned maps
record every fiber and boundary identification, including the
cutting endpoints, for the count in VII (2.6), page 218. -/
theorem Net.exists_swap_subarc_model
    {S : Type*} [TopologicalSpace S] [T2Space S] (N : Net S) (i : Fin N.r)
    (u v : unitInterval) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v}) :
    ∃ (M : Net S) (C A B : Set N.D) (ψ : A ⊕ B → M.D),
      M.r = N.r ∧ M.seamV = N.seamV ∧
      IsClosedDisc A ∧ IsClosedDisc B ∧ A ∪ B = univ ∧ A ∩ B = F ∧
      discBd A = range (pieceA (N.f i) u.val v.val) ∪ F ∧
      discBd B = C ∪ F ∧ range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D ∧
      IsQuotientMap ψ ∧
      (∀ x : A, M.φ (ψ (Sum.inl x)) = N.φ x.val) ∧
      (∀ y : B, M.φ (ψ (Sum.inr y)) = N.φ y.val) ∧
      Function.Injective (ψ ∘ Sum.inl) ∧ Function.Injective (ψ ∘ Sum.inr) ∧
      (∀ (x : A) (y : B), ψ (Sum.inl x) = ψ (Sum.inr y) ↔
        ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
          y.val = pieceA (N.g i) u.val v.val t) ∧
      (∀ x : A, ψ (Sum.inl x) ∈ bd M.D ↔
        x.val ∈ discBd A ∧ x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1) ∧
      (∀ y : B, ψ (Sum.inr y) ∈ bd M.D ↔
        y.val ∈ discBd B ∧ y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1) := by
  obtain ⟨C, A, B, ψ₀, φ₀, hA, hB, hAB, hI, hAd, hBd, hcover,
    hψ₀, hφ₀, hφA, hφB, hiA, hiB, hcross, hαbd, hβbd⟩ :=
    N.exists_swap_disc i u v hu huv hv hF hFbd
  obtain ⟨e, hcα, hcβ, hiα, hiβ, hT, hcross', hαbd', hβbd', hφ, hφA', hφB'⟩ :=
    N.exists_transported_cut_maps hψ₀ hφ₀ hφA hφB hiA hiB hcross hαbd hβbd
  let α : A → N.D := e ∘ ψ₀ ∘ Sum.inl
  let β : B → N.D := e ∘ ψ₀ ∘ Sum.inr
  let φ : N.D → S := φ₀ ∘ e.symm
  obtain ⟨M, eM, hr, hMap, hV⟩ := N.exists_swap_net_of_maps N.isSurface_D N.isClosedDisc_D
    i u v hu huv hv hF hFbd hAB hI hAd hcover hBd α β hcα hcβ
    hiα hiβ hT hcross' hαbd' hβbd'
    φ hφ hφA' hφB'
  let E := e.trans eM
  let ψ := E ∘ ψ₀
  have hEMap : ∀ z, M.φ (E z) = φ₀ z := by
    intro z
    have h := congrFun hMap (e z)
    change M.φ (E z) = φ₀ (e.symm (e z)) at h
    exact h.trans (congrArg φ₀ (e.symm_apply_apply z))
  refine ⟨M, C, A, B, ψ, hr, hV, hA, hB, hAB, hI, hAd, hBd, hcover,
    E.isQuotientMap.comp hψ₀, ?_, ?_, E.injective.comp hiA, E.injective.comp hiB, ?_, ?_, ?_⟩
  · intro x
    exact (hEMap _).trans (hφA x)
  · intro y
    exact (hEMap _).trans (hφB y)
  · intro x y
    exact E.injective.eq_iff.trans (hcross x y)
  · intro x
    exact (mem_bd_homeomorph_iff E _).trans (hαbd x)
  · intro y
    exact (mem_bd_homeomorph_iff E _).trans (hβbd y)

/-- Cutting and pasting the selected subarc produces a normal net
when the original net and the proper cutting line are normal. The
number of pairs and the seam vertices stay unchanged. This proves
the normality assertion in VII (2.6), page 218. -/
theorem Net.exists_swap_subarc_normal
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S)
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {G : Drawing S} (hN : N.IsNormalFor G)
    {F : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    (hNormal : G_D.IsNormal F) :
    ∃ M : Net S, M.IsNormalFor G ∧ M.r = N.r ∧ M.seamV = N.seamV ∧
      M.seamU ⊆ N.seamU ∪ N.φ '' F := by
  let : T2Space S := hS.2.1
  obtain ⟨M, C, A, B, ψ, hr, hV, _, _, _, _, hAd, hBd, hcover,
    hψ, hφA, hφB, _, _, _, hαbd, hβbd⟩ :=
    N.exists_swap_subarc_model i u v hu huv hv hF hFbd
  have hU := N.seamU_subset_of_swap_maps M i u v huv.le hAd hBd hcover ψ hψ.surjective
    hφA hφB (fun x hx => ((hαbd x).mp hx).1) (fun y hy => ((hβbd y).mp hy).1)
  exact ⟨M, N.isNormalFor_of_swap_seam_subset hS M hN hr hU
    (N.normal_image_of_pullback hPull hNormal), hr, hV, hU⟩

/-- The new normal net from a proper line between interior points of
one paired side. Its number of pairs is unchanged. Its exact boundary
contact balance removes twice the contacts on the open pasted subarc
and adds twice the contacts on the inner cutting line, with no endpoint
term. This is the subarc form of the new-net construction in VII (2.6),
page 218, also used in VII (4.6), page 230. -/
theorem Net.exists_swap_subarc
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S)
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {G : Drawing S} (hN : N.IsNormalFor G)
    {F : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    (hNormal : G_D.IsNormal F) :
    ∃ M : Net S, M.IsNormalFor G ∧ M.r = N.r ∧ M.seamV = N.seamV ∧
      M.bdVertexPreimageCard G +
        2 * (N.φ '' ((N.f i '' Icc u v) \ {N.f i u, N.f i v}) ∩ G.V).ncard =
      N.bdVertexPreimageCard G +
        2 * (N.φ '' (F \ {N.f i u, N.f i v}) ∩ G.V).ncard := by
  let : T2Space S := hS.2.1
  obtain ⟨M, C, A, B, ψ, hr, hV, _, _, _, hI, hAd, hBd, hcover,
    hψ, hφA, hφB, hiA, hiB, hcross, hαbd, hβbd⟩ :=
    N.exists_swap_subarc_model i u v hu huv hv hF hFbd
  have hU := N.seamU_subset_of_swap_maps M i u v huv.le hAd hBd hcover ψ hψ.surjective
    hφA hφB (fun x hx => ((hαbd x).mp hx).1) (fun y hy => ((hβbd y).mp hy).1)
  have hM := N.isNormalFor_of_swap_seam_subset hS M hN hr hU
    (N.normal_image_of_pullback hPull hNormal)
  have hT : range (ψ ∘ Sum.inl) ∪ range (ψ ∘ Sum.inr) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨w, rfl⟩ := hψ.surjective z
    cases w with
    | inl x => exact Or.inl (mem_range_self x)
    | inr y => exact Or.inr (mem_range_self y)
  have hCount := N.swap_contact_balance M i u v hu huv hv hF hFbd hI hAd hBd hcover
    (ψ ∘ Sum.inl) (ψ ∘ Sum.inr) hiA hiB hT hcross hφA hφB hαbd hβbd G.V G.finite_V
  have hOpen : (N.f i '' Icc u v) \ {N.f i u, N.f i v} = N.f i '' Ioo u v := by
    rw [← image_pair, ← image_sdiff (N.injective_f i), Icc_sdiff_both]
  refine ⟨M, hM, hr, hV, ?_⟩
  rw [hOpen]
  change (M.φ ⁻¹' G.V ∩ bd M.D).ncard + _ = (N.φ ⁻¹' G.V ∩ bd N.D).ncard + _
  rw [inter_comm (M.φ ⁻¹' G.V) (bd M.D), inter_comm (N.φ ⁻¹' G.V) (bd N.D)]
  exact hCount

/-- Minimality bounds contacts on the open selected subarc by contacts
on the inner cutting line. This is the minimality comparison in the
proof of VII (2.6), page 218, in the subarc configuration also used
on page 230 in VII (4.6). -/
theorem Net.subarc_contacts_le_cutting_contacts
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S)
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {G : Drawing S} (hMin : N.IsMinimalFor G)
    {F : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    (hNormal : G_D.IsNormal F) :
    (N.φ '' ((N.f i '' Icc u v) \ {N.f i u, N.f i v}) ∩ G.V).ncard ≤
      (N.φ '' (F \ {N.f i u, N.f i v}) ∩ G.V).ncard := by
  obtain ⟨M, hM, _, _, hBalance⟩ :=
    N.exists_swap_subarc hS i u v hu huv hv hMin.1 hF hFbd hPull hNormal
  have hle := hMin.2.1 M hM
  omega

end GraphMinor.GM07

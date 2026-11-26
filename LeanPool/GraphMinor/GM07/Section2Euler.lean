/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.Surface.CapCoh
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.SideCut
import LeanPool.GraphMinor.Surface.SurfacePull

/-!
# Graph Minors VII, Section 2: Euler's Formula for Seam Graphs ((2.2))

This file proves the Euler formula for the seam graph `J` of a net `N` on a surface `S ≃ₜ Σ(a, b,
c)`
used in the proof of `(2.2)` (page 216):
`|E(J)| + 1 = |V(J)| + 2a + b + c`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Filter GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

namespace Net

/-! ## 1. Openness of seam interiors on `bd N.D` and disjointness from `bd S` -/

/-- Reversing the roles of `N.f` and `N.g` in a net `N : Net S` gives a net with the same `D`, `r`,
and `φ`. -/
def swapFG (N : Net S) : Net S where
  D := N.D
  isSurface_D := N.isSurface_D
  isClosedDisc_D := N.isClosedDisc_D
  r := N.r
  f := N.g
  g := N.f
  φ := N.φ
  injective_f := N.injective_g
  range_f_subset_bd := N.range_g_subset_bd
  injective_g := N.injective_f
  range_g_subset_bd := N.range_f_subset_bd
  internally_disjoint_ff := N.internally_disjoint_gg
  internally_disjoint_gg := N.internally_disjoint_ff
  internally_disjoint_fg := N.internally_disjoint_gf
  internally_disjoint_gf := N.internally_disjoint_fg
  quotientMap_φ := N.quotientMap_φ
  pasting_eq i x := (N.pasting_eq i x).symm
  interior_inj := N.interior_inj
  bd_eq_iff x y := by
    rw [N.bd_eq_iff x y]
    constructor <;> intro h <;> induction h with
    | rel a b hab =>
      rcases hab with ⟨i, t, rfl, rfl⟩
      exact .symm _ _ (.rel _ _ ⟨i, t, rfl, rfl⟩)
    | refl a => exact .refl a
    | symm a b _ ih => exact .symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

/-- For any net `N`, `i : Fin N.r`, and open interval `(a, b) ⊆ (0, 1)`, `N.f i '' Ioo a b` is open
in `bd N.D`: there is an open set `U ⊆ N.D` such that `U ∩ bd N.D = N.f i '' Ioo a b`. -/
theorem exists_isOpen_inter_bd_eq_image_Ioo_f (N : Net S) (i : Fin N.r)
    (a b : unitInterval) :
    ∃ U : Set N.D, IsOpen U ∧ U ∩ bd N.D = N.f i '' Ioo a b := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hOArc : IsOArc (bd N.D) := N.isOArc_bd_D
  have hf0_bd : N.f i 0 ∈ bd N.D := N.range_f_subset_bd i ⟨0, rfl⟩
  have hf1_bd : N.f i 1 ∈ bd N.D := N.range_f_subset_bd i ⟨1, rfl⟩
  have hf01_ne : N.f i 0 ≠ N.f i 1 := fun h => zero_ne_one (N.injective_f i h)
  obtain ⟨B₁, B₂, hcomp, hdisj, hunion, ⟨h₁, _, _⟩, ⟨h₂, _, _⟩⟩ :=
    oArc_components_diff_pair hOArc hf0_bd hf1_bd hf01_ne
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have hIoo_pc := Net.unitInterval_interior_isPathConnected
  have hfIoo_conn : IsPreconnected (N.f i '' Ioo (0 : unitInterval) 1) :=
    (hIoo_pc.image (N.f i).continuous).isConnected.isPreconnected
  have hf0_not : N.f i 0 ∉ N.f i '' Ioo (0 : unitInterval) 1 := by
    rintro ⟨s, hs, hs0⟩
    exact hs.1.ne (N.injective_f i hs0).symm
  have hf1_not : N.f i 1 ∉ N.f i '' Ioo (0 : unitInterval) 1 := by
    rintro ⟨s, hs, hs1⟩
    exact hs.2.ne (N.injective_f i hs1)
  have hfIoo_sub : N.f i '' Ioo (0 : unitInterval) 1 ⊆ bd N.D \ {N.f i 0, N.f i 1} := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨N.range_f_subset_bd i ⟨s, rfl⟩, ?_⟩
    rintro (h0 | h1)
    · exact hf0_not ⟨s, hs, h0⟩
    · exact hf1_not ⟨s, hs, mem_singleton_iff.mp h1⟩
  let B := connectedComponentIn (bd N.D \ {N.f i 0, N.f i 1}) (N.f i t₀)
  have hB_mem : B ∈ componentsIn (bd N.D \ {N.f i 0, N.f i 1}) :=
    ⟨N.f i t₀, hfIoo_sub ⟨t₀, ht₀, rfl⟩, rfl⟩
  rw [hcomp] at hB_mem
  have hB_sub_fIoo : B ⊆ N.f i '' Ioo (0 : unitInterval) 1 :=
    (N.subset_image_Ioo_f_of_isPreconnected i isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (fun h => (connectedComponentIn_subset _ _ h).2 (Or.inl rfl))
      (fun h => (connectedComponentIn_subset _ _ h).2 (Or.inr rfl))
      ht₀ (mem_connectedComponentIn (hfIoo_sub ⟨t₀, ht₀, rfl⟩))).1
  have hB_eq : B = N.f i '' Ioo (0 : unitInterval) 1 :=
    Subset.antisymm hB_sub_fIoo
      (hfIoo_conn.subset_connectedComponentIn ⟨t₀, ht₀, rfl⟩ hfIoo_sub)
  have hK₁_closed : IsClosed (B₁ ∪ {N.f i 0, N.f i 1}) := by
    have hcomp₁ : IsCompact (range (Subtype.val ∘ h₁)) := isCompact_range (by fun_prop)
    have hrange₁ : range (Subtype.val ∘ h₁) = B₁ ∪ {N.f i 0, N.f i 1} := by
      ext x
      simp only [Function.comp_apply, mem_range]
      exact ⟨by rintro ⟨t, rfl⟩; exact (h₁ t).2, fun hx => ⟨h₁.symm ⟨x, hx⟩, by simp⟩⟩
    rw [← hrange₁]
    exact hcomp₁.isClosed
  have hK₂_closed : IsClosed (B₂ ∪ {N.f i 0, N.f i 1}) := by
    have hcomp₂ : IsCompact (range (Subtype.val ∘ h₂)) := isCompact_range (by fun_prop)
    have hrange₂ : range (Subtype.val ∘ h₂) = B₂ ∪ {N.f i 0, N.f i 1} := by
      ext x
      simp only [Function.comp_apply, mem_range]
      exact ⟨by rintro ⟨t, rfl⟩; exact (h₂ t).2, fun hx => ⟨h₂.symm ⟨x, hx⟩, by simp⟩⟩
    rw [← hrange₂]
    exact hcomp₂.isClosed
  have hex_U₀ : ∃ U₀ : Set N.D, IsOpen U₀ ∧ U₀ ∩ bd N.D = N.f i '' Ioo (0 : unitInterval) 1 := by
    rcases hB_mem with hB₁ | hB₂
    · refine ⟨(B₂ ∪ {N.f i 0, N.f i 1})ᶜ, hK₂_closed.isOpen_compl, ?_⟩
      rw [← hB_eq, hB₁]
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_union, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hxnot, hxbd⟩
        have hxdiff : x ∈ bd N.D \ {N.f i 0, N.f i 1} :=
          ⟨hxbd, fun h => hxnot (Or.inr h)⟩
        exact (hunion ▸ hxdiff).resolve_right fun h => hxnot (Or.inl h)
      · intro hxB₁
        have hxdiff : x ∈ bd N.D \ {N.f i 0, N.f i 1} := hunion ▸ Or.inl hxB₁
        refine ⟨?_, hxdiff.1⟩
        rintro (hxB₂ | hxends)
        · exact Disjoint.notMem_of_mem_left hdisj hxB₁ hxB₂
        · exact hxdiff.2 hxends
    · refine ⟨(B₁ ∪ {N.f i 0, N.f i 1})ᶜ, hK₁_closed.isOpen_compl, ?_⟩
      rw [← hB_eq, hB₂]
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_union, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hxnot, hxbd⟩
        have hxdiff : x ∈ bd N.D \ {N.f i 0, N.f i 1} :=
          ⟨hxbd, fun h => hxnot (Or.inr h)⟩
        exact (hunion ▸ hxdiff).resolve_left fun h => hxnot (Or.inl h)
      · intro hxB₂
        have hxdiff : x ∈ bd N.D \ {N.f i 0, N.f i 1} := hunion ▸ Or.inr hxB₂
        refine ⟨?_, hxdiff.1⟩
        rintro (hxB₁ | hxends)
        · exact Disjoint.notMem_of_mem_right hdisj hxB₂ hxB₁
        · exact hxdiff.2 hxends
  rcases hex_U₀ with ⟨U₀, hU₀_open, hU₀_eq⟩
  let K_left : Set N.D := N.f i '' Iic a
  let K_right : Set N.D := N.f i '' Ici b
  have hK_left : IsClosed K_left :=
    (isClosed_Iic.isCompact.image (N.f i).continuous).isClosed
  have hK_right : IsClosed K_right :=
    (isClosed_Ici.isCompact.image (N.f i).continuous).isClosed
  refine ⟨U₀ ∩ K_leftᶜ ∩ K_rightᶜ, (hU₀_open.inter hK_left.isOpen_compl).inter
    hK_right.isOpen_compl, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_compl_iff, K_left, K_right, mem_image, mem_Iic, mem_Ici, mem_Ioo]
  constructor
  · rintro ⟨⟨⟨hxU₀, hxl⟩, hxr⟩, hxbd⟩
    have hx_fIoo : x ∈ N.f i '' Ioo (0 : unitInterval) 1 := hU₀_eq ▸ ⟨hxU₀, hxbd⟩
    rcases hx_fIoo with ⟨s, _, rfl⟩
    refine ⟨s, ⟨?_, ?_⟩, rfl⟩
    · by_contra! hsa
      exact hxl ⟨s, hsa, rfl⟩
    · by_contra! hbs
      exact hxr ⟨s, hbs, rfl⟩
  · rintro ⟨s, ⟨has, hsb⟩, rfl⟩
    have hs0 : (0 : unitInterval) < s := lt_of_le_of_lt (Subtype.coe_le_coe.mp a.2.1) has
    have hs1 : s < (1 : unitInterval) := lt_of_lt_of_le hsb (Subtype.coe_le_coe.mp b.2.2)
    have hmem : N.f i s ∈ U₀ ∩ bd N.D := hU₀_eq.symm ▸ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨⟨⟨hmem.1, ?_⟩, ?_⟩, hmem.2⟩
    · rintro ⟨t, hta, htf⟩
      have hst : t = s := N.injective_f i htf
      exact (not_le_of_gt has) (hst ▸ hta)
    · rintro ⟨t, hbt, htf⟩
      have hst : t = s := N.injective_f i htf
      exact (not_le_of_gt hsb) (hst ▸ hbt)

/-- For any net `N`, `i : Fin N.r`, and open interval `(a, b) ⊆ (0, 1)`, `N.g i '' Ioo a b` is open
in `bd N.D`: there is an open set `U ⊆ N.D` such that `U ∩ bd N.D = N.g i '' Ioo a b`. -/
theorem exists_isOpen_inter_bd_eq_image_Ioo_g (N : Net S) (i : Fin N.r)
    (a b : unitInterval) :
    ∃ U : Set N.D, IsOpen U ∧ U ∩ bd N.D = N.g i '' Ioo a b :=
  N.swapFG.exists_isOpen_inter_bd_eq_image_Ioo_f i a b

private theorem seam_image_near_arc_interior
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (i : Fin N.r)
    (V₁ : Set N.D)
    (V₂ : Set N.D)
    (Uf₀ : Set N.D)
    (hUf₀_bd : Uf₀ ∩ bd N.D = ⇑(N.f i) '' Ioo 0 1)
    (Ug₀ : Set N.D)
    (hUg₀_bd : Ug₀ ∩ bd N.D = ⇑(N.g i) '' Ioo 0 1) :
    let U₁ := V₁ ∩ Uf₀
      let U₂ := V₂ ∩ Ug₀
      (N.φ '' (U₁ ∪ U₂)ᶜ)ᶜ ∩ N.seamU ⊆ (N.φ ∘ N.f i) '' Ioo (0 : unitInterval) 1 := by
  intro U₁ U₂
  let W₀ := (N.φ '' (U₁ ∪ U₂)ᶜ)ᶜ
  rintro z ⟨hzW₀, x, hxbd, rfl⟩
  have hxU : x ∈ U₁ ∪ U₂ := by
    by_contra hxnot
    exact hzW₀ ⟨x, hxnot, rfl⟩
  rcases hxU with hxU₁ | hxU₂
  · have hxf : x ∈ N.f i '' Ioo (0 : unitInterval) 1 := hUf₀_bd ▸ ⟨hxU₁.2, hxbd⟩
    rcases hxf with ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · have hxg : x ∈ N.g i '' Ioo (0 : unitInterval) 1 := hUg₀_bd ▸ ⟨hxU₂.2, hxbd⟩
    rcases hxg with ⟨s, hs, rfl⟩
    exact ⟨s, hs, N.φ_f_eq_φ_g i s⟩

private theorem net_interior_image_open
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (hφ_closed : IsClosedMap N.φ) :
    ∀ (U : Set N.D), IsOpen U → IsOpen (N.φ '' (U \ bd N.D)) := by
  intro U hU
  have hclosed_compl : IsClosed ((U \ bd N.D)ᶜ) := (hU.sdiff (isClosed_bd N.D)).isClosed_compl
  have heq : N.φ '' (U \ bd N.D) = (N.φ '' (U \ bd N.D)ᶜ)ᶜ := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxU, hxbd⟩, rfl⟩ ⟨y, hy, hφy⟩
      have hxy : x = y := N.interior_inj x hxbd y hφy.symm
      subst hxy
      exact hy ⟨hxU, hxbd⟩
    · intro hz
      obtain ⟨x, rfl⟩ := N.quotientMap_φ.surjective z
      by_cases hx : x ∈ U \ bd N.D
      · exact ⟨x, hx, rfl⟩
      · exact False.elim (hz ⟨x, hx, rfl⟩)
  rw [heq]
  exact (hφ_closed _ hclosed_compl).isOpen_compl

private theorem net_neighborhood_covered_off_boundary
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (i : Fin N.r)
    (U₁ : Set N.D)
    (U₂ : Set N.D)
    (a_ivl : ↑unitInterval)
    (b_ivl : ↑unitInterval)
    (hIoo_ab_sub_bd : (N.φ ∘ N.f i) '' Ioo a_ivl b_ivl ⊆ bd S)
    (Uf₁ : Set N.D)
    (hUf₁_bd : Uf₁ ∩ bd N.D = ⇑(N.f i) '' Ioo a_ivl b_ivl)
    (Ug₁ : Set N.D)
    (hUg₁_bd : Ug₁ ∩ bd N.D = ⇑(N.g i) '' Ioo a_ivl b_ivl)
    :
    let U₁' := U₁ ∩ Uf₁
    let U₂' := U₂ ∩ Ug₁
    ((N.φ '' (U₁' ∪ U₂')ᶜ)ᶜ) \ bd S ⊆ (N.φ '' (U₁' \ bd N.D)) ∪ (N.φ '' (U₂' \ bd N.D)) := by
  intro U₁' U₂'
  let O₁ := N.φ '' (U₁' \ bd N.D)
  let O₂ := N.φ '' (U₂' \ bd N.D)
  let W' := (N.φ '' (U₁' ∪ U₂')ᶜ)ᶜ
  rintro z ⟨hzW', hzbd⟩
  obtain ⟨y, rfl⟩ := N.quotientMap_φ.surjective z
  have hyU : y ∈ U₁' ∪ U₂' := by
    by_contra hny
    exact hzW' ⟨y, hny, rfl⟩
  by_cases hybd : y ∈ bd N.D
  · exfalso
    rcases hyU with hy₁ | hy₂
    · have hy_mem : y ∈ Uf₁ ∩ bd N.D := ⟨hy₁.2, hybd⟩
      rw [hUf₁_bd] at hy_mem
      rcases hy_mem with ⟨u, hu, rfl⟩
      exact hzbd (hIoo_ab_sub_bd ⟨u, hu, rfl⟩)
    · have hy_mem : y ∈ Ug₁ ∩ bd N.D := ⟨hy₂.2, hybd⟩
      rw [hUg₁_bd] at hy_mem
      rcases hy_mem with ⟨u, hu, rfl⟩
      have hgu : N.φ (N.g i u) = (N.φ ∘ N.f i) u := (N.φ_f_eq_φ_g i u).symm
      exact hzbd (hIoo_ab_sub_bd ⟨u, hu, hgu.symm⟩)
  · rcases hyU with hy₁ | hy₂
    · exact Or.inl ⟨y, ⟨hy₁, hybd⟩, rfl⟩
    · exact Or.inr ⟨y, ⟨hy₂, hybd⟩, rfl⟩

private theorem net_arc_map_injective_interior
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (i : Fin N.r)
    (hIoo_pc : IsPathConnected (Ioo (0 : unitInterval) 1)) :
    InjOn (N.φ ∘ ⇑(N.f i)) (Ioo 0 1) := by
  let c := N.φ ∘ ⇑(N.f i)
  intro u₁ hu₁ u₂ hu₂ h12
  have hU_conn : IsPreconnected (N.f i '' Ioo (0 : unitInterval) 1) :=
    (hIoo_pc.image (N.f i).continuous).isConnected.isPreconnected
  have hU_bd : N.f i '' Ioo (0 : unitInterval) 1 ⊆ bd N.D := by
    rintro _ ⟨u, _, rfl⟩; exact N.range_f_subset_bd i ⟨u, rfl⟩
  have hU_disj : Disjoint (N.f i '' Ioo (0 : unitInterval) 1) (N.φ ⁻¹' N.seamV) := by
    rw [disjoint_left]
    rintro _ ⟨u, hu, rfl⟩
    exact N.notMem_seamV_of_mem_Ioo i hu
  exact N.injective_f i
    (N.injOn_φ_of_isPreconnected hU_conn hU_bd hU_disj ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩ h12)

private theorem chart_parameter_injective {S : Type u} (ψ : ℝ → S) (c : unitInterval → S)
    (c_inv : S → unitInterval) {J : Set ℝ}
    (hψ : InjOn ψ J) (himage : ψ '' J ⊆ c '' (c ⁻¹' (ψ '' J)))
    (hleft : LeftInvOn c_inv c (c ⁻¹' (ψ '' J))) :
    InjOn (fun s => (c_inv (ψ s) : ℝ)) J := by
  have hright : ∀ s ∈ J, c (c_inv (ψ s)) = ψ s := by
    intro s hs
    obtain ⟨u, hu, hcu⟩ := himage ⟨s, hs, rfl⟩
    rw [← hcu, hleft hu]
  intro s hs t ht hst
  apply hψ hs ht
  rw [← hright s hs, ← hright t ht, Subtype.ext hst]

private theorem net_subarc_maps_into_boundary
    {S : Type u}
    [TopologicalSpace S]
    {t : unitInterval}
    (c : unitInterval → S)
    (W₀ : Set S)
    (ψ : ℝ → S)
    (s₀ : ℝ)
    (δ : ℝ)
    (hψJ_sub_W₀ : ψ '' (Icc (s₀ - δ) (s₀ + δ)) ⊆ W₀ ∩ bd S)
    (hc_Tψ_eq : c '' (c ⁻¹' (ψ '' (Icc (s₀ - δ) (s₀ + δ)))) = (ψ ''
      (Icc (s₀ - δ) (s₀ + δ))))
    (c_inv : S → unitInterval)
    (hc_inv_left : LeftInvOn c_inv c (c ⁻¹' (ψ '' (Icc (s₀ - δ) (s₀
      + δ)))))
    (hτ_cont : ContinuousOn (fun s => (c_inv (ψ s) : ℝ)) (Icc (s₀ - δ) (s₀ + δ)))
    (hs_left_mem : s₀ - δ ∈ (Icc (s₀ - δ) (s₀ + δ)))
    (hs_right_mem : s₀ + δ ∈ (Icc (s₀ - δ) (s₀ + δ))) :
    c '' Ioo (c_inv (ψ (if (fun s => (c_inv (ψ s) : ℝ)) (s₀ - δ) < ↑t then s₀ - δ else
      s₀ + δ)))
      (c_inv (ψ (if (c_inv (ψ (s₀ - δ)) : ℝ) < t.1 then s₀ + δ else s₀ - δ))) ⊆ bd S := by
  let J_ivl := Icc (s₀ - δ) (s₀ + δ)
  let K_ψ := ψ '' J_ivl
  let T_ψ := c ⁻¹' K_ψ
  let τ := fun s => (c_inv (ψ s) : ℝ)
  let a_ivl := c_inv (ψ (if τ (s₀ - δ) < ↑t then s₀ - δ else s₀ + δ))
  let b_ivl := c_inv (ψ (if τ (s₀ - δ) < ↑t then s₀ + δ else s₀ - δ))
  rintro _ ⟨u, hu, rfl⟩
  have hu_range : u.1 ∈ τ '' J_ivl := by
    refine (isPreconnected_Icc.image τ hτ_cont).Icc_subset ?_ ?_
      ⟨Subtype.coe_le_coe.mpr hu.1.le, Subtype.coe_le_coe.mpr hu.2.le⟩
    · dsimp [a_ivl, τ]
      split_ifs
      · exact ⟨s₀ - δ, hs_left_mem, rfl⟩
      · exact ⟨s₀ + δ, hs_right_mem, rfl⟩
    · dsimp [b_ivl, τ]
      split_ifs
      · exact ⟨s₀ + δ, hs_right_mem, rfl⟩
      · exact ⟨s₀ - δ, hs_left_mem, rfl⟩
  rcases hu_range with ⟨s, hs, hτs⟩
  have hu_eq : u = c_inv (ψ s) := Subtype.ext hτs.symm
  obtain ⟨w, hw, hcw⟩ : ψ s ∈ c '' T_ψ := hc_Tψ_eq.symm ▸ ⟨s, hs, rfl⟩
  have hcu : c u = ψ s := by rw [hu_eq, ← hcw, hc_inv_left hw]
  rw [hcu]
  exact (hψJ_sub_W₀ ⟨s, hs, rfl⟩).2

private theorem net_interior_accumulates {S : Type u} [TopologicalSpace S] (N : Net S)
    {x : N.D} {U : Set N.D} (hU : IsOpen U) (hx : x ∈ U) :
    N.φ x ∈ closure (N.φ '' (U \ bd N.D)) := by
  have hcl : x ∈ closure (U \ bd N.D) := by
    rw [_root_.mem_closure_iff]
    intro V hV hxV
    exact _root_.mem_closure_iff.mp (mem_closure_compl_bd (N.isSurface_D.2.2 x))
      (V ∩ U) (hV.inter hU) ⟨hxV, hx⟩
      |>.imp fun z ⟨⟨hzV, hzU⟩, hzbd⟩ => ⟨hzV, hzU, hzbd⟩
  exact image_closure_subset_closure_image N.quotientMap_φ.continuous ⟨x, hcl, rfl⟩

/-- No interior point of any seam `N.f i '' Ioo 0 1` maps into `bd S`: for every `i : Fin N.r` and
`t ∈ Ioo (0 : unitInterval) 1`, `N.φ (N.f i t) ∉ bd S`. -/
theorem notMem_bd_of_mem_Ioo (hS : IsSurface S) (N : Net S) (i : Fin N.r)
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    N.φ (N.f i t) ∉ bd S := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have : T2Space S := hS.2.1
  intro hp_bd
  let p : S := N.φ (N.f i t)
  let x₁ : N.D := N.f i t
  let x₂ : N.D := N.g i t
  have hx12_ne : x₁ ≠ x₂ := fun h => N.internally_disjoint_fg i i t ht ⟨t, h.symm⟩
  obtain ⟨V₁, V₂, hV₁_open, hV₂_open, hx₁V₁, hx₂V₂, hV_disj⟩ := t2_separation hx12_ne
  obtain ⟨Uf₀, hUf₀_open, hUf₀_bd⟩ := N.exists_isOpen_inter_bd_eq_image_Ioo_f i 0 1
  obtain ⟨Ug₀, hUg₀_open, hUg₀_bd⟩ := N.exists_isOpen_inter_bd_eq_image_Ioo_g i 0 1
  let U₁ : Set N.D := V₁ ∩ Uf₀
  let U₂ : Set N.D := V₂ ∩ Ug₀
  have hU₁_open : IsOpen U₁ := hV₁_open.inter hUf₀_open
  have hU₂_open : IsOpen U₂ := hV₂_open.inter hUg₀_open
  have hx₁U₁ : x₁ ∈ U₁ := by
    have hx₁Uf₀ : x₁ ∈ Uf₀ ∩ bd N.D := by
      rw [hUf₀_bd]
      exact ⟨t, ht, rfl⟩
    exact ⟨hx₁V₁, hx₁Uf₀.1⟩
  have hx₂U₂ : x₂ ∈ U₂ := by
    have hx₂Ug₀ : x₂ ∈ Ug₀ ∩ bd N.D := by
      rw [hUg₀_bd]
      exact ⟨t, ht, rfl⟩
    exact ⟨hx₂V₂, hx₂Ug₀.1⟩
  have hU_disj : Disjoint U₁ U₂ := hV_disj.mono inter_subset_left inter_subset_left
  have hφ_closed : IsClosedMap N.φ := N.quotientMap_φ.continuous.isClosedMap
  let W₀ : Set S := (N.φ '' (U₁ ∪ U₂)ᶜ)ᶜ
  have hW₀_open : IsOpen W₀ := (hφ_closed _ (hU₁_open.union hU₂_open).isClosed_compl).isOpen_compl
  have hpW₀ : p ∈ W₀ := by
    rintro ⟨y, hy, hyp⟩
    rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht hyp.symm with rfl | rfl
    · exact hy (Or.inl hx₁U₁)
    · exact hy (Or.inr hx₂U₂)
  have hW₀_seam : W₀ ∩ N.seamU ⊆ (N.φ ∘ N.f i) '' Ioo (0 : unitInterval) 1 := by
    exact seam_image_near_arc_interior (S := S) N i V₁ V₂ Uf₀ hUf₀_bd Ug₀ hUg₀_bd
  -- Use a boundary chart around `p ∈ bd S` to find an open subinterval `(a, b)` around `t`
  -- mapped into `bd S`.
  obtain ⟨ψ, W₁, hψ_cont, hψ_inj, hW₁_open, hpW₁, hψ_Ioo, hψ_bd⟩ :=
    exists_boundary_chart (hS.2.2 p) hp_bd
  obtain ⟨s₀, hs₀_Ioo, hψs₀⟩ : p ∈ ψ '' Ioo (-1) 1 := hψ_Ioo.symm ▸ ⟨hpW₁, hp_bd⟩
  have hψ_nhds : ψ ⁻¹' W₀ ∈ 𝓝[Icc (-1 : ℝ) 1] s₀ :=
    (hψ_cont s₀ (Ioo_subset_Icc_self hs₀_Ioo)).preimage_mem_nhdsWithin (hW₀_open.mem_nhds
      (hψs₀ ▸ hpW₀))
  obtain ⟨δ₀, hδ₀, hball_ψ⟩ := Metric.mem_nhdsWithin_iff.mp hψ_nhds
  let δ : ℝ := min (δ₀ / 2) (min ((s₀ - (-1)) / 2) ((1 - s₀) / 2))
  have hδ_pos : 0 < δ :=
    lt_min (half_pos hδ₀) (lt_min (half_pos (sub_pos.mpr hs₀_Ioo.1)) (half_pos
      (sub_pos.mpr hs₀_Ioo.2)))
  have hδ_le1 : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ_le2 : δ ≤ (s₀ - (-1)) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le3 : δ ≤ (1 - s₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let J_ivl : Set ℝ := Icc (s₀ - δ) (s₀ + δ)
  have hJ_sub_Ioo : J_ivl ⊆ Ioo (-1 : ℝ) 1 := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hJ_sub_Icc : J_ivl ⊆ Icc (-1 : ℝ) 1 := hJ_sub_Ioo.trans Ioo_subset_Icc_self
  have hψJ_sub_W₀ : ψ '' J_ivl ⊆ W₀ ∩ bd S := by
    rintro _ ⟨s, hs, rfl⟩
    have hs_ball : s ∈ ball s₀ δ₀ := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1, hs.2, hδ_le1], by linarith [hs.1, hs.2, hδ_le1]⟩
    exact ⟨hball_ψ ⟨hs_ball, hJ_sub_Icc hs⟩, hψ_bd ⟨s, hJ_sub_Icc hs, rfl⟩⟩
  let c : unitInterval → S := N.φ ∘ N.f i
  have hc_cont : Continuous c := N.quotientMap_φ.continuous.comp (N.f i).continuous
  have hc_inj_Ioo : InjOn c (Ioo (0 : unitInterval) 1) := by
    exact net_arc_map_injective_interior N i Net.unitInterval_interior_isPathConnected
  let K_ψ : Set S := ψ '' J_ivl
  have hKψ_compact : IsCompact K_ψ := isCompact_Icc.image_of_continuousOn (hψ_cont.mono hJ_sub_Icc)
  have hKψ_sub_cIoo : K_ψ ⊆ c '' Ioo (0 : unitInterval) 1 := fun z hz => by
    have hz' := hψJ_sub_W₀ hz
    exact hW₀_seam ⟨hz'.1, N.bd_subset_seamU hz'.2⟩
  let T_ψ : Set unitInterval := c ⁻¹' K_ψ
  have hTψ_closed : IsClosed T_ψ := hKψ_compact.isClosed.preimage hc_cont
  have hTψ_compact : IsCompact T_ψ := hTψ_closed.isCompact
  have hTψ_sub_Ioo : T_ψ ⊆ Ioo (0 : unitInterval) 1 := by
    intro u hu
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo u with rfl | rfl | hu_Ioo
    · rcases hKψ_sub_cIoo hu with ⟨w, hw, hcw⟩
      exact False.elim (N.notMem_seamV_of_mem_Ioo i hw ⟨i, Or.inl hcw.symm⟩)
    · rcases hKψ_sub_cIoo hu with ⟨w, hw, hcw⟩
      exact False.elim (N.notMem_seamV_of_mem_Ioo i hw ⟨i, Or.inr hcw.symm⟩)
    · exact hu_Ioo
  have hc_Tψ_eq : c '' T_ψ = K_ψ := by
    apply Subset.antisymm (image_preimage_subset c K_ψ)
    intro z hz
    rcases hKψ_sub_cIoo hz with ⟨u, _, rfl⟩
    exact ⟨u, hz, rfl⟩
  obtain ⟨c_inv, hc_inv_cont, hc_inv_left⟩ :=
    exists_inv_of_compactOn hTψ_compact hc_cont.continuousOn (hc_inj_Ioo.mono hTψ_sub_Ioo)
  let τ : ℝ → ℝ := fun s => (c_inv (ψ s)).1
  have hτ_cont : ContinuousOn τ J_ivl := by
    refine continuous_subtype_val.comp_continuousOn (hc_inv_cont.comp (hψ_cont.mono hJ_sub_Icc) ?_)
    intro s hs
    rw [hc_Tψ_eq]
    exact ⟨s, hs, rfl⟩
  have hτ_inj : InjOn τ J_ivl := by
    exact chart_parameter_injective ψ c c_inv (hψ_inj.mono hJ_sub_Icc)
      (hc_Tψ_eq ▸ subset_rfl) hc_inv_left
  have ht_Tψ : t ∈ T_ψ := by
    change c t ∈ K_ψ
    have hct : c t = ψ s₀ := hψs₀.symm
    rw [hct]
    exact ⟨s₀, ⟨by linarith, by linarith⟩, rfl⟩
  have hτ_s₀ : τ s₀ = t.1 := by
    change (c_inv (ψ s₀)).1 = t.1
    have hct : ψ s₀ = c t := hψs₀
    rw [hct]
    exact congr_arg Subtype.val (hc_inv_left ht_Tψ)
  have hs_left_mem : s₀ - δ ∈ J_ivl := ⟨le_rfl, by linarith⟩
  have hs_right_mem : s₀ + δ ∈ J_ivl := ⟨by linarith, le_rfl⟩
  have hs₀_mem : s₀ ∈ J_ivl := ⟨by linarith, by linarith⟩
  have h_between : (τ (s₀ - δ) < t.1 ∧ t.1 < τ (s₀ + δ)) ∨
      (τ (s₀ + δ) < t.1 ∧ t.1 < τ (s₀ - δ)) := by
    rw [← hτ_s₀]
    rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (by linarith : s₀ - δ ≤ s₀ + δ)
      hτ_cont hτ_inj with hmono | hanti
    · exact .inl ⟨hmono hs_left_mem hs₀_mem (by linarith),
        hmono hs₀_mem hs_right_mem (by linarith)⟩
    · exact .inr ⟨hanti hs₀_mem hs_right_mem (by linarith),
        hanti hs_left_mem hs₀_mem (by linarith)⟩
  let a_ivl : unitInterval := c_inv (ψ (if τ (s₀ - δ) < t.1 then s₀ - δ else s₀ + δ))
  let b_ivl : unitInterval := c_inv (ψ (if τ (s₀ - δ) < t.1 then s₀ + δ else s₀ - δ))
  have hat : a_ivl < t := by
    rw [← Subtype.coe_lt_coe]
    dsimp [a_ivl]
    split_ifs with hlt
    · exact hlt
    · exact (h_between.resolve_left fun h => hlt h.1).1
  have htb : t < b_ivl := by
    rw [← Subtype.coe_lt_coe]
    dsimp [b_ivl]
    split_ifs with hlt
    · exact (h_between.resolve_right fun h => not_lt_of_gt h.2 hlt).2
    · exact (h_between.resolve_left fun h => hlt h.1).2
  have hab_ivl : a_ivl < b_ivl := hat.trans htb
  have hIoo_ab_sub_bd : c '' Ioo a_ivl b_ivl ⊆ bd S := by
    exact net_subarc_maps_into_boundary (t := t) c W₀ ψ s₀ δ hψJ_sub_W₀ hc_Tψ_eq c_inv
      hc_inv_left hτ_cont hs_left_mem hs_right_mem
  -- Shrink `U₁, U₂` so that `W' ∩ N.seamU ⊆ c '' Ioo a_ivl b_ivl ⊆ bd S`.
  obtain ⟨Uf₁, hUf₁_open, hUf₁_bd⟩ := N.exists_isOpen_inter_bd_eq_image_Ioo_f i a_ivl b_ivl
  obtain ⟨Ug₁, hUg₁_open, hUg₁_bd⟩ := N.exists_isOpen_inter_bd_eq_image_Ioo_g i a_ivl b_ivl
  let U₁' : Set N.D := U₁ ∩ Uf₁
  let U₂' : Set N.D := U₂ ∩ Ug₁
  have hU₁'_open : IsOpen U₁' := hU₁_open.inter hUf₁_open
  have hU₂'_open : IsOpen U₂' := hU₂_open.inter hUg₁_open
  have hx₁U₁' : x₁ ∈ U₁' := by
    have hx₁Uf₁ : x₁ ∈ Uf₁ ∩ bd N.D := by
      rw [hUf₁_bd]
      exact ⟨t, ⟨hat, htb⟩, rfl⟩
    exact ⟨hx₁U₁, hx₁Uf₁.1⟩
  have hx₂U₂' : x₂ ∈ U₂' := by
    have hx₂Ug₁ : x₂ ∈ Ug₁ ∩ bd N.D := by
      rw [hUg₁_bd]
      exact ⟨t, ⟨hat, htb⟩, rfl⟩
    exact ⟨hx₂U₂, hx₂Ug₁.1⟩
  have hU'_disj : Disjoint U₁' U₂' := hU_disj.mono inter_subset_left inter_subset_left
  let O₁ : Set S := N.φ '' (U₁' \ bd N.D)
  let O₂ : Set S := N.φ '' (U₂' \ bd N.D)
  have hopen_map_compl : ∀ U : Set N.D, IsOpen U → IsOpen (N.φ '' (U \ bd N.D)) := by
    exact net_interior_image_open (S := S) N hφ_closed
  have hO₁_open : IsOpen O₁ := hopen_map_compl U₁' hU₁'_open
  have hO₂_open : IsOpen O₂ := hopen_map_compl U₂' hU₂'_open
  have hO_disj : Disjoint O₁ O₂ := by
    rw [disjoint_iff_forall_ne]
    rintro _ ⟨y₁, ⟨hy₁U, hy₁bd⟩, rfl⟩ _ ⟨y₂, ⟨hy₂U, _⟩, rfl⟩ heq
    have hy12 : y₁ = y₂ := N.interior_inj y₁ hy₁bd y₂ heq
    subst hy12
    exact hU'_disj.le_bot ⟨hy₁U, hy₂U⟩
  have hp_cl_O₁ : p ∈ closure O₁ := by
    exact net_interior_accumulates N hU₁'_open hx₁U₁'
  have hp_cl_O₂ : p ∈ closure O₂ := by
    change N.φ (N.f i t) ∈ closure O₂
    rw [N.φ_f_eq_φ_g i t]
    exact net_interior_accumulates N hU₂'_open hx₂U₂'
  let W' : Set S := (N.φ '' (U₁' ∪ U₂')ᶜ)ᶜ
  have hW'_open : IsOpen W' :=
    (hφ_closed _ (hU₁'_open.union hU₂'_open).isClosed_compl).isOpen_compl
  have hpW' : p ∈ W' := by
    rintro ⟨y, hy, hφy⟩
    rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht hφy.symm with rfl | rfl
    · exact hy (Or.inl hx₁U₁')
    · exact hy (Or.inr hx₂U₂')
  have hW'_sdiff_bd : W' \ bd S ⊆ O₁ ∪ O₂ := by
    exact net_neighborhood_covered_off_boundary (S := S) N i U₁ U₂ a_ivl b_ivl
      hIoo_ab_sub_bd Uf₁ hUf₁_bd Ug₁ hUg₁_bd
  obtain ⟨V, P, hV_open, hpV, hVW', hPV, hP_pre, hP_int, hV_clP⟩ :=
    (hS.2.2 p).exists_half hW'_open hpW'
  have hP_union : P ⊆ O₁ ∪ O₂ := fun z hz => hW'_sdiff_bd ⟨hVW' (hPV hz), fun hbd => hbd
    (hP_int z hz)⟩
  rcases hP_pre.subset_or_subset hO₁_open hO₂_open hO_disj hP_union with hPO₁ | hPO₂
  · have hclP_disj : Disjoint (closure P) O₂ :=
      (Disjoint.mono_left hPO₁ hO_disj).closure_left hO₂_open
    have hV_disj : Disjoint V O₂ := hclP_disj.mono_left hV_clP
    obtain ⟨z, hzV, hzO₂⟩ := _root_.mem_closure_iff.mp hp_cl_O₂ V hV_open hpV
    exact hV_disj.le_bot ⟨hzV, hzO₂⟩
  · have hclP_disj : Disjoint (closure P) O₁ :=
      (Disjoint.mono_left hPO₂ hO_disj.symm).closure_left hO₁_open
    have hV_disj : Disjoint V O₁ := hclP_disj.mono_left hV_clP
    obtain ⟨z, hzV, hzO₁⟩ := _root_.mem_closure_iff.mp hp_cl_O₁ V hV_open hpV
    exact hV_disj.le_bot ⟨hzV, hzO₁⟩

/-! ## 2. Boundary cuffs and edge counting (`|E(J)| = r + |bd(S) ∩ V(J)|`) -/

/-- Every cuff `C ∈ cuffs S` of a surface `S` is closed in `S`. -/
theorem isClosed_of_mem_cuffs (hS : IsSurface S) {C : Set S} (hC : C ∈ cuffs S) :
    IsClosed C := by
  have : T2Space S := hS.2.1
  obtain ⟨e⟩ := (cuff_statement S hS).2.2 C hC
  have hcomp : IsCompact (range (Subtype.val ∘ e)) := isCompact_range (by fun_prop)
  have hrange : range (Subtype.val ∘ e) = C := by
    ext x
    simp only [Function.comp_apply, mem_range]
    exact ⟨by rintro ⟨t, rfl⟩; exact (e t).2, fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
  rw [← hrange]
  exact hcomp.isClosed

/-- For every cuff `C ∈ cuffs S`, `bd S \ C` is closed in `S`. -/
theorem isClosed_bd_sdiff_cuff (hS : IsSurface S) {C : Set S} (hC : C ∈ cuffs S) :
    IsClosed (bd S \ C) := by
  have hfin : (cuffs S \ {C}).Finite := (cuff_statement S hS).2.1.sdiff
  have heq : bd S \ C = ⋃₀ (cuffs S \ {C}) := by
    ext x
    simp only [Set.mem_sdiff, mem_sUnion, mem_singleton_iff]
    constructor
    · rintro ⟨hxbd, hxC⟩
      rw [← sUnion_cuffs (S := S)] at hxbd
      rcases hxbd with ⟨C', hC', hxC'⟩
      refine ⟨C', ⟨hC', ?_⟩, hxC'⟩
      rintro rfl
      exact hxC hxC'
    · rintro ⟨C', ⟨hC', hne⟩, hxC'⟩
      have hxbd : x ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨C', hC', hxC'⟩
      refine ⟨hxbd, fun hxC => ?_⟩
      exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne) hxC' hxC
  rw [heq]
  exact hfin.isClosed_sUnion fun C' hC' => isClosed_of_mem_cuffs hS hC'.1

/-- Every cuff `C ∈ cuffs S` of a surface `S` contains at least one vertex of `N.seamV` whenever
`0 < N.r`. -/
theorem cuff_inter_seamV_nonempty (hS : IsSurface S) (N : Net S) (hpos : 0 < N.r)
    {C : Set S} (hC : C ∈ cuffs S) :
    (C ∩ N.seamV).Nonempty := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have : T2Space S := hS.2.1
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  let A₁ : Set N.D := bd N.D ∩ N.φ ⁻¹' C
  let A₂ : Set N.D := bd N.D \ N.φ ⁻¹' C
  have hA₁_closed : IsClosed A₁ :=
    (isClosed_bd N.D).inter ((isClosed_of_mem_cuffs hS hC).preimage N.quotientMap_φ.continuous)
  have hA₂_eq : A₂ =
      (⋃ i : Fin N.r, (range (N.f i) ∪ range (N.g i))) ∪
        (bd N.D ∩ N.φ ⁻¹' (bd S \ C)) := by
    ext x
    simp only [A₂, Set.mem_sdiff, mem_preimage, mem_union, mem_iUnion, mem_range, mem_inter_iff]
    constructor
    · rintro ⟨hxbd, hxC⟩
      by_cases hxbdS : N.φ x ∈ bd S
      · exact Or.inr ⟨hxbd, hxbdS, hxC⟩
      · by_cases hxV : N.φ x ∈ N.seamV
        · obtain ⟨i, hi⟩ := mem_iUnion.mp (N.preimage_seamV_subset_endpoints hxV)
          simp only [mem_insert_iff, mem_singleton_iff] at hi
          rcases hi with rfl | rfl | rfl | rfl
          · exact Or.inl ⟨i, Or.inl ⟨0, rfl⟩⟩
          · exact Or.inl ⟨i, Or.inl ⟨1, rfl⟩⟩
          · exact Or.inl ⟨i, Or.inr ⟨0, rfl⟩⟩
          · exact Or.inl ⟨i, Or.inr ⟨1, rfl⟩⟩
        · obtain ⟨i, w, hw, -, hfib, -⟩ :=
            N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hxbd hxbdS hxV
          have hx_mem : x ∈ N.φ ⁻¹' {N.φ x} := rfl
          rw [hfib, mem_insert_iff, mem_singleton_iff] at hx_mem
          rcases hx_mem with rfl | rfl
          · exact Or.inl ⟨i, Or.inl ⟨w, rfl⟩⟩
          · exact Or.inl ⟨i, Or.inr ⟨w, rfl⟩⟩
    · rintro (⟨i, ⟨t, rfl⟩ | ⟨t, rfl⟩⟩ | ⟨hxbd, hxbdS, hxC⟩)
      · refine ⟨N.range_f_subset_bd i ⟨t, rfl⟩, fun hφC => ?_⟩
        rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact hemp.subset ⟨hφC, i, Or.inl rfl⟩
        · exact hemp.subset ⟨hφC, i, Or.inr rfl⟩
        · exact N.notMem_bd_of_mem_Ioo hS i ht (sUnion_cuffs (S := S) ▸ ⟨C, hC, hφC⟩)
      · refine ⟨N.range_g_subset_bd i ⟨t, rfl⟩, fun hφC => ?_⟩
        have hφf : N.φ (N.f i t) ∈ C := (N.φ_f_eq_φ_g i t).symm ▸ hφC
        rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact hemp.subset ⟨hφf, i, Or.inl rfl⟩
        · exact hemp.subset ⟨hφf, i, Or.inr rfl⟩
        · exact N.notMem_bd_of_mem_Ioo hS i ht (sUnion_cuffs (S := S) ▸ ⟨C, hC, hφf⟩)
      · exact ⟨hxbd, hxC⟩
  have hA₂_closed : IsClosed A₂ := by
    rw [hA₂_eq]
    refine (isClosed_iUnion_of_finite fun i => ?_).union
      ((isClosed_bd N.D).inter ((isClosed_bd_sdiff_cuff hS hC).preimage N.quotientMap_φ.continuous))
    exact (isCompact_range (N.f i).continuous).isClosed.union
      (isCompact_range (N.g i).continuous).isClosed
  have hA₁_ne : A₁.Nonempty := by
    obtain ⟨y, hybd, rfl⟩ := hC
    obtain ⟨x, rfl⟩ := N.quotientMap_φ.surjective y
    have hxbd : x ∈ bd N.D := by
      rw [← N.preimage_seamU]
      exact N.bd_subset_seamU hybd
    exact ⟨x, hxbd, mem_connectedComponentIn hybd⟩
  have hA₂_ne : A₂.Nonempty := by
    refine ⟨N.f ⟨0, hpos⟩ 0, ?_⟩
    rw [hA₂_eq]
    exact Or.inl (mem_iUnion.mpr ⟨⟨0, hpos⟩, Or.inl ⟨0, rfl⟩⟩)
  have hcov : bd N.D ⊆ A₁ ∪ A₂ := fun x hx => by
    by_cases hxC : N.φ x ∈ C
    · exact Or.inl ⟨hx, hxC⟩
    · exact Or.inr ⟨hx, hxC⟩
  obtain ⟨z, _, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp
    N.isOArc_bd_D.isPreconnected A₁ A₂ hA₁_closed hA₂_closed hcov
    ⟨hA₁_ne.some, hA₁_ne.some_mem.1, hA₁_ne.some_mem⟩
    ⟨hA₂_ne.some, hA₂_ne.some_mem.1, hA₂_ne.some_mem⟩
  exact hz₂.2 hz₁.2

/-- Whenever `N.IsSeamGraphFor J`, we have `0 < N.r` because `J.V = N.seamV` is nonempty. -/
theorem r_pos_of_isSeamGraphFor (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J) :
    0 < N.r :=
  hJ.1

/-- For any finite nonempty subset `V ⊆ Circle`, the arc-wise connected components of `Vᶜ` are
precisely `nextSegment V v` for `v ∈ V`, and there are `V.ncard` of them. -/
theorem arcComponentsIn_compl_circle {V : Set Circle} (hV : V.Finite) (hne : V.Nonempty) :
    arcComponentsIn (Vᶜ) = (nextSegment V) '' V ∧
      (arcComponentsIn (Vᶜ)).ncard = V.ncard := by
  have hseg_pc : ∀ v ∈ V, IsPathConnected (nextSegment V v) := by
    intro v hv
    obtain ⟨e⟩ := nonempty_homeomorph_Ioo_nextSegment hV hv
    have : PathConnectedSpace (Ioo (0 : ℝ) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp
        ((convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num, by norm_num⟩)
    have heq : range (Subtype.val ∘ e) = nextSegment V v := by
      ext z
      simp only [Function.comp_apply, mem_range]
      exact ⟨by rintro ⟨t, rfl⟩; exact (e t).2, fun hz => ⟨e.symm ⟨z, hz⟩, by simp⟩⟩
    rw [← heq]
    exact isPathConnected_range (continuous_subtype_val.comp e.continuous)
  have hseg_mem : ∀ v ∈ V, nextSegment V v ∈ arcComponentsIn (Vᶜ) := by
    intro v hv
    obtain ⟨z, hz⟩ := nextSegment_nonempty hV hv
    refine ⟨⟨z, hz⟩, nextSegment_subset_compl, hseg_pc v hv, ?_⟩
    intro D hDV hDpc hsub
    apply Subset.antisymm _ hsub
    rw [← connectedComponentIn_compl_eq_nextSegment hV hv hz]
    exact hDpc.isConnected.isPreconnected.subset_connectedComponentIn (hsub hz) hDV
  have heq : arcComponentsIn (Vᶜ) = (nextSegment V) '' V := by
    ext E
    simp only [mem_image]
    constructor
    · intro hE
      obtain ⟨z, hzE⟩ := hE.1
      have hzV : z ∈ Vᶜ := hE.2.1 hzE
      obtain ⟨v, ⟨hv, hzv⟩, -⟩ := exists_unique_nextSegment_of_mem_compl hV hne hzV
      refine ⟨v, hv, ?_⟩
      have hsub : E ⊆ nextSegment V v := by
        rw [← connectedComponentIn_compl_eq_nextSegment hV hv hzv]
        exact hE.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hzE hE.2.1
      exact hE.2.2.2 (nextSegment V v) nextSegment_subset_compl (hseg_pc v hv) hsub
    · rintro ⟨v, hv, rfl⟩
      exact hseg_mem v hv
  have hinj : InjOn (nextSegment V) V := by
    intro v₁ hv₁ v₂ hv₂ h12
    obtain ⟨z, hz₁⟩ := nextSegment_nonempty hV hv₁
    have hz₂ : z ∈ nextSegment V v₂ := h12 ▸ hz₁
    have hzV : z ∈ Vᶜ := nextSegment_subset_compl hz₁
    obtain ⟨v, _, huniq⟩ := exists_unique_nextSegment_of_mem_compl hV hne hzV
    exact (huniq v₁ ⟨hv₁, hz₁⟩).trans (huniq v₂ ⟨hv₂, hz₂⟩).symm
  exact ⟨heq, by rw [heq, Set.InjOn.ncard_image hinj]⟩

/-- For each cuff `C ∈ cuffs S` and seam graph `J` of a net `N`, the number of arc-wise connected
components of `C \ J.V` equals `(C ∩ J.V).ncard` (and is finite). -/
theorem ncard_arcComponentsIn_cuff_sdiff (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) {C : Set S} (hC : C ∈ cuffs S) :
    (arcComponentsIn (C \ J.V)).Finite ∧
      (arcComponentsIn (C \ J.V)).ncard = (C ∩ J.V).ncard := by
  have : T2Space S := hS.2.1
  obtain ⟨φ_C⟩ := (cuff_statement S hS).2.2 C hC
  let ι : Circle → S := Subtype.val ∘ φ_C
  have hι_cont : Continuous ι := continuous_subtype_val.comp φ_C.continuous
  have hι_inj : Function.Injective ι := Subtype.val_injective.comp φ_C.injective
  let V_C : Set Circle := ι ⁻¹' J.V
  have hVC_fin : V_C.Finite := J.finite_V.preimage hι_inj.injOn
  have hVC_ne : V_C.Nonempty := by
    obtain ⟨x, hxC, hxV⟩ := N.cuff_inter_seamV_nonempty hS hJ.1 hC
    refine ⟨φ_C.symm ⟨x, hxC⟩, ?_⟩
    rw [mem_preimage, hJ.2.2]
    simpa [ι] using hxV
  have hι_VC : ι '' V_C = C ∩ J.V := by
    ext x
    simp only [V_C, ι, Function.comp_apply, mem_image, mem_preimage, mem_inter_iff]
    exact ⟨by rintro ⟨z, hz, rfl⟩; exact ⟨(φ_C z).2, hz⟩,
      fun ⟨hxC, hxV⟩ => ⟨φ_C.symm ⟨x, hxC⟩, by simpa using hxV, by simp⟩⟩
  have hι_compl : ι '' (V_Cᶜ) = C \ J.V := by
    ext x
    simp only [V_C, ι, Function.comp_apply, mem_image, mem_compl_iff, mem_preimage, Set.mem_sdiff]
    exact ⟨by rintro ⟨z, hz, rfl⟩; exact ⟨(φ_C z).2, hz⟩,
      fun ⟨hxC, hxV⟩ => ⟨φ_C.symm ⟨x, hxC⟩, by simpa using hxV, by simp⟩⟩
  obtain ⟨g, hg_cont, hgi⟩ :=
    exists_inv_of_compactOn (isCompact_univ (X := Circle)) hι_cont.continuousOn hι_inj.injOn
  have harc_img : arcComponentsIn (C \ J.V) = image ι '' arcComponentsIn (V_Cᶜ) := by
    rw [← hι_compl]
    exact GM11.arcComponentsIn_image hι_cont.continuousOn
      (hg_cont.mono (image_mono (subset_univ _))) (fun z _ => hgi (mem_univ z))
  obtain ⟨harc_eq, hncard_VC⟩ := arcComponentsIn_compl_circle hVC_fin hVC_ne
  have harc_fin : (arcComponentsIn (V_Cᶜ)).Finite := by
    rw [harc_eq]
    exact hVC_fin.image _
  refine ⟨harc_img ▸ harc_fin.image _, ?_⟩
  rw [harc_img, ncard_image_of_injective _ (Set.image_injective.mpr hι_inj), hncard_VC,
    ← hι_VC, ncard_image_of_injective _ hι_inj]

/-- The number of arc-wise connected components of `bd S \ J.V` equals `(bd S ∩ J.V).ncard`. -/
theorem ncard_arcComponentsIn_bd_sdiff (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    (arcComponentsIn (bd S \ J.V)).Finite ∧
      (arcComponentsIn (bd S \ J.V)).ncard = (bd S ∩ J.V).ncard := by
  have : T2Space S := hS.2.1
  have hkey : ∀ 𝓐 : Set (Set S), 𝓐.Finite → 𝓐 ⊆ cuffs S →
      (arcComponentsIn ((⋃₀ 𝓐) \ J.V)).Finite ∧
        (arcComponentsIn ((⋃₀ 𝓐) \ J.V)).ncard = ((⋃₀ 𝓐) ∩ J.V).ncard := by
    intro 𝓐 h𝓐
    induction 𝓐, h𝓐 using Set.Finite.induction_on with
    | empty =>
      intro _
      have hemp : arcComponentsIn ((⋃₀ (∅ : Set (Set S))) \ J.V) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        rintro E ⟨⟨x, hx⟩, hsub, _⟩
        exact absurd (hsub hx) (by simp)
      rw [hemp]
      simp
    | @insert C 𝓐 hC_not_mem h𝓐_fin ih =>
      intro hsub
      have hC_cuff : C ∈ cuffs S := hsub (mem_insert _ _)
      have h𝓐_sub : 𝓐 ⊆ cuffs S := (subset_insert _ _).trans hsub
      obtain ⟨hfin_𝓐, hncard_𝓐⟩ := ih h𝓐_sub
      obtain ⟨hfin_C, hncard_C⟩ := N.ncard_arcComponentsIn_cuff_sdiff hS hJ hC_cuff
      have hC_closed : IsClosed C := isClosed_of_mem_cuffs hS hC_cuff
      have h𝓐_closed : IsClosed (⋃₀ 𝓐) :=
        h𝓐_fin.isClosed_sUnion fun C' hC' => isClosed_of_mem_cuffs hS (h𝓐_sub hC')
      have hdisj_C_𝓐 : Disjoint C (⋃₀ 𝓐) := by
        rw [Set.disjoint_left]
        rintro x hxC ⟨C', hC', hxC'⟩
        have hne : C ≠ C' := fun h => hC_not_mem (h ▸ hC')
        exact Set.disjoint_left.mp (cuffs_disjoint hC_cuff (h𝓐_sub hC') hne) hxC hxC'
      have hsdiff_eq : (⋃₀ insert C 𝓐) \ J.V = (C \ J.V) ∪ ((⋃₀ 𝓐) \ J.V) := by
        rw [sUnion_insert, union_sdiff_distrib]
      have harc_union :
          arcComponentsIn ((⋃₀ insert C 𝓐) \ J.V) =
            arcComponentsIn (C \ J.V) ∪ arcComponentsIn ((⋃₀ 𝓐) \ J.V) := by
        rw [hsdiff_eq]
        exact GM11.arcComponentsIn_union hC_closed h𝓐_closed sdiff_subset sdiff_subset
          fun x _ hxC hx𝓐 => Set.disjoint_left.mp hdisj_C_𝓐 hxC hx𝓐
      have hdisj_arc : Disjoint (arcComponentsIn (C \ J.V)) (arcComponentsIn ((⋃₀ 𝓐) \ J.V)) := by
        rw [Set.disjoint_left]
        intro E hEC hE𝓐
        obtain ⟨x, hx⟩ := hEC.1
        exact Set.disjoint_left.mp hdisj_C_𝓐 (hEC.2.1 hx).1 (hE𝓐.2.1 hx).1
      have hinter_eq : (⋃₀ insert C 𝓐) ∩ J.V = (C ∩ J.V) ∪ ((⋃₀ 𝓐) ∩ J.V) := by
        rw [sUnion_insert, union_inter_distrib_right]
      have hdisj_V : Disjoint (C ∩ J.V) ((⋃₀ 𝓐) ∩ J.V) :=
        hdisj_C_𝓐.mono inter_subset_left inter_subset_left
      refine ⟨harc_union ▸ hfin_C.union hfin_𝓐, ?_⟩
      rw [harc_union, ncard_union_eq hdisj_arc hfin_C hfin_𝓐, hncard_C, hncard_𝓐,
        hinter_eq, ncard_union_eq hdisj_V (J.finite_V.subset inter_subset_right)
          (J.finite_V.subset inter_subset_right)]
  simpa [sUnion_cuffs] using hkey (cuffs S) (cuff_statement S hS).2.1 Subset.rfl

/-! ### Explicit edge decomposition of a seam graph -/

/-- The `i`-th interior seam curve `N.φ ∘ N.f i : C(unitInterval, S)`. -/
def interiorSeamCurve (N : Net S) (i : Fin N.r) : C(unitInterval, S) :=
  ⟨N.φ ∘ N.f i, N.quotientMap_φ.continuous.comp (N.f i).continuous⟩

/-- The `i`-th interior seam edge `(N.φ ∘ N.f i) '' Ioo 0 1`. -/
def interiorSeamEdge (N : Net S) (i : Fin N.r) : Set S :=
  N.interiorSeamCurve i '' Ioo (0 : unitInterval) 1

theorem e_int_isLink [T2Space S] (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    (i : Fin N.r) :
    J.toGraph.IsLink (N.interiorSeamEdge i) (N.φ (N.f i 0)) (N.φ (N.f i 1)) := by
  refine (Drawing.eq_edge_of_injOn_Ioo J (N.interiorSeamCurve i) ?_ ?_ ?_ ?_).2
  · rw [hJ.2.2]
    exact ⟨i, Or.inl rfl⟩
  · rw [hJ.2.2]
    exact ⟨i, Or.inr rfl⟩
  · intro t ht
    rw [hJ.2.1, hJ.2.2]
    exact ⟨⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩, N.notMem_seamV_of_mem_Ioo i ht⟩
  · intro t₁ ht₁ t₂ _ h12
    rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht₁ h12 with hff | hfg
    · exact (N.injective_f i hff).symm
    · exact False.elim (N.internally_disjoint_gf i i t₁ ht₁ ⟨t₂, hfg⟩)

theorem e_int_mem_E [T2Space S] (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    (i : Fin N.r) : N.interiorSeamEdge i ∈ J.E :=
  (N.e_int_isLink hJ i).edge_mem

theorem tilde_e_int [T2Space S] (N : Net S) {J : Drawing S} (hJ : N.IsSeamGraphFor J)
    (i : Fin N.r) :
    tilde (N.interiorSeamEdge i) = {N.φ (N.f i 0), N.φ (N.f i 1)} := by
  rw [tilde_eq_closure_inter_V J (N.e_int_mem_E hJ i)]
  have hlink := N.e_int_isLink hJ i
  unfold Drawing.toGraph at hlink
  exact hlink.2.2.2

theorem e_int_injective (N : Net S) : Function.Injective N.interiorSeamEdge := by
  intro i j hij
  let t₀ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t₀]
  have hmem : N.interiorSeamCurve i t₀ ∈ N.interiorSeamEdge j := hij ▸ ⟨t₀, ht₀, rfl⟩
  rcases hmem with ⟨s, _, hs_eq⟩
  by_contra hne
  rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ht₀ hs_eq.symm with hff | hfg
  · exact N.internally_disjoint_ff i j hne t₀ ht₀ ⟨s, hff⟩
  · exact N.internally_disjoint_gf i j t₀ ht₀ ⟨s, hfg⟩

theorem disjoint_e_int_bd (hS : IsSurface S) (N : Net S) (i : Fin N.r) :
    Disjoint (N.interiorSeamEdge i) (bd S) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ hbd
  exact N.notMem_bd_of_mem_Ioo hS i ht hbd

theorem seamGraph_edges_eq (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    J.E = range N.interiorSeamEdge ∪ arcComponentsIn (bd S \ J.V) ∧
      Disjoint (range N.interiorSeamEdge) (arcComponentsIn (bd S \ J.V)) := by
  have : T2Space S := hS.2.1
  let A : Set S := (J.U \ J.V) \ bd S
  let B : Set S := bd S \ J.V
  have hA_eq : A = ⋃ i : Fin N.r, N.interiorSeamEdge i := by
    ext p
    simp only [A, interiorSeamEdge, interiorSeamCurve, ContinuousMap.coe_mk, Function.comp_apply,
      Set.mem_sdiff,
      mem_iUnion, mem_image]
    constructor
    · rintro ⟨⟨hpU, hpV⟩, hpbd⟩
      rw [hJ.2.1] at hpU
      rw [hJ.2.2] at hpV
      obtain ⟨x, hxbd, rfl⟩ := hpU
      obtain ⟨i, w, hw, hφw, -, -⟩ :=
        N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hxbd hpbd hpV
      exact ⟨i, w, hw, hφw⟩
    · rintro ⟨i, t, ht, rfl⟩
      rw [hJ.2.1, hJ.2.2]
      exact ⟨⟨⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩,
        N.notMem_seamV_of_mem_Ioo i ht⟩, N.notMem_bd_of_mem_Ioo hS i ht⟩
  let U₁ : Set S := ⋃ i : Fin N.r, range (N.interiorSeamCurve i)
  have hU₁_closed : IsClosed U₁ :=
    isClosed_iUnion_of_finite fun i => (isCompact_range (N.interiorSeamCurve i).continuous).isClosed
  have hA_sub_U₁ : A ⊆ U₁ := by
    rw [hA_eq]
    exact iUnion_mono fun i => image_subset_range _ _
  have hUV_eq : J.U \ J.V = A ∪ B := by
    ext p
    simp only [A, B, Set.mem_sdiff, mem_union]
    have hbd_sub : bd S ⊆ J.U := hJ.2.1 ▸ N.bd_subset_seamU
    by_cases hpbd : p ∈ bd S
    · exact ⟨fun ⟨_, hpV⟩ => Or.inr ⟨hpbd, hpV⟩,
        by rintro (⟨⟨_, hpV⟩, _⟩ | ⟨_, hpV⟩) <;> exact ⟨hbd_sub hpbd, hpV⟩⟩
    · constructor
      · intro hp
        exact Or.inl ⟨hp, hpbd⟩
      · rintro (⟨hp, _⟩ | ⟨hpbd', _⟩)
        · exact hp
        · exact False.elim (hpbd hpbd')
  have hAB_disj : ∀ x ∈ A ∪ B, x ∈ U₁ → x ∉ bd S := by
    intro x hx hu₁ hxbd
    rw [mem_iUnion] at hu₁
    rcases hu₁ with ⟨i, t, rfl⟩
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · rw [← hUV_eq] at hx
      exact hx.2 (hJ.2.2 ▸ ⟨i, Or.inl rfl⟩)
    · rw [← hUV_eq] at hx
      exact hx.2 (hJ.2.2 ▸ ⟨i, Or.inr rfl⟩)
    · exact N.notMem_bd_of_mem_Ioo hS i ht hxbd
  have harc_union : J.E = arcComponentsIn A ∪ arcComponentsIn B := by
    change arcComponentsIn (J.U \ J.V) = _
    rw [hUV_eq]
    exact GM11.arcComponentsIn_union hU₁_closed (isClosed_bd S) hA_sub_U₁ sdiff_subset hAB_disj
  have harc_A : arcComponentsIn A = range N.interiorSeamEdge := by
    ext E
    simp only [mem_range]
    constructor
    · intro hE
      have hEJ : E ∈ J.E := harc_union ▸ Or.inl hE
      obtain ⟨p, hpE⟩ := hE.1
      have hpA : p ∈ A := hE.2.1 hpE
      rw [hA_eq, mem_iUnion] at hpA
      obtain ⟨i, hpi⟩ := hpA
      exact ⟨i, J.edge_eq_of_mem (N.e_int_mem_E hJ i) hEJ hpi hpE⟩
    · rintro ⟨i, rfl⟩
      rcases harc_union ▸ N.e_int_mem_E hJ i with hEA | hEB
      · exact hEA
      · obtain ⟨p, hp⟩ := hEB.1
        have hpA : p ∈ A := by
          rw [hA_eq, mem_iUnion]
          exact ⟨i, hp⟩
        exact False.elim (hpA.2 (hEB.2.1 hp).1)
  have hdisj_arc : Disjoint (range N.interiorSeamEdge) (arcComponentsIn B) := by
    rw [← harc_A, Set.disjoint_left]
    intro E hEA hEB
    obtain ⟨p, hp⟩ := hEA.1
    exact (hEA.2.1 hp).2 (hEB.2.1 hp).1
  exact ⟨harc_A ▸ harc_union, hdisj_arc⟩

/-- For any seam graph `J` of a net `N` on a surface `S`,
`J.E.ncard = N.r + (bd S ∩ J.V).ncard`. -/
theorem ncard_E_seamGraph (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) :
    J.E.ncard = N.r + (bd S ∩ J.V).ncard := by
  obtain ⟨hedges, hdisjoint⟩ := N.seamGraph_edges_eq hS hJ
  obtain ⟨hfin, hcount⟩ := N.ncard_arcComponentsIn_bd_sdiff hS hJ
  rw [hedges, ncard_union_eq hdisjoint (finite_range _) hfin, hcount,
    ncard_range_of_injective N.e_int_injective, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## 3. Cohomology of a net and Euler's formula ((2.2)) -/

local notation "K" => ZMod 2

/-- The vertex set `N.seamV` of a net `N` is finite. -/
theorem finite_seamV (N : Net S) : N.seamV.Finite := by
  refine (finite_iUnion fun i : Fin N.r =>
    (finite_singleton (N.φ (N.f i 1))).insert (N.φ (N.f i 0))).subset fun v hv => ?_
  rcases hv with ⟨i, h0 | h1⟩
  · exact mem_iUnion.mpr ⟨i, Or.inl h0.symm⟩
  · exact mem_iUnion.mpr ⟨i, Or.inr (mem_singleton_iff.mpr h1.symm)⟩

/-- Submodule of `N.seamV → K` consisting of functions that are constant on `C ∩ N.seamV` for each
cuff `C ∈ cuffs S`. -/
private def W_bd (N : Net S) : Submodule K (N.seamV → K) where
  carrier := {w : N.seamV → K |
    ∀ C ∈ cuffs S, ∀ x : N.seamV, x.1 ∈ C → ∀ y : N.seamV, y.1 ∈ C → w x = w y}
  add_mem' {w₁ w₂} hw₁ hw₂ C hC x hx y hy := by
    simp [hw₁ C hC x hx y hy, hw₂ C hC x hx y hy]
  zero_mem' _ _ _ _ _ _ := rfl
  smul_mem' c {w} hw C hC x hx y hy := by
    simp [hw C hC x hx y hy]

/-- The coboundary linear map `δ : N.W_bd →ₗ[K] (Fin N.r → K)` sending `w` to
`i ↦ w(φ(f_i(0))) + w(φ(f_i(1)))`. -/
private def δ (N : Net S) : N.W_bd →ₗ[K] (Fin N.r → K) where
  toFun w i :=
    w.1 ⟨N.φ (N.f i 0), i, Or.inl rfl⟩ + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩
  map_add' w₁ w₂ := by
    ext i
    change (w₁.1 _ + w₂.1 _) + (w₁.1 _ + w₂.1 _) = (w₁.1 _ + w₁.1 _) + (w₂.1 _ + w₂.1 _)
    ring
  map_smul' c w := by
    ext i
    change c * w.1 _ + c * w.1 _ = c * (w.1 _ + w.1 _)
    ring

/-- Helper constructing the cuff containing a boundary point `x ∈ bd S`. -/
private noncomputable def cuffOf {x : S} (hx : x ∈ bd S) : cuffs S :=
  ⟨connectedComponentIn (bd S) x, x, hx, rfl⟩

private theorem cuffOf_eq {C : cuffs S} {x : S} (hx : x ∈ C.1) (hxbd : x ∈ bd S) :
    cuffOf hxbd = C := by
  apply Subtype.ext
  obtain ⟨z, _, hC⟩ := C.2
  change connectedComponentIn (bd S) x = C.1
  rw [← hC] at hx ⊢
  exact (connectedComponentIn_eq hx).symm

/-- The dimension of `N.W_bd` satisfies
`Module.finrank K N.W_bd + (bd S ∩ N.seamV).ncard = N.seamV.ncard + (cuffs S).ncard`. -/
private theorem finrank_W_bd (hS : IsSurface S) (N : Net S) (hpos : 0 < N.r) :
    Module.finrank K N.W_bd + (bd S ∩ N.seamV).ncard =
      N.seamV.ncard + (cuffs S).ncard := by
  classical
  have : T2Space S := hS.2.1
  have hfin_V : N.seamV.Finite := N.finite_seamV
  have hfin_cuffs : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hfin_int : (N.seamV \ bd S).Finite := hfin_V.sdiff
  have hfin_bd : (bd S ∩ N.seamV).Finite := hfin_V.subset inter_subset_right
  let _ : Fintype N.seamV := hfin_V.fintype
  let _ : Fintype ↑(N.seamV \ bd S) := hfin_int.fintype
  let _ : Fintype ↑(cuffs S) := hfin_cuffs.fintype
  have hne_cuff : ∀ C : cuffs S, ∃ v : N.seamV, v.1 ∈ C.1 := by
    intro C
    obtain ⟨x, hxC, hxV⟩ := N.cuff_inter_seamV_nonempty hS hpos C.2
    exact ⟨⟨x, hxV⟩, hxC⟩
  choose v_C hv_C using hne_cuff
  let toFun : N.W_bd → (↑(N.seamV \ bd S) → K) × (↑(cuffs S) → K) := fun w =>
    (fun x => w.1 ⟨x.1, x.2.1⟩, fun C => w.1 (v_C C))
  let invFun : (↑(N.seamV \ bd S) → K) × (↑(cuffs S) → K) → N.W_bd := fun p =>
    ⟨fun x =>
      if hx : x.1 ∈ bd S then
        p.2 (cuffOf hx)
      else
        p.1 ⟨x.1, x.2, hx⟩,
      by
        intro C hC x hxC y hyC
        have hxbd : x.1 ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨C, hC, hxC⟩
        have hybd : y.1 ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨C, hC, hyC⟩
        simp only [hxbd, hybd, ↓reduceDIte]
        rw [cuffOf_eq (C := ⟨C, hC⟩) hxC hxbd, cuffOf_eq (C := ⟨C, hC⟩) hyC hybd]⟩
  let e : N.W_bd ≃ₗ[K] ((↑(N.seamV \ bd S) → K) × (↑(cuffs S) → K)) :=
    { toFun := toFun
      invFun := invFun
      map_add' := fun w₁ w₂ => by
        ext x <;> rfl
      map_smul' := fun c w => by
        ext x <;> rfl
      left_inv := fun w => by
        ext x
        dsimp only [toFun, invFun]
        split_ifs with hxbd
        · have hxC : x.1 ∈ (cuffOf hxbd).1 := mem_connectedComponentIn hxbd
          exact w.2 (cuffOf hxbd).1 (cuffOf hxbd).2 (v_C (cuffOf hxbd)) (hv_C (cuffOf hxbd)) x hxC
        · rfl
      right_inv := fun p => by
        ext x
        · dsimp only [toFun, invFun]
          have hnot : ¬ (x.1 : S) ∈ bd S := x.2.2
          simp only [hnot, ↓reduceDIte]
        · dsimp only [toFun, invFun]
          have hbd : (v_C x).1 ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨x.1, x.2, hv_C x⟩
          simp only [hbd, ↓reduceDIte]
          rw [cuffOf_eq (hv_C x) hbd] }
  have hfinrank : Module.finrank K N.W_bd =
      (N.seamV \ bd S).ncard + (cuffs S).ncard := by
    rw [LinearEquiv.finrank_eq e, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  have hpart : (N.seamV \ bd S).ncard + (bd S ∩ N.seamV).ncard = N.seamV.ncard := by
    have hunion : (N.seamV \ bd S) ∪ (bd S ∩ N.seamV) = N.seamV := by
      ext x
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff]
      tauto
    have hdisj : Disjoint (N.seamV \ bd S) (bd S ∩ N.seamV) := by
      rw [Set.disjoint_left]
      exact fun _ hx hy => hx.2 hy.1
    rw [← ncard_union_eq hdisj hfin_int hfin_bd, hunion]
  omega

/-- Key connectedness lemma on `bd N.D`: if `d : N.D → K` and `w ∈ N.W_bd` satisfy:
1. `d (N.f i 0) + d (N.f i 1) = N.δ w i` and `d (N.g i 0) + d (N.g i 1) = N.δ w i` for all `i`,
2. `d` is locally constant on `bd N.D ∩ N.φ ⁻¹' (bd S)`,
then `x ↦ d x + w.1 ⟨N.φ x, hx⟩` is constant on `N.φ ⁻¹' N.seamV`. -/
private theorem bd_D_const_of_cuff_and_seam (hS : IsSurface S) (N : Net S) (hpos : 0 < N.r)
    (d : N.D → K) (w : N.W_bd)
    (hdf : ∀ i : Fin N.r, d (N.f i 0) + d (N.f i 1) = N.δ w i)
    (hdg : ∀ i : Fin N.r, d (N.g i 0) + d (N.g i 1) = N.δ w i)
    (hloc : ∀ p ∈ bd N.D ∩ N.φ ⁻¹' (bd S),
      ∃ W ∈ 𝓝 p, ∀ x ∈ W ∩ (bd N.D ∩ N.φ ⁻¹' (bd S)), d x = d p)
    {x z : N.D} (hx : N.φ x ∈ N.seamV) (hz : N.φ z ∈ N.seamV) :
    d x + w.1 ⟨N.φ x, hx⟩ = d z + w.1 ⟨N.φ z, hz⟩ := by
  classical
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have : T2Space S := hS.2.1
  have hne_cuff : ∀ C : cuffs S, ∃ v : N.seamV, v.1 ∈ C.1 := by
    intro C
    obtain ⟨y, hyC, hyV⟩ := N.cuff_inter_seamV_nonempty hS hpos C.2
    exact ⟨⟨y, hyV⟩, hyC⟩
  choose v_C hv_C using hne_cuff
  let val_f (i : Fin N.r) : K := d (N.f i 0) + w.1 ⟨N.φ (N.f i 0), i, Or.inl rfl⟩
  let val_g (i : Fin N.r) : K := d (N.g i 0) + w.1 ⟨N.φ (N.g i 0), i, Or.inl (N.φ_f_eq_φ_g i 0)⟩
  have hval_f1 : ∀ i : Fin N.r,
      d (N.f i 1) + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩ = val_f i := by
    intro i
    have h1 := hdf i
    change d (N.f i 0) + d (N.f i 1) =
      w.1 ⟨N.φ (N.f i 0), i, Or.inl rfl⟩ + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩ at h1
    have h2 : (d (N.f i 1) + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩) + val_f i =
        (d (N.f i 0) + d (N.f i 1)) +
          (w.1 ⟨N.φ (N.f i 0), i, Or.inl rfl⟩ + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩) := by
      dsimp [val_f]; ring
    refine CharTwo.add_eq_zero.mp ?_
    rw [h2, h1, CharTwo.add_self_eq_zero]
  have hval_g1 : ∀ i : Fin N.r,
      d (N.g i 1) + w.1 ⟨N.φ (N.g i 1), i, Or.inr (N.φ_f_eq_φ_g i 1)⟩ = val_g i := by
    intro i
    have h1 := hdg i
    change d (N.g i 0) + d (N.g i 1) =
      w.1 ⟨N.φ (N.f i 0), i, Or.inl rfl⟩ + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩ at h1
    have hw0 : (⟨N.φ (N.g i 0), i, Or.inl (N.φ_f_eq_φ_g i 0)⟩ : N.seamV) =
        ⟨N.φ (N.f i 0), i, Or.inl rfl⟩ := Subtype.ext (N.φ_f_eq_φ_g i 0).symm
    have hw1 : (⟨N.φ (N.g i 1), i, Or.inr (N.φ_f_eq_φ_g i 1)⟩ : N.seamV) =
        ⟨N.φ (N.f i 1), i, Or.inr rfl⟩ := Subtype.ext (N.φ_f_eq_φ_g i 1).symm
    rw [hw1]
    have h2 : (d (N.g i 1) + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩) + val_g i =
        (d (N.g i 0) + d (N.g i 1)) +
          (w.1 ⟨N.φ (N.f i 0), i, Or.inl rfl⟩ + w.1 ⟨N.φ (N.f i 1), i, Or.inr rfl⟩) := by
      dsimp [val_g]; rw [hw0]; ring
    refine CharTwo.add_eq_zero.mp ?_
    rw [h2, h1, CharTwo.add_self_eq_zero]
  let u : N.D → K := fun y =>
    if hyV : N.φ y ∈ N.seamV then
      d y + w.1 ⟨N.φ y, hyV⟩
    else if hyf : ∃ i : Fin N.r, y ∈ range (N.f i) then
      val_f hyf.choose
    else if hyg : ∃ i : Fin N.r, y ∈ range (N.g i) then
      val_g hyg.choose
    else if hybd : N.φ y ∈ bd S then
      d y + w.1 (v_C (cuffOf hybd))
    else 0
  have hu_f : ∀ (i : Fin N.r) (t : unitInterval), u (N.f i t) = val_f i := by
    intro i t
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · have hV : N.φ (N.f i 0) ∈ N.seamV := ⟨i, Or.inl rfl⟩
      simp only [u, hV, ↓reduceDIte, val_f]
    · have hV : N.φ (N.f i 1) ∈ N.seamV := ⟨i, Or.inr rfl⟩
      simp only [u, hV, ↓reduceDIte]
      exact hval_f1 i
    · have hnV : N.φ (N.f i t) ∉ N.seamV := N.notMem_seamV_of_mem_Ioo i ht
      have hrf : ∃ j : Fin N.r, N.f i t ∈ range (N.f j) := ⟨i, t, rfl⟩
      simp only [u, hnV, hrf, ↓reduceDIte]
      obtain ⟨s, hs⟩ := hrf.choose_spec
      by_contra hne
      have hij : i ≠ hrf.choose := fun h => hne (h ▸ rfl)
      exact N.internally_disjoint_ff i hrf.choose hij t ht ⟨s, hs⟩
  have hu_g : ∀ (i : Fin N.r) (t : unitInterval), u (N.g i t) = val_g i := by
    intro i t
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · have hV : N.φ (N.g i 0) ∈ N.seamV := ⟨i, Or.inl (N.φ_f_eq_φ_g i 0)⟩
      simp only [u, hV, ↓reduceDIte, val_g]
    · have hV : N.φ (N.g i 1) ∈ N.seamV := ⟨i, Or.inr (N.φ_f_eq_φ_g i 1)⟩
      simp only [u, hV, ↓reduceDIte]
      exact hval_g1 i
    · have hnV : N.φ (N.g i t) ∉ N.seamV := by
        rw [← N.φ_f_eq_φ_g i t]
        exact N.notMem_seamV_of_mem_Ioo i ht
      have hnf : ¬ ∃ j : Fin N.r, N.g i t ∈ range (N.f j) := by
        rintro ⟨j, s, hs⟩
        exact N.internally_disjoint_gf i j t ht ⟨s, hs⟩
      have hrg : ∃ j : Fin N.r, N.g i t ∈ range (N.g j) := ⟨i, t, rfl⟩
      simp only [u, hnV, hnf, hrg, ↓reduceDIte]
      obtain ⟨s, hs⟩ := hrg.choose_spec
      by_contra hne
      have hij : i ≠ hrg.choose := fun h => hne (h ▸ rfl)
      exact N.internally_disjoint_gg i hrg.choose hij t ht ⟨s, hs⟩
  have hu_cuff : ∀ (C : cuffs S) (y : N.D), y ∈ bd N.D ∩ N.φ ⁻¹' C.1 →
      u y = d y + w.1 (v_C C) := by
    intro C y ⟨hybd_D, hyC⟩
    have hybdS : N.φ y ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨C.1, C.2, hyC⟩
    by_cases hyV : N.φ y ∈ N.seamV
    · simp only [u, hyV, ↓reduceDIte]
      rw [w.2 C.1 C.2 ⟨N.φ y, hyV⟩ hyC (v_C C) (hv_C C)]
    · have hnf : ¬ ∃ i : Fin N.r, y ∈ range (N.f i) := by
        rintro ⟨i, t, rfl⟩
        rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact hyV ⟨i, Or.inl rfl⟩
        · exact hyV ⟨i, Or.inr rfl⟩
        · exact N.notMem_bd_of_mem_Ioo hS i ht hybdS
      have hng : ¬ ∃ i : Fin N.r, y ∈ range (N.g i) := by
        rintro ⟨i, t, rfl⟩
        have hyV' : N.φ (N.f i t) ∉ N.seamV := by rwa [N.φ_f_eq_φ_g i t]
        have hybdS' : N.φ (N.f i t) ∈ bd S := by rwa [N.φ_f_eq_φ_g i t]
        rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
        · exact hyV' ⟨i, Or.inl rfl⟩
        · exact hyV' ⟨i, Or.inr rfl⟩
        · exact N.notMem_bd_of_mem_Ioo hS i ht hybdS'
      simp only [u, hyV, hnf, hng, hybdS, ↓reduceDIte]
      rw [cuffOf_eq hyC hybdS]
  have hu_loc : ∀ p ∈ bd N.D, ∃ W ∈ 𝓝 p, ∀ y ∈ W ∩ bd N.D, u y = u p := by
    intro p hp
    let F_f : Set N.D := ⋃ (i : Fin N.r) (_ : p ∉ range (N.f i)), range (N.f i)
    let F_g : Set N.D := ⋃ (i : Fin N.r) (_ : p ∉ range (N.g i)), range (N.g i)
    let F_c : Set N.D :=
      ⋃ (C ∈ cuffs S) (_ : p ∉ bd N.D ∩ N.φ ⁻¹' C), (bd N.D ∩ N.φ ⁻¹' C)
    have hFf_cl : IsClosed F_f :=
      isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ =>
        (isCompact_range (N.f i).continuous).isClosed
    have hFg_cl : IsClosed F_g :=
      isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ =>
        (isCompact_range (N.g i).continuous).isClosed
    have hFc_cl : IsClosed F_c := by
      refine (cuff_statement S hS).2.1.isClosed_biUnion fun C hC =>
        isClosed_iUnion_of_finite fun _ => (isClosed_bd N.D).inter ?_
      exact (isClosed_of_mem_cuffs hS hC).preimage N.quotientMap_φ.continuous
    have hp_not_F : p ∈ (F_f ∪ F_g ∪ F_c)ᶜ := by
      rintro ((h | h) | h)
      · obtain ⟨i, hni, hi⟩ := mem_iUnion₂.mp h
        exact hni hi
      · obtain ⟨i, hni, hi⟩ := mem_iUnion₂.mp h
        exact hni hi
      · obtain ⟨C, _, h⟩ := mem_iUnion₂.mp h
        obtain ⟨hni, hi⟩ := mem_iUnion.mp h
        exact hni hi
    have hW₁_mem : (F_f ∪ F_g ∪ F_c)ᶜ ∈ 𝓝 p :=
      ((hFf_cl.union hFg_cl).union hFc_cl).isOpen_compl.mem_nhds hp_not_F
    have hW₂_mem : ∃ W₂ ∈ 𝓝 p, p ∈ bd N.D ∩ N.φ ⁻¹' (bd S) →
        ∀ y ∈ W₂ ∩ (bd N.D ∩ N.φ ⁻¹' (bd S)), d y = d p := by
      by_cases hp_bd : p ∈ bd N.D ∩ N.φ ⁻¹' (bd S)
      · obtain ⟨W₂, hW₂, h2⟩ := hloc p hp_bd
        exact ⟨W₂, hW₂, fun _ => h2⟩
      · exact ⟨univ, univ_mem, fun h => False.elim (hp_bd h)⟩
    obtain ⟨W₂, hW₂, hW₂_eq⟩ := hW₂_mem
    refine ⟨(F_f ∪ F_g ∪ F_c)ᶜ ∩ W₂, Filter.inter_mem hW₁_mem hW₂, fun y ⟨⟨hyF, hyW₂⟩, hybd⟩ => ?_⟩
    by_cases hybdS : N.φ y ∈ bd S
    · obtain ⟨C, hC, hyC⟩ := sUnion_cuffs (S := S) ▸ hybdS
      have hpC : p ∈ bd N.D ∩ N.φ ⁻¹' C := by
        by_contra hnp
        exact hyF (Or.inr (mem_iUnion₂.mpr ⟨C, hC, mem_iUnion.mpr ⟨hnp, hybd, hyC⟩⟩))
      have hpbdS : N.φ p ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨C, hC, hpC.2⟩
      rw [hu_cuff ⟨C, hC⟩ y ⟨hybd, hyC⟩, hu_cuff ⟨C, hC⟩ p hpC,
        hW₂_eq ⟨hp, hpbdS⟩ y ⟨hyW₂, hybd, hybdS⟩]
    · have hy_fg : ∃ i : Fin N.r, y ∈ range (N.f i) ∨ y ∈ range (N.g i) := by
        by_cases hyV : N.φ y ∈ N.seamV
        · obtain ⟨i, hi⟩ := mem_iUnion.mp (N.preimage_seamV_subset_endpoints hyV)
          simp only [mem_insert_iff, mem_singleton_iff] at hi
          rcases hi with rfl | rfl | rfl | rfl
          · exact ⟨i, Or.inl ⟨0, rfl⟩⟩
          · exact ⟨i, Or.inl ⟨1, rfl⟩⟩
          · exact ⟨i, Or.inr ⟨0, rfl⟩⟩
          · exact ⟨i, Or.inr ⟨1, rfl⟩⟩
        · obtain ⟨i, w', _, _, hfib, -⟩ :=
            N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hybd hybdS hyV
          have hy_mem : y ∈ N.φ ⁻¹' {N.φ y} := rfl
          rw [hfib, mem_insert_iff, mem_singleton_iff] at hy_mem
          rcases hy_mem with rfl | rfl
          · exact ⟨i, Or.inl ⟨w', rfl⟩⟩
          · exact ⟨i, Or.inr ⟨w', rfl⟩⟩
      rcases hy_fg with ⟨i, ⟨t, rfl⟩ | ⟨t, rfl⟩⟩
      · have hpf : p ∈ range (N.f i) := by
          by_contra hnp
          exact hyF (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨i, hnp, t, rfl⟩)))
        rcases hpf with ⟨s, rfl⟩
        rw [hu_f i t, hu_f i s]
      · have hpg : p ∈ range (N.g i) := by
          by_contra hnp
          exact hyF (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨i, hnp, t, rfl⟩)))
        rcases hpg with ⟨s, rfl⟩
        rw [hu_g i t, hu_g i s]
  have hxbd : x ∈ bd N.D := by
    rw [← N.preimage_seamU]
    rcases hx with ⟨i, h0 | h1⟩
    · exact ⟨N.f i 0, N.range_f_subset_bd i ⟨0, rfl⟩, h0⟩
    · exact ⟨N.f i 1, N.range_f_subset_bd i ⟨1, rfl⟩, h1⟩
  have hzbd : z ∈ bd N.D := by
    rw [← N.preimage_seamU]
    rcases hz with ⟨i, h0 | h1⟩
    · exact ⟨N.f i 0, N.range_f_subset_bd i ⟨0, rfl⟩, h0⟩
    · exact ⟨N.f i 1, N.range_f_subset_bd i ⟨1, rfl⟩, h1⟩
  have heq := const_of_locally N.isOArc_bd_D.isPreconnected hu_loc hxbd hzbd
  simpa only [u, hx, hz, ↓reduceDIte] using heq

/-- The rank of `N.δ` satisfies `Module.finrank K (LinearMap.range N.δ) + 1 = Module.finrank K
N.W_bd`. -/
private theorem finrank_range_δ (hS : IsSurface S) (N : Net S) (hpos : 0 < N.r) :
    Module.finrank K (LinearMap.range N.δ) + 1 = Module.finrank K N.W_bd := by
  have : T2Space S := hS.2.1
  have hfin_V : N.seamV.Finite := N.finite_seamV
  let _ : Fintype N.seamV := hfin_V.fintype
  let _ : FiniteDimensional K N.W_bd := inferInstance
  have h1 := LinearMap.finrank_range_add_finrank_ker N.δ
  rw [← h1]
  congr 1
  let one_W : N.W_bd := ⟨fun _ => 1, fun _ _ _ _ _ _ => rfl⟩
  have hone_ker : one_W ∈ LinearMap.ker N.δ := by
    rw [LinearMap.mem_ker]
    ext i
    exact CharTwo.add_self_eq_zero 1
  have hker_eq : LinearMap.ker N.δ = Submodule.span K {one_W} := by
    refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr hone_ker)
    rw [LinearMap.mem_ker] at hw
    let v₀ : N.seamV := ⟨N.φ (N.f ⟨0, hpos⟩ 0), ⟨0, hpos⟩, Or.inl rfl⟩
    refine Submodule.mem_span_singleton.mpr ⟨w.1 v₀, ?_⟩
    ext v
    change w.1 v₀ * 1 = w.1 v
    rw [mul_one]
    obtain ⟨x, hx⟩ := N.quotientMap_φ.surjective v.1
    have hxV : N.φ x ∈ N.seamV := hx.symm ▸ v.2
    have hconst := N.bd_D_const_of_cuff_and_seam hS hpos 0 w
      (fun i => by simp [congr_fun hw i])
      (fun i => by simp [congr_fun hw i])
      (fun p _ => ⟨univ, univ_mem, fun _ _ => rfl⟩)
      (⟨⟨0, hpos⟩, Or.inl rfl⟩ : N.φ (N.f ⟨0, hpos⟩ 0) ∈ N.seamV) hxV
    simp only [Pi.zero_apply, zero_add] at hconst
    have hv_eq : (⟨N.φ x, hxV⟩ : N.seamV) = v := Subtype.ext hx
    rwa [hv_eq] at hconst
  rw [hker_eq]
  refine (finrank_span_singleton ?_).symm
  intro h0
  let v₀ : N.seamV := ⟨N.φ (N.f ⟨0, hpos⟩ 0), ⟨0, hpos⟩, Or.inl rfl⟩
  have : (1 : K) = 0 := congr_fun (congr_arg Subtype.val h0) v₀
  exact one_ne_zero this

/-- If a local cocycle `ψ : S → S → K` has a primitive `d : N.D → K` of `pbk N.φ ψ` on `univ : Set
N.D`
that satisfies `d (N.f i t) = d (N.g i t)` for all `i, t`, then `CohRel ψ 0`. -/
private theorem cohRel_of_prim_fib [T2Space S] (N : Net S) {ψ : S → S → K} (hψ : IsCoc ψ)
    {d : N.D → K} (hd : Prim (pbk N.φ ψ) univ d)
    (hfg : ∀ (i : Fin N.r) (t : unitInterval), d (N.f i t) = d (N.g i t)) :
    CohRel ψ 0 := by
  have : CompactSpace N.D := N.isSurface_D.1
  let R : N.D → N.D → Prop := fun a b =>
    ∃ (j : Fin N.r) (s : unitInterval), a = N.f j s ∧ b = N.g j s
  have hrel_eq : ∀ x y : N.D, Relation.EqvGen R x y → d x = d y := by
    intro x y hrel
    induction hrel with
    | rel a b hab =>
      rcases hab with ⟨i, t, rfl, rfl⟩
      exact hfg i t
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  have hfib : ∀ x y : N.D, N.φ x = N.φ y → d x = d y :=
    fun x y hxy => hrel_eq x y ((N.bd_eq_iff x y).mp hxy)
  choose r hr using N.quotientMap_φ.surjective
  let h : S → K := fun p => d (r p)
  have hφ : ∀ x : N.D, h (N.φ x) = d x := fun x => hfib (r (N.φ x)) x (hr (N.φ x))
  have hex_W : ∀ z : N.D, ∃ W : Set N.D, IsOpen W ∧ z ∈ W ∧
      ∀ a ∈ W, ∀ b ∈ W, ψ (N.φ a) (N.φ b) = d a + d b := by
    intro z
    obtain ⟨W₀, hW₀, h1⟩ := hd z (mem_univ z)
    obtain ⟨W, hW_sub, hW_open, hzW⟩ := mem_nhds_iff.mp hW₀
    exact ⟨W, hW_open, hzW, fun a ha b hb => h1 a ⟨hW_sub ha, trivial⟩ b ⟨hW_sub hb, trivial⟩⟩
  choose W hW_open hzW hW_eq using hex_W
  obtain ⟨N_coc, hN_coc, hcoc⟩ := hψ
  have hφ_closed : IsClosedMap N.φ := N.quotientMap_φ.continuous.isClosedMap
  have hex_V : ∀ p : S, ∃ V : Set S, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V, ∀ y ∈ V, ψ x y = h y - h x := by
    intro p
    let U_p : Set N.D := ⋃ z ∈ N.φ ⁻¹' {p}, W z
    have hUp_open : IsOpen U_p := isOpen_biUnion fun z _ => hW_open z
    let V₁ : Set S := (N.φ '' U_pᶜ)ᶜ
    have hV₁_open : IsOpen V₁ := (hφ_closed _ hUp_open.isClosed_compl).isOpen_compl
    have hpV₁ : p ∈ V₁ := by
      rintro ⟨z, hz, rfl⟩
      exact hz (mem_iUnion₂.mpr ⟨z, rfl, hzW z⟩)
    obtain ⟨u₁, hu₁, u₂, hu₂, hu_sub⟩ := mem_nhds_prod_iff.mp (hN_coc p)
    obtain ⟨V₂, hV₂_sub, hV₂_open, hpV₂⟩ := mem_nhds_iff.mp (Filter.inter_mem hu₁ hu₂)
    refine ⟨V₁ ∩ V₂, hV₁_open.inter hV₂_open, ⟨hpV₁, hpV₂⟩, fun x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ => ?_⟩
    have hxp : ψ x p = h x + h p := by
      obtain ⟨a, rfl⟩ := N.quotientMap_φ.surjective x
      have haU : a ∈ U_p := by
        by_contra hna
        exact hx₁ ⟨a, hna, rfl⟩
      obtain ⟨z, hz, haW⟩ := mem_iUnion₂.mp haU
      have hpz : N.φ z = p := hz
      rw [← hpz, hW_eq z a haW z (hzW z), hφ a, hφ z]
    have hpy : ψ p y = h p + h y := by
      obtain ⟨b, rfl⟩ := N.quotientMap_φ.surjective y
      have hbU : b ∈ U_p := by
        by_contra hnb
        exact hy₁ ⟨b, hnb, rfl⟩
      obtain ⟨z, hz, hbW⟩ := mem_iUnion₂.mp hbU
      have hpz : N.φ z = p := hz
      rw [← hpz, hW_eq z z (hzW z) b hbW, hφ z, hφ b]
    have hxy_coc := hcoc x p y
      (hu_sub ⟨(hV₂_sub hx₂).1, (hV₂_sub hpV₂).2⟩)
      (hu_sub ⟨(hV₂_sub hpV₂).1, (hV₂_sub hy₂).2⟩)
      (hu_sub ⟨(hV₂_sub hx₂).1, (hV₂_sub hy₂).2⟩)
    rw [← hxy_coc, hxp, hpy, CharTwo.sub_eq_add]
    have hring : (h x + h p) + (h p + h y) = (h p + h p) + (h y + h x) := by ring
    rw [hring, CharTwo.add_self_eq_zero, zero_add]
  choose V hV_open hpV hV_eq using hex_V
  refine ⟨h, ⋃ p : S, V p ×ˢ V p, ?_, ?_⟩
  · intro p
    exact Filter.mem_of_superset ((hV_open p).prod (hV_open p) |>.mem_nhds ⟨hpV p, hpV p⟩)
      (subset_iUnion (fun q => V q ×ˢ V q) p)
  · rintro x y hxy
    obtain ⟨p, hxV, hyV⟩ := mem_iUnion.mp hxy
    simpa using hV_eq p x hxV y hyV

/-- Along any seam `i : Fin N.r`, a primitive `g` of `pbk N.φ ψ` on `univ : Set N.D` has constant
jump `g (N.f i t) + g (N.g i t) = g (N.f i 0) + g (N.g i 0)` for all `t : unitInterval`, and in
particular `g (N.f i 0) + g (N.f i 1) = g (N.g i 0) + g (N.g i 1)`. -/
private theorem prim_seam_jump_const (N : Net S) {ψ : S → S → K} {g : N.D → K}
    (hg : Prim (pbk N.φ ψ) univ g) (i : Fin N.r) :
    (∀ t : unitInterval, g (N.f i t) + g (N.g i t) = g (N.f i 0) + g (N.g i 0)) ∧
      g (N.f i 0) + g (N.f i 1) = g (N.g i 0) + g (N.g i 1) := by
  have hpf : Prim (pbk (N.φ ∘ N.f i) ψ) univ (g ∘ N.f i) := by
    intro t _
    obtain ⟨W, hW, h1⟩ := hg (N.f i t) (mem_univ _)
    refine ⟨N.f i ⁻¹' W, (N.f i).continuous.continuousAt.preimage_mem_nhds hW,
      fun s hs s' hs' => h1 (N.f i s) ⟨hs.1, trivial⟩ (N.f i s') ⟨hs'.1, trivial⟩⟩
  have hpg : Prim (pbk (N.φ ∘ N.f i) ψ) univ (g ∘ N.g i) := by
    intro t _
    obtain ⟨W, hW, h1⟩ := hg (N.g i t) (mem_univ _)
    refine ⟨N.g i ⁻¹' W, (N.g i).continuous.continuousAt.preimage_mem_nhds hW,
      fun s hs s' hs' => ?_⟩
    change ψ (N.φ (N.f i s)) (N.φ (N.f i s')) = g (N.g i s) + g (N.g i s')
    rw [N.φ_f_eq_φ_g i s, N.φ_f_eq_φ_g i s']
    exact h1 (N.g i s) ⟨hs.1, trivial⟩ (N.g i s') ⟨hs'.1, trivial⟩
  have hconst : ∀ t : unitInterval, g (N.f i t) + g (N.g i t) = g (N.f i 0) + g (N.g i 0) :=
    fun t => hpf.const hpg isPreconnected_univ Subset.rfl Subset.rfl trivial trivial
  refine ⟨hconst, ?_⟩
  have h1 := hconst 1
  have h2 : (g (N.f i 0) + g (N.f i 1)) + (g (N.g i 0) + g (N.g i 1)) =
      (g (N.f i 0) + g (N.g i 0)) + (g (N.f i 1) + g (N.g i 1)) := by ring
  refine CharTwo.add_eq_zero.mp ?_
  rw [h2, h1, CharTwo.add_self_eq_zero]

/-- Two local cocycles `φ, φ'` that vanish near the diagonal of `bd S` with primitives `g, g'` on
`univ : Set N.D` satisfy `CohRel φ φ'` if and only if their seam voltage difference
`i ↦ (g (N.f i 0) + g (N.f i 1)) + (g' (N.f i 0) + g' (N.f i 1))` lies in `LinearMap.range N.δ`. -/
private theorem cohRel_iff_mem_range_δ (hS : IsSurface S) (N : Net S) (hpos : 0 < N.r)
    {φ φ' : S → S → K} (hφ : IsCoc φ) (hφ' : IsCoc φ')
    {N_bd N'_bd : Set (S × S)} (hN_bd : NearDiag N_bd) (hN'_bd : NearDiag N'_bd)
    (hbd : ∀ x ∈ bd S, ∀ y ∈ bd S, (x, y) ∈ N_bd → φ x y = 0)
    (hbd' : ∀ x ∈ bd S, ∀ y ∈ bd S, (x, y) ∈ N'_bd → φ' x y = 0)
    {g g' : N.D → K} (hg : Prim (pbk N.φ φ) univ g) (hg' : Prim (pbk N.φ φ') univ g') :
    CohRel φ φ' ↔
      (fun i : Fin N.r => (g (N.f i 0) + g (N.f i 1)) + (g' (N.f i 0) + g' (N.f i 1))) ∈
        LinearMap.range N.δ := by
  have : T2Space S := hS.2.1
  constructor
  · rintro ⟨k, N_rel, hN_rel, hrel⟩
    have hk_cuff : ∀ C ∈ cuffs S, ∀ x : N.seamV, x.1 ∈ C → ∀ y : N.seamV, y.1 ∈ C →
        k x.1 = k y.1 := by
      intro C hC x hxC y hyC
      have hC_sub : C ⊆ bd S := by
        obtain ⟨z, hz, rfl⟩ := hC
        exact connectedComponentIn_subset _ _
      refine const_of_locally ((cuff_statement S hS).2.2 C hC).isPreconnected
        (u := k) (fun p hp => ?_) hxC hyC
      have hM : NearDiag (N_rel ∩ N_bd ∩ N'_bd) := (hN_rel.inter hN_bd).inter hN'_bd
      have hMp : (fun q => (p, q)) ⁻¹' (N_rel ∩ N_bd ∩ N'_bd) ∈ 𝓝 p :=
        (Continuous.prodMk_right p).continuousAt.preimage_mem_nhds (hM p)
      refine ⟨_, hMp, fun q ⟨⟨⟨hq_rel, hq_bd⟩, hq_bd'⟩, hqC⟩ => ?_⟩
      have hp_bd : p ∈ bd S := hC_sub hp
      have hq_bdS : q ∈ bd S := hC_sub hqC
      have hr := hrel p q hq_rel
      rw [hbd p hp_bd q hq_bdS hq_bd, hbd' p hp_bd q hq_bdS hq_bd', sub_zero,
        CharTwo.sub_eq_add] at hr
      exact CharTwo.add_eq_zero.mp hr.symm
    let w : N.W_bd := ⟨fun v => k v.1, hk_cuff⟩
    refine ⟨w, ?_⟩
    ext i
    have hc := const_of_locally (isPreconnected_range (N.f i).continuous)
      (u := fun x => g x + g' x + k (N.φ x)) (fun p _ => by
        obtain ⟨W, hW, h1⟩ := hg p trivial
        obtain ⟨W', hW', h2⟩ := hg' p trivial
        have hNp : (fun x => (N.φ p, N.φ x)) ⁻¹' N_rel ∈ 𝓝 p :=
          (Continuous.prodMk_right (N.φ p) |>.comp
            N.quotientMap_φ.continuous).continuousAt.preimage_mem_nhds
            (hN_rel (N.φ p))
        refine ⟨W ∩ W' ∩ _, Filter.inter_mem (Filter.inter_mem hW hW') hNp, fun x hx => ?_⟩
        have h3 := h1 p ⟨mem_of_mem_nhds hW, trivial⟩ x ⟨hx.1.1.1, trivial⟩
        have h4 := h2 p ⟨mem_of_mem_nhds hW', trivial⟩ x ⟨hx.1.1.2, trivial⟩
        have h5 := hrel (N.φ p) (N.φ x) hx.1.2
        change φ (N.φ p) (N.φ x) = g p + g x at h3
        change φ' (N.φ p) (N.φ x) = g' p + g' x at h4
        rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, h3, h4] at h5
        have h6 : (g x + g' x + k (N.φ x)) + (g p + g' p + k (N.φ p)) =
            (g p + g x + (g' p + g' x)) + (k (N.φ x) + k (N.φ p)) := by ring
        refine CharTwo.add_eq_zero.mp ?_
        rw [h6, h5, CharTwo.add_self_eq_zero]) ⟨0, rfl⟩ ⟨1, rfl⟩
    change k (N.φ (N.f i 0)) + k (N.φ (N.f i 1)) =
      (g (N.f i 0) + g (N.f i 1)) + (g' (N.f i 0) + g' (N.f i 1))
    have h7 : ((g (N.f i 0) + g (N.f i 1)) + (g' (N.f i 0) + g' (N.f i 1))) +
        (k (N.φ (N.f i 0)) + k (N.φ (N.f i 1))) =
        (g (N.f i 0) + g' (N.f i 0) + k (N.φ (N.f i 0))) +
          (g (N.f i 1) + g' (N.f i 1) + k (N.φ (N.f i 1))) := by ring
    refine (CharTwo.add_eq_zero.mp ?_).symm
    rw [h7, hc, CharTwo.add_self_eq_zero]
  · rintro ⟨w, hw⟩
    let ψ : S → S → K := fun x y => φ x y + φ' x y
    let d : N.D → K := fun x => g x + g' x
    have hψ_coc : IsCoc ψ := by
      obtain ⟨N₁, hN₁, hc₁⟩ := hφ
      obtain ⟨N₂, hN₂, hc₂⟩ := hφ'
      refine ⟨N₁ ∩ N₂, hN₁.inter hN₂, fun x y z hxy hyz hxz => ?_⟩
      change (φ x y + φ' x y) + (φ y z + φ' y z) = φ x z + φ' x z
      rw [← hc₁ x y z hxy.1 hyz.1 hxz.1, ← hc₂ x y z hxy.2 hyz.2 hxz.2]
      ring
    have hd_prim : Prim (pbk N.φ ψ) univ d := by
      intro p _
      obtain ⟨W, hW, h1⟩ := hg p trivial
      obtain ⟨W', hW', h2⟩ := hg' p trivial
      refine ⟨W ∩ W', Filter.inter_mem hW hW', fun a ha b hb => ?_⟩
      change pbk N.φ φ a b + pbk N.φ φ' a b = (g a + g' a) + (g b + g' b)
      rw [h1 a ⟨ha.1.1, trivial⟩ b ⟨hb.1.1, trivial⟩,
        h2 a ⟨ha.1.2, trivial⟩ b ⟨hb.1.2, trivial⟩]
      ring
    have hdf : ∀ i : Fin N.r, d (N.f i 0) + d (N.f i 1) = N.δ w i := by
      intro i
      have hi := (congr_fun hw i).symm
      change d (N.f i 0) + d (N.f i 1) = N.δ w i
      calc
        d (N.f i 0) + d (N.f i 1)
          = (g (N.f i 0) + g (N.f i 1)) + (g' (N.f i 0) + g' (N.f i 1)) := by
            dsimp [d]; ring
        _ = N.δ w i := hi
    have hdg : ∀ i : Fin N.r, d (N.g i 0) + d (N.g i 1) = N.δ w i := by
      intro i
      have h1 := (N.prim_seam_jump_const hg i).2
      have h2 := (N.prim_seam_jump_const hg' i).2
      calc
        d (N.g i 0) + d (N.g i 1)
          = (g (N.g i 0) + g (N.g i 1)) + (g' (N.g i 0) + g' (N.g i 1)) := by
            dsimp [d]; ring
        _ = (g (N.f i 0) + g (N.f i 1)) + (g' (N.f i 0) + g' (N.f i 1)) := by
            rw [h1, h2]
        _ = d (N.f i 0) + d (N.f i 1) := by dsimp [d]; ring
        _ = N.δ w i := hdf i
    have hloc : ∀ p ∈ bd N.D ∩ N.φ ⁻¹' (bd S),
        ∃ W ∈ 𝓝 p, ∀ x ∈ W ∩ (bd N.D ∩ N.φ ⁻¹' (bd S)), d x = d p := by
      intro p ⟨hpbd_D, hpbd_S⟩
      obtain ⟨W, hW, h1⟩ := hd_prim p trivial
      have hM : NearDiag (N_bd ∩ N'_bd) := hN_bd.inter hN'_bd
      have hMp : (fun x => (N.φ p, N.φ x)) ⁻¹' (N_bd ∩ N'_bd) ∈ 𝓝 p :=
        (Continuous.prodMk_right (N.φ p) |>.comp
          N.quotientMap_φ.continuous).continuousAt.preimage_mem_nhds
          (hM (N.φ p))
      refine ⟨W ∩ _, Filter.inter_mem hW hMp, fun x ⟨⟨hxW, hxN⟩, _, hxbd_S⟩ => ?_⟩
      have hpx := h1 p ⟨mem_of_mem_nhds hW, trivial⟩ x ⟨hxW, trivial⟩
      change φ (N.φ p) (N.φ x) + φ' (N.φ p) (N.φ x) = d p + d x at hpx
      rw [hbd (N.φ p) hpbd_S (N.φ x) hxbd_S hxN.1,
        hbd' (N.φ p) hpbd_S (N.φ x) hxbd_S hxN.2, zero_add, add_comm (d p)] at hpx
      exact CharTwo.add_eq_zero.mp hpx.symm
    have hfg : ∀ (i : Fin N.r) (t : unitInterval), d (N.f i t) = d (N.g i t) := by
      intro i t
      have hjump := (N.prim_seam_jump_const hd_prim i).1 t
      have hf0_V : N.φ (N.f i 0) ∈ N.seamV := ⟨i, Or.inl rfl⟩
      have hg0_V : N.φ (N.g i 0) ∈ N.seamV := ⟨i, Or.inl (N.φ_f_eq_φ_g i 0)⟩
      have h0 := N.bd_D_const_of_cuff_and_seam hS hpos d w hdf hdg hloc hf0_V hg0_V
      have hw_eq : (⟨N.φ (N.g i 0), hg0_V⟩ : N.seamV) = ⟨N.φ (N.f i 0), hf0_V⟩ :=
        Subtype.ext (N.φ_f_eq_φ_g i 0).symm
      rw [hw_eq] at h0
      rw [add_right_cancel h0, CharTwo.add_self_eq_zero] at hjump
      exact CharTwo.add_eq_zero.mp hjump
    obtain ⟨h_rel, N_rel, hN_rel, hrel⟩ := N.cohRel_of_prim_fib hψ_coc hd_prim hfg
    refine ⟨h_rel, N_rel, hN_rel, fun x y hxy => ?_⟩
    have hr := hrel x y hxy
    simp only [ψ, Pi.zero_apply, add_zero, CharTwo.sub_eq_add] at hr ⊢
    exact hr

/-- Helper for `exists_step_func_on_bd_D`: the two halves `Ico 0 t_mid` and `Ioc t_mid 1` of `N.f i`
lie in opposite components of `bd N.D \ {N.f i t_mid, N.g i t_mid}`. -/
private theorem half_arc_in_opposite_components (N : Net S) (i : Fin N.r)
    {t_mid : unitInterval} (ht_mid : t_mid ∈ Ioo (0 : unitInterval) 1)
    {B₁ B₂ : Set N.D}
    (hcomp : componentsIn (bd N.D \ {N.f i t_mid, N.g i t_mid}) = {B₁, B₂})
    (hdisj : Disjoint B₁ B₂)
    (hunion : bd N.D \ {N.f i t_mid, N.g i t_mid} = B₁ ∪ B₂)
    (hm_cl₁ : N.f i t_mid ∈ closure B₁) (hm_cl₂ : N.f i t_mid ∈ closure B₂) :
    (N.f i '' Ico 0 t_mid ⊆ B₁ ∧ N.f i '' Ioc t_mid 1 ⊆ B₂) ∨
      (N.f i '' Ico 0 t_mid ⊆ B₂ ∧ N.f i '' Ioc t_mid 1 ⊆ B₁) := by
  let M : Set N.D := {N.f i t_mid, N.g i t_mid}
  have hsub_cc : ∀ {A : Set N.D} {a : N.D}, IsPreconnected A → a ∈ A → A ⊆ bd N.D \ M →
      A ⊆ B₁ ∨ A ⊆ B₂ := by
    intro A a hconn ha hsub
    have h1 : A ⊆ connectedComponentIn (bd N.D \ M) a := hconn.subset_connectedComponentIn ha hsub
    have h2 : connectedComponentIn (bd N.D \ M) a ∈ ({B₁, B₂} : Set (Set N.D)) :=
      hcomp ▸ ⟨a, hsub ha, rfl⟩
    rcases h2 with hB1 | hB2
    · exact Or.inl (hB1 ▸ h1)
    · exact Or.inr ((mem_singleton_iff.mp hB2) ▸ h1)
  have hIco_sub : N.f i '' Ico 0 t_mid ⊆ bd N.D \ M := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨N.range_f_subset_bd i ⟨u, rfl⟩, ?_⟩
    rintro (h1 | h2)
    · exact hu.2.ne (N.injective_f i h1)
    · exact N.internally_disjoint_gf i i t_mid ht_mid ⟨u, mem_singleton_iff.mp h2⟩
  have hIoc_sub : N.f i '' Ioc t_mid 1 ⊆ bd N.D \ M := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨N.range_f_subset_bd i ⟨u, rfl⟩, ?_⟩
    rintro (h1 | h2)
    · exact hu.1.ne' (N.injective_f i h1)
    · exact N.internally_disjoint_gf i i t_mid ht_mid ⟨u, mem_singleton_iff.mp h2⟩
  have h0_Ico : N.f i 0 ∈ N.f i '' Ico 0 t_mid := ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩
  have h1_Ioc : N.f i 1 ∈ N.f i '' Ioc t_mid 1 := ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩
  have hIco_B := hsub_cc (isPreconnected_Ico.image _ (N.f i).continuous.continuousOn) h0_Ico
    hIco_sub
  have hIoc_B := hsub_cc (isPreconnected_Ioc.image _ (N.f i).continuous.continuousOn) h1_Ioc
    hIoc_sub
  obtain ⟨U, hU, hU_eq⟩ := N.exists_isOpen_inter_bd_eq_image_Ioo_f i 0 1
  have hmU : N.f i t_mid ∈ U := by
    have h : N.f i t_mid ∈ U ∩ bd N.D := by
      rw [hU_eq]
      exact ⟨t_mid, ht_mid, rfl⟩
    exact h.1
  have hnot_both : ∀ {B B' : Set N.D}, Disjoint B B' → B' ⊆ bd N.D \ M →
      N.f i t_mid ∈ closure B' →
      ¬ (N.f i '' Ico 0 t_mid ⊆ B ∧ N.f i '' Ioc t_mid 1 ⊆ B) := by
    intro B B' hd hB'_sub hm_cl ⟨h1, h2⟩
    obtain ⟨x, hxU, hxB'⟩ := _root_.mem_closure_iff.mp hm_cl U hU hmU
    have hx_Ioo : x ∈ N.f i '' Ioo (0 : unitInterval) 1 := by
      rw [← hU_eq]
      exact ⟨hxU, (hB'_sub hxB').1⟩
    obtain ⟨u, hu, rfl⟩ := hx_Ioo
    rcases lt_trichotomy u t_mid with hlt | rfl | hgt
    · exact hd.le_bot ⟨h1 ⟨u, ⟨hu.1.le, hlt⟩, rfl⟩, hxB'⟩
    · exact (hB'_sub hxB').2 (Or.inl rfl)
    · exact hd.le_bot ⟨h2 ⟨u, ⟨hgt, hu.2.le⟩, rfl⟩, hxB'⟩
  have hB1_sub : B₁ ⊆ bd N.D \ M := fun x hx => hunion ▸ Or.inl hx
  have hB2_sub : B₂ ⊆ bd N.D \ M := fun x hx => hunion ▸ Or.inr hx
  rcases hIco_B with h1 | h1 <;> rcases hIoc_B with h2 | h2
  · exact False.elim (hnot_both hdisj hB2_sub hm_cl₂ ⟨h1, h2⟩)
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact False.elim (hnot_both hdisj.symm hB1_sub hm_cl₁ ⟨h1, h2⟩)

/-- For each seam index `i : Fin N.r`, there is a step function `g_i : N.D → K` jumping only at the
midpoints `N.f i (1/2)` and `N.g i (1/2)` on `bd N.D`, with endpoint jump `δ_{i,j}` on `N.f j` and
constant sum `g_i (N.f j u) + g_i (N.g j u)` along each seam `j`. -/
private theorem exists_step_func_on_bd_D (N : Net S) (i : Fin N.r) :
    let t_mid : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    ∃ g_i : N.D → K,
      (∀ j : Fin N.r, g_i (N.f j 0) + g_i (N.f j 1) = if j = i then 1 else 0) ∧
      (∀ (j : Fin N.r) (u : unitInterval),
        g_i (N.f j u) + g_i (N.g j u) = g_i (N.f j 0) + g_i (N.g j 0)) ∧
      (∀ p ∈ bd N.D \ {N.f i t_mid, N.g i t_mid},
        ∃ W ∈ 𝓝 p, ∀ x ∈ W ∩ bd N.D, g_i x = g_i p) := by
  classical
  have : T2Space N.D := N.isSurface_D.2.1
  let t_mid : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht_mid : t_mid ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t_mid]
  let m₁ : N.D := N.f i t_mid
  let m₂ : N.D := N.g i t_mid
  have hm₁_bd : m₁ ∈ bd N.D := N.range_f_subset_bd i ⟨t_mid, rfl⟩
  have hm₂_bd : m₂ ∈ bd N.D := N.range_g_subset_bd i ⟨t_mid, rfl⟩
  have hm12 : m₁ ≠ m₂ := fun h => N.internally_disjoint_fg i i t_mid ht_mid ⟨t_mid, h.symm⟩
  obtain ⟨B₁, B₂, hcomp, hdisj, hunion, hline₁, hline₂⟩ :=
    oArc_components_diff_pair N.isOArc_bd_D hm₁_bd hm₂_bd hm12
  obtain ⟨hcl₁, hm₁_cl₁, hm₂_cl₁⟩ := hline₁.isClosed_union_and_endpoints_mem_closure
  obtain ⟨hcl₂, hm₁_cl₂, hm₂_cl₂⟩ := hline₂.isClosed_union_and_endpoints_mem_closure
  have hB1_sub : B₁ ⊆ bd N.D \ {m₁, m₂} := fun x hx => hunion ▸ Or.inl hx
  have hB2_sub : B₂ ⊆ bd N.D \ {m₁, m₂} := fun x hx => hunion ▸ Or.inr hx
  have hf_half := N.half_arc_in_opposite_components i ht_mid hcomp hdisj hunion hm₁_cl₁ hm₁_cl₂
  have hpair_symm : ({m₂, m₁} : Set N.D) = {m₁, m₂} := pair_comm m₂ m₁
  have hg_half :
      (N.g i '' Ico 0 t_mid ⊆ B₁ ∧ N.g i '' Ioc t_mid 1 ⊆ B₂) ∨
        (N.g i '' Ico 0 t_mid ⊆ B₂ ∧ N.g i '' Ioc t_mid 1 ⊆ B₁) := by
    have hcomp' : componentsIn (bd N.swapFG.D \ {N.swapFG.f i t_mid, N.swapFG.g i t_mid}) =
        {B₁, B₂} := by
      change componentsIn (bd N.D \ {m₂, m₁}) = {B₁, B₂}
      rwa [hpair_symm]
    have hunion' : bd N.swapFG.D \ {N.swapFG.f i t_mid, N.swapFG.g i t_mid} =
        B₁ ∪ B₂ := by
      change bd N.D \ {m₂, m₁} = B₁ ∪ B₂
      rwa [hpair_symm]
    have h := N.swapFG.half_arc_in_opposite_components i ht_mid hcomp' hdisj hunion' hm₂_cl₁ hm₂_cl₂
    exact h
  let valB (x : N.D) : K := if x ∈ B₁ then 1 else 0
  let g_i : N.D → K := fun x =>
    if x = m₁ then valB (N.f i 1)
    else if x = m₂ then valB (N.g i 1)
    else valB x
  have hg_i_not_m : ∀ {x : N.D}, x ∉ ({m₁, m₂} : Set N.D) → g_i x = valB x := by
    intro x hx
    have hx1 : x ≠ m₁ := fun h => hx (Or.inl h)
    have hx2 : x ≠ m₂ := fun h => hx (Or.inr (mem_singleton_iff.mpr h))
    simp [g_i, hx1, hx2]
  have hvalB_B1 : ∀ {x : N.D}, x ∈ B₁ → valB x = 1 := by
    intro x hx
    simp [valB, hx]
  have hvalB_B2 : ∀ {x : N.D}, x ∈ B₂ → valB x = 0 := by
    intro x hx
    have hx1 : x ∉ B₁ := fun hx1 => hdisj.le_bot ⟨hx1, hx⟩
    simp [valB, hx1]
  have hf_not_m : ∀ {j : Fin N.r} {u : unitInterval}, (j ≠ i ∨ u ≠ t_mid) →
      N.f j u ∉ ({m₁, m₂} : Set N.D) := by
    rintro j u hju (h1 | h2)
    · rcases hju with hij | hu
      · exact N.internally_disjoint_ff i j (Ne.symm hij) t_mid ht_mid ⟨u, h1⟩
      · by_cases hij : j = i
        · subst hij
          exact hu (N.injective_f j h1)
        · exact N.internally_disjoint_ff i j (Ne.symm hij) t_mid ht_mid ⟨u, h1⟩
    · exact N.internally_disjoint_gf i j t_mid ht_mid ⟨u, mem_singleton_iff.mp h2⟩
  have hg_not_m : ∀ {j : Fin N.r} {u : unitInterval}, (j ≠ i ∨ u ≠ t_mid) →
      N.g j u ∉ ({m₁, m₂} : Set N.D) := by
    rintro j u hju (h1 | h2)
    · exact N.internally_disjoint_fg i j t_mid ht_mid ⟨u, h1⟩
    · rcases hju with hij | hu
      · exact N.internally_disjoint_gg i j (Ne.symm hij) t_mid ht_mid ⟨u, mem_singleton_iff.mp h2⟩
      · by_cases hij : j = i
        · subst hij
          exact hu (N.injective_g j (mem_singleton_iff.mp h2))
        · exact N.internally_disjoint_gg i j (Ne.symm hij) t_mid ht_mid ⟨u, mem_singleton_iff.mp h2⟩
  have h0_ne_mid : (0 : unitInterval) ≠ t_mid := ht_mid.1.ne
  have h1_ne_mid : (1 : unitInterval) ≠ t_mid := ht_mid.2.ne'
  have hf_i_Ico : ∀ u ∈ Ico 0 t_mid, g_i (N.f i u) = g_i (N.f i 0) := by
    intro u hu
    rw [hg_i_not_m (hf_not_m (Or.inr hu.2.ne)), hg_i_not_m (hf_not_m (Or.inr h0_ne_mid))]
    rcases hf_half with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hvalB_B1 (h1 ⟨u, hu, rfl⟩), hvalB_B1 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩)]
    · rw [hvalB_B2 (h1 ⟨u, hu, rfl⟩), hvalB_B2 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩)]
  have hf_i_Ioc : ∀ u ∈ Ioc t_mid 1, g_i (N.f i u) = g_i (N.f i 1) := by
    intro u hu
    rw [hg_i_not_m (hf_not_m (Or.inr hu.1.ne')), hg_i_not_m (hf_not_m (Or.inr h1_ne_mid))]
    rcases hf_half with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [hvalB_B2 (h2 ⟨u, hu, rfl⟩), hvalB_B2 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
    · rw [hvalB_B1 (h2 ⟨u, hu, rfl⟩), hvalB_B1 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
  have hg_i_Ico : ∀ u ∈ Ico 0 t_mid, g_i (N.g i u) = g_i (N.g i 0) := by
    intro u hu
    rw [hg_i_not_m (hg_not_m (Or.inr hu.2.ne)), hg_i_not_m (hg_not_m (Or.inr h0_ne_mid))]
    rcases hg_half with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hvalB_B1 (h1 ⟨u, hu, rfl⟩), hvalB_B1 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩)]
    · rw [hvalB_B2 (h1 ⟨u, hu, rfl⟩), hvalB_B2 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩)]
  have hg_i_Ioc : ∀ u ∈ Ioc t_mid 1, g_i (N.g i u) = g_i (N.g i 1) := by
    intro u hu
    rw [hg_i_not_m (hg_not_m (Or.inr hu.1.ne')), hg_i_not_m (hg_not_m (Or.inr h1_ne_mid))]
    rcases hg_half with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [hvalB_B2 (h2 ⟨u, hu, rfl⟩), hvalB_B2 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
    · rw [hvalB_B1 (h2 ⟨u, hu, rfl⟩), hvalB_B1 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
  have hf_i_01 : g_i (N.f i 0) + g_i (N.f i 1) = 1 := by
    rw [hg_i_not_m (hf_not_m (Or.inr h0_ne_mid)), hg_i_not_m (hf_not_m (Or.inr h1_ne_mid))]
    rcases hf_half with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hvalB_B1 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩), hvalB_B2 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
      rfl
    · rw [hvalB_B2 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩), hvalB_B1 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
      rfl
  have hg_i_01 : g_i (N.g i 0) + g_i (N.g i 1) = 1 := by
    rw [hg_i_not_m (hg_not_m (Or.inr h0_ne_mid)), hg_i_not_m (hg_not_m (Or.inr h1_ne_mid))]
    rcases hg_half with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hvalB_B1 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩), hvalB_B2 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
      rfl
    · rw [hvalB_B2 (h1 ⟨0, ⟨le_rfl, ht_mid.1⟩, rfl⟩), hvalB_B1 (h2 ⟨1, ⟨ht_mid.2, le_rfl⟩, rfl⟩)]
      rfl
  have hf_ne_const : ∀ {j : Fin N.r}, j ≠ i → ∀ u : unitInterval, g_i (N.f j u) = g_i (N.f j 0)
    := by
    intro j hij u
    rw [hg_i_not_m (hf_not_m (Or.inl hij)), hg_i_not_m (hf_not_m (Or.inl hij))]
    have hconn : IsPreconnected (range (N.f j)) := (isConnected_range
      (N.f j).continuous).isPreconnected
    have hsub : range (N.f j) ⊆ bd N.D \ {m₁, m₂} := by
      rintro _ ⟨s, rfl⟩
      exact ⟨N.range_f_subset_bd j ⟨s, rfl⟩, hf_not_m (Or.inl hij)⟩
    have hcc := hconn.subset_connectedComponentIn ⟨0, rfl⟩ hsub
    have hmem : connectedComponentIn (bd N.D \ {m₁, m₂}) (N.f j 0) ∈ ({B₁, B₂} : Set (Set N.D)) :=
      hcomp ▸ ⟨N.f j 0, hsub ⟨0, rfl⟩, rfl⟩
    rcases hmem with hB1 | hB2
    · rw [hvalB_B1 (hB1 ▸ hcc ⟨u, rfl⟩), hvalB_B1 (hB1 ▸ hcc ⟨0, rfl⟩)]
    · have hB2' := mem_singleton_iff.mp hB2
      rw [hvalB_B2 (hB2' ▸ hcc ⟨u, rfl⟩), hvalB_B2 (hB2' ▸ hcc ⟨0, rfl⟩)]
  have hg_ne_const : ∀ {j : Fin N.r}, j ≠ i → ∀ u : unitInterval, g_i (N.g j u) = g_i (N.g j 0)
    := by
    intro j hij u
    rw [hg_i_not_m (hg_not_m (Or.inl hij)), hg_i_not_m (hg_not_m (Or.inl hij))]
    have hconn : IsPreconnected (range (N.g j)) := (isConnected_range
      (N.g j).continuous).isPreconnected
    have hsub : range (N.g j) ⊆ bd N.D \ {m₁, m₂} := by
      rintro _ ⟨s, rfl⟩
      exact ⟨N.range_g_subset_bd j ⟨s, rfl⟩, hg_not_m (Or.inl hij)⟩
    have hcc := hconn.subset_connectedComponentIn ⟨0, rfl⟩ hsub
    have hmem : connectedComponentIn (bd N.D \ {m₁, m₂}) (N.g j 0) ∈ ({B₁, B₂} : Set (Set N.D)) :=
      hcomp ▸ ⟨N.g j 0, hsub ⟨0, rfl⟩, rfl⟩
    rcases hmem with hB1 | hB2
    · rw [hvalB_B1 (hB1 ▸ hcc ⟨u, rfl⟩), hvalB_B1 (hB1 ▸ hcc ⟨0, rfl⟩)]
    · have hB2' := mem_singleton_iff.mp hB2
      rw [hvalB_B2 (hB2' ▸ hcc ⟨u, rfl⟩), hvalB_B2 (hB2' ▸ hcc ⟨0, rfl⟩)]
  refine ⟨g_i, ?_, ?_, ?_⟩
  · intro j
    by_cases hij : j = i
    · subst hij
      simp only [↓reduceIte, hf_i_01]
    · simp only [hij, ↓reduceIte, hf_ne_const hij 1, CharTwo.add_self_eq_zero]
  · intro j u
    by_cases hij : j = i
    · subst hij
      have hsum1 : g_i (N.f j 1) + g_i (N.g j 1) = g_i (N.f j 0) + g_i (N.g j 0) := by
        have hring : (g_i (N.f j 1) + g_i (N.g j 1)) + (g_i (N.f j 0) + g_i (N.g j 0)) =
            (g_i (N.f j 0) + g_i (N.f j 1)) + (g_i (N.g j 0) + g_i (N.g j 1)) := by ring
        refine CharTwo.add_eq_zero.mp ?_
        rw [hring, hf_i_01, hg_i_01, CharTwo.add_self_eq_zero]
      rcases lt_trichotomy u t_mid with hlt | rfl | hgt
      · rw [hf_i_Ico u ⟨ u.2.1, hlt ⟩, hg_i_Ico u ⟨ u.2.1, hlt ⟩]
      · have hfm : g_i (N.f j t_mid) = g_i (N.f j 1) := by
          rw [hg_i_not_m (hf_not_m (Or.inr h1_ne_mid))]
          simp [g_i, m₁]
        have hgm : g_i (N.g j t_mid) = g_i (N.g j 1) := by
          rw [hg_i_not_m (hg_not_m (Or.inr h1_ne_mid))]
          simp [g_i, m₂, hm12.symm]
        rw [hfm, hgm, hsum1]
      · rw [hf_i_Ioc u ⟨ hgt, u.2.2 ⟩, hg_i_Ioc u ⟨ hgt, u.2.2 ⟩, hsum1]
    · rw [hf_ne_const hij u, hg_ne_const hij u]
  · intro p hp
    have hp_B : p ∈ B₁ ∪ B₂ := hunion ▸ hp
    rcases hp_B with hp1 | hp2
    · have hp_not2 : p ∉ B₂ ∪ {m₁, m₂} := by
        rintro (h2 | hm)
        · exact hdisj.le_bot ⟨hp1, h2⟩
        · exact hp.2 hm
      refine ⟨(B₂ ∪ {m₁, m₂})ᶜ, hcl₂.isOpen_compl.mem_nhds hp_not2, fun x ⟨hxW, hxbd⟩ => ?_⟩
      have hx_not_m : x ∉ ({m₁, m₂} : Set N.D) := fun hm => hxW (Or.inr hm)
      have hx_diff : x ∈ B₁ ∪ B₂ :=
        hunion ▸ (show x ∈ bd N.D \ {m₁, m₂} from ⟨hxbd, hx_not_m⟩)
      have hx_B1 : x ∈ B₁ := hx_diff.resolve_right fun h2 => hxW (Or.inl h2)
      rw [hg_i_not_m hx_not_m, hg_i_not_m hp.2, hvalB_B1 hx_B1, hvalB_B1 hp1]
    · have hp_not1 : p ∉ B₁ ∪ {m₁, m₂} := by
        rintro (h1 | hm)
        · exact hdisj.le_bot ⟨h1, hp2⟩
        · exact hp.2 hm
      refine ⟨(B₁ ∪ {m₁, m₂})ᶜ, hcl₁.isOpen_compl.mem_nhds hp_not1, fun x ⟨hxW, hxbd⟩ => ?_⟩
      have hx_not_m : x ∉ ({m₁, m₂} : Set N.D) := fun hm => hxW (Or.inr hm)
      have hx_diff : x ∈ B₁ ∪ B₂ :=
        hunion ▸ (show x ∈ bd N.D \ {m₁, m₂} from ⟨hxbd, hx_not_m⟩)
      have hx_B2 : x ∈ B₂ := hx_diff.resolve_left fun h1 => hxW (Or.inl h1)
      rw [hg_i_not_m hx_not_m, hg_i_not_m hp.2, hvalB_B2 hx_B2, hvalB_B2 hp2]

private theorem net_voltage_relation_isClosed
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    [T2Space N.D]
    (g : N.D → K)
    (hg_sum : ∀ (j : Fin N.r) (u : ↑unitInterval), g ((N.f j) u) + g ((N.g j) u) = g ((N.f j) 0) +
      g ((N.g j) 0))
    : letI : TopologicalSpace K := ⊥
      IsClosed {p : (N.D × K) × (N.D × K) |
        N.φ p.1.1 = N.φ p.2.1 ∧ g p.1.1 + p.1.2 = g p.2.1 + p.2.2} := by
  let _ : TopologicalSpace K := ⊥
  have : DiscreteTopology K := ⟨rfl⟩
  let covRel (x y : N.D × K) :=
    N.φ x.1 = N.φ y.1 ∧ g x.1 + x.2 = g y.1 + y.2
  change IsClosed {p : (N.D × K) × (N.D × K) | covRel p.1 p.2}
  let R₁ : Set ((N.D × K) × (N.D × K)) := {p | p.1 = p.2}
  let R₂ (i : Fin N.r) : Set ((N.D × K) × (N.D × K)) :=
    {p | (p.1.1, p.2.1) ∈ range (fun u => (N.f i u, N.g i u)) ∪
        range (fun u => (N.g i u, N.f i u)) ∧
      p.1.2 + p.2.2 = g (N.f i 0) + g (N.g i 0)}
  let R₃ : Set ((N.D × K) × (N.D × K)) :=
    {p | p.1.1 ∈ N.φ ⁻¹' N.seamV ∧ p.2.1 ∈ N.φ ⁻¹' N.seamV ∧ covRel p.1 p.2}
  have hcov_eq : {p : (N.D × K) × (N.D × K) | covRel p.1 p.2} =
      (R₁ ∪ ⋃ i : Fin N.r, R₂ i) ∪ R₃ := by
    ext ⟨⟨x, s⟩, ⟨y, t⟩⟩
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hφ, hg_eq⟩
      by_cases hxy : x = y
      · subst hxy
        exact Or.inl (Or.inl (Prod.ext rfl (add_left_cancel hg_eq)))
      · by_cases hxV : N.φ x ∈ N.seamV
        · have hyV : N.φ y ∈ N.seamV := hφ ▸ hxV
          exact Or.inr ⟨hxV, hyV, hφ, hg_eq⟩
        · have hIoo : ∃ (i : Fin N.r) (u : unitInterval),
              u ∈ Ioo (0 : unitInterval) 1 ∧ N.φ (N.f i u) = N.φ x := by
            by_contra hnot
            let R_step : N.D → N.D → Prop := fun a b =>
              ∃ (j : Fin N.r) (u : unitInterval), a = N.f j u ∧ b = N.g j u
            have hrel : Relation.EqvGen R_step x y := (N.bd_eq_iff x y).mp hφ
            have hno_step : ∀ a b : N.D, R_step a b → N.φ a ≠ N.φ x := by
              rintro a b ⟨j, u, rfl, rfl⟩ hφ_a
              rcases unitInterval_eq_zero_or_one_or_mem_Ioo u with rfl | rfl | hu
              · exact hxV ⟨j, Or.inl hφ_a⟩
              · exact hxV ⟨j, Or.inr hφ_a⟩
              · exact hnot ⟨j, u, hu, hφ_a⟩
            have heq_of_rel : ∀ a b : N.D, Relation.EqvGen R_step a b →
                (N.φ a = N.φ x → a = b) := by
              intro a b hab
              induction hab with
              | rel u v huv =>
                exact fun hu => False.elim (hno_step u v huv hu)
              | refl u =>
                exact fun _ => rfl
              | symm u v huv ih =>
                intro hv
                have huv_φ : N.φ u = N.φ v := (N.bd_eq_iff u v).mpr huv
                exact (ih (huv_φ.trans hv)).symm
              | trans u w v huw _ ih1 ih2 =>
                intro hu
                have huw_φ : N.φ u = N.φ w := (N.bd_eq_iff u w).mpr huw
                exact (ih1 hu).trans (ih2 (huw_φ.symm.trans hu))
            exact hxy (heq_of_rel x y hrel rfl)
          obtain ⟨i, u, hu, hφ_u⟩ := hIoo
          have hx_fg := N.eq_f_or_g_of_φ_eq_of_mem_Ioo i hu hφ_u
          have hy_fg := N.eq_f_or_g_of_φ_eq_of_mem_Ioo i hu (hφ_u.trans hφ)
          rcases hx_fg with rfl | rfl <;> rcases hy_fg with rfl | rfl
          · exact False.elim (hxy rfl)
          · refine Or.inl (Or.inr ⟨i, Or.inl ⟨u, rfl⟩, ?_⟩)
            rw [← hg_sum i u]
            have h1 : (s + t) + (g (N.f i u) + g (N.g i u)) =
                (g (N.f i u) + s) + (g (N.g i u) + t) := by ring
            refine CharTwo.add_eq_zero.mp ?_
            rw [h1, hg_eq, CharTwo.add_self_eq_zero]
          · refine Or.inl (Or.inr ⟨i, Or.inr ⟨u, rfl⟩, ?_⟩)
            rw [← hg_sum i u]
            have h1 : (s + t) + (g (N.f i u) + g (N.g i u)) =
                (g (N.g i u) + s) + (g (N.f i u) + t) := by ring
            refine CharTwo.add_eq_zero.mp ?_
            rw [h1, hg_eq, CharTwo.add_self_eq_zero]
          · exact False.elim (hxy rfl)
    · rintro ((h1 | ⟨i, ⟨⟨u, hu⟩ | ⟨u, hu⟩, hst⟩⟩) | ⟨_, _, hcov⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (show (x, s) = (y, t) from h1)
        exact ⟨rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hu.symm
        refine ⟨N.φ_f_eq_φ_g i u, ?_⟩
        have hst' : s + t = g (N.f i u) + g (N.g i u) := hst.trans (hg_sum i u).symm
        have h1 : (g (N.f i u) + s) + (g (N.g i u) + t) =
            (s + t) + (g (N.f i u) + g (N.g i u)) := by ring
        exact CharTwo.add_eq_zero.mp (by rw [h1, hst', CharTwo.add_self_eq_zero])
      · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hu.symm
        refine ⟨(N.φ_f_eq_φ_g i u).symm, ?_⟩
        have hst' : s + t = g (N.f i u) + g (N.g i u) := hst.trans (hg_sum i u).symm
        have h1 : (g (N.g i u) + s) + (g (N.f i u) + t) =
            (s + t) + (g (N.f i u) + g (N.g i u)) := by ring
        exact CharTwo.add_eq_zero.mp (by rw [h1, hst', CharTwo.add_self_eq_zero])
      · exact hcov
  rw [hcov_eq]
  refine ((isClosed_diagonal.union (isClosed_iUnion_of_finite fun i => ?_)).union ?_)
  · have hcl_fg : IsClosed (range (fun u => (N.f i u, N.g i u)) ∪
        range (fun u => (N.g i u, N.f i u))) :=
      ((isCompact_range ((N.f i).continuous.prodMk (N.g i).continuous)).isClosed).union
        ((isCompact_range ((N.g i).continuous.prodMk (N.f i).continuous)).isClosed)
    have hc1 : Continuous fun p : (N.D × K) × (N.D × K) => (p.1.1, p.2.1) :=
      (continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)
    have hc2 : Continuous fun p : (N.D × K) × (N.D × K) => p.1.2 + p.2.2 :=
      (continuous_of_discreteTopology (f := fun q : K × K => q.1 + q.2)).comp
        ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
    exact (hcl_fg.preimage hc1).inter (isClosed_singleton.preimage hc2)
  · have hfin_pre : (N.φ ⁻¹' N.seamV).Finite := N.finite_preimage N.finite_seamV
    have hfin_R3 : R₃.Finite := by
      refine (((hfin_pre.prod finite_univ).prod (hfin_pre.prod finite_univ)).subset ?_)
      rintro ⟨⟨x, s⟩, ⟨y, t⟩⟩ ⟨hx, hy, _⟩
      exact ⟨⟨hx, trivial⟩, ⟨hy, trivial⟩⟩
    exact hfin_R3.isClosed

private theorem net_cover_action_free
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    (g : N.D → K)
    (covSetoid : Setoid (N.D × K))
    (hexact : ∀ {x y : N.D × K}, Quotient.mk covSetoid x = Quotient.mk covSetoid y →
      N.φ x.1 = N.φ y.1 ∧ g x.1 + x.2 = g y.1 + y.2)
    (τ : K → (Quotient covSetoid) → (Quotient covSetoid))
    (hτmk : ∀ (s : K) (x : N.D × K),
      τ s (Quotient.mk covSetoid x) = Quotient.mk covSetoid (x.1, x.2 + s)) :
    ∀ (s : K) (z : (Quotient covSetoid)), τ s z = z → s = 0 := by
  let Z := Quotient covSetoid
  intro s z he
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  rw [hτmk] at he
  exact add_eq_left.mp (add_left_cancel (hexact he).2)

private theorem voltage_primitive_of_cover
    {S : Type u}
    [TopologicalSpace S]
    (N : Net S)
    {Z : Type u}
    [TopologicalSpace Z]
    (g : N.D → K)
    (mk : N.D × K → Z)
    (hmk : let _ : TopologicalSpace K := ⊥; Continuous mk)
    (τ : K → Z → Z)
    (hτmk : ∀ (s : K) (x : N.D × K), τ s (mk x) = mk (x.1, x.2 + s))
    (σ : S → Z)
    (hσf : ∀ (a : N.D), σ (N.φ a) = mk (a, g a))
    (φ : S → S → K)
    (V_cov : Set (Z × Z))
    (hV_cov : NearDiag V_cov)
    (hφs : ∀ (x y : S) (s : K), (τ s (σ x), σ y) ∈ V_cov → φ x y = s)
    (hinv : ∀ (t : K) (z z' : Z), (z, z') ∈ V_cov → (τ t z, τ t z') ∈ V_cov) :
    Prim (pbk N.φ φ) univ g := by
  let _ : TopologicalSpace K := ⊥
  let P : N.D → Z := fun z => mk (z, 0)
  have hPc : Continuous P := hmk.comp (continuous_id.prodMk continuous_const)
  intro p _
  have hVp : (fun a : N.D × N.D => (P a.1, P a.2)) ⁻¹' V_cov ∈ 𝓝 (p, p) :=
    ((hPc.comp continuous_fst).prodMk (hPc.comp continuous_snd)).continuousAt.preimage_mem_nhds
      (hV_cov (P p))
  rw [mem_nhds_prod_iff] at hVp
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := hVp
  refine ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, fun a ha b hb => ?_⟩
  have hab : (P a, P b) ∈ V_cov := hsub (mk_mem_prod ha.1.1 hb.1.2)
  have h2 := hinv (g b) _ _ hab
  change (τ (g b) (mk (a, 0)), τ (g b) (mk (b, 0))) ∈ V_cov at h2
  rw [hτmk, hτmk, zero_add] at h2
  have hab' : mk (a, g b) = τ (g a + g b) (σ (N.φ a)) := by
    rw [hσf a, hτmk]
    congr 2
    have hring : g a + (g a + g b) = (g a + g a) + g b := by ring
    rw [hring, CharTwo.add_self_eq_zero, zero_add]
  rw [hab', ← hσf b] at h2
  exact hφs (N.φ a) (N.φ b) (g a + g b) h2

/-- Every seam voltage assignment `v : Fin N.r → K` arises from a local cocycle `φ : S → S → K`
that vanishes near the diagonal of `bd S` and has a primitive `g` on `N.D` with endpoint jumps `v`.
-/
private theorem exists_cocycle_of_net_volt (hS : IsSurface S) (N : Net S) (v : Fin N.r → K) :
    ∃ (φ : S → S → K) (g : N.D → K),
      IsCoc φ ∧
      (∃ N_bd : Set (S × S), NearDiag N_bd ∧ ∀ x ∈ bd S, ∀ y ∈ bd S, (x, y) ∈ N_bd → φ x y = 0) ∧
      Prim (pbk N.φ φ) univ g ∧
      ∀ i : Fin N.r, g (N.f i 0) + g (N.f i 1) = v i := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have : T2Space S := hS.2.1
  let _ : TopologicalSpace K := ⊥
  have : DiscreteTopology K := ⟨rfl⟩
  let t_mid : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht_mid : t_mid ∈ Ioo (0 : unitInterval) 1 := by
    constructor <;> rw [← Subtype.coe_lt_coe] <;> norm_num [t_mid]
  choose g_step hg_step01 hg_step_sum hg_step_loc using N.exists_step_func_on_bd_D
  let g : N.D → K := fun x => ∑ i : Fin N.r, v i * g_step i x
  have hg_01 : ∀ j : Fin N.r, g (N.f j 0) + g (N.f j 1) = v j := by
    intro j
    calc
      g (N.f j 0) + g (N.f j 1)
        = ∑ i : Fin N.r, v i * (g_step i (N.f j 0) + g_step i (N.f j 1)) := by
          dsimp [g]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (mul_add (v i) _ _).symm
      _ = ∑ i : Fin N.r, v i * (if j = i then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hg_step01 i j]
      _ = v j := by simp
  have hg_sum : ∀ (j : Fin N.r) (u : unitInterval),
      g (N.f j u) + g (N.g j u) = g (N.f j 0) + g (N.g j 0) := by
    intro j u
    calc
      g (N.f j u) + g (N.g j u)
        = ∑ i : Fin N.r, v i * (g_step i (N.f j u) + g_step i (N.g j u)) := by
          dsimp [g]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (mul_add (v i) _ _).symm
      _ = ∑ i : Fin N.r, v i * (g_step i (N.f j 0) + g_step i (N.g j 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hg_step_sum i j u]
      _ = g (N.f j 0) + g (N.g j 0) := by
          dsimp [g]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => mul_add (v i) _ _
  have hg_loc : ∀ p ∈ bd N.D ∩ N.φ ⁻¹' (bd S), ∃ W ∈ 𝓝 p, ∀ x ∈ W ∩ bd N.D, g x = g p := by
    intro p ⟨hpbd_D, hpbd_S⟩
    have hp_not_m : ∀ i : Fin N.r, p ∈ bd N.D \ {N.f i t_mid, N.g i t_mid} := by
      intro i
      refine ⟨hpbd_D, ?_⟩
      rintro (rfl | h2)
      · exact N.notMem_bd_of_mem_Ioo hS i ht_mid hpbd_S
      · rw [mem_singleton_iff.mp h2] at hpbd_S
        change N.φ (N.g i t_mid) ∈ bd S at hpbd_S
        rw [← N.φ_f_eq_φ_g i t_mid] at hpbd_S
        exact N.notMem_bd_of_mem_Ioo hS i ht_mid hpbd_S
    choose W_i hW_i hW_i_eq using fun i => hg_step_loc i p (hp_not_m i)
    refine ⟨⋂ i : Fin N.r, W_i i, Filter.iInter_mem.mpr hW_i, fun x ⟨hxW, hxbd⟩ => ?_⟩
    dsimp [g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW_i_eq i x ⟨mem_iInter.mp hxW i, hxbd⟩]
  let covRel (x y : N.D × K) : Prop := N.φ x.1 = N.φ y.1 ∧ g x.1 + x.2 = g y.1 + y.2
  let covSetoid : Setoid (N.D × K) :=
    { r := covRel
      iseqv :=
        { refl := fun x => ⟨rfl, rfl⟩
          symm := fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩
          trans := fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨h1.trans h3, h2.trans h4⟩ } }
  have hcl_cov : IsClosed {p : (N.D × K) × (N.D × K) | covSetoid.r p.1 p.2} := by
    exact net_voltage_relation_isClosed (S := S) N g hg_sum
  have htZ : T2Space (Quotient covSetoid) :=
    t2Space_quotient_of_isClosed covSetoid hcl_cov
  let Z := Quotient covSetoid
  let mk : N.D × K → Z := Quotient.mk covSetoid
  have hmk : Continuous mk := continuous_quotient_mk'
  have hsound : ∀ {x y : N.D × K}, N.φ x.1 = N.φ y.1 → g x.1 + x.2 = g y.1 + y.2 → mk x = mk y :=
    fun h1 h2 => Quotient.sound ⟨h1, h2⟩
  have hexact : ∀ {x y : N.D × K}, mk x = mk y → N.φ x.1 = N.φ y.1 ∧ g x.1 + x.2 = g y.1 + y.2 :=
    fun h => Quotient.exact h
  let τ : K → Z → Z := fun s =>
    Quotient.lift (fun x => mk (x.1, x.2 + s)) fun x y h =>
      hsound h.1 (by
        have h2 : g x.1 + x.2 = g y.1 + y.2 := h.2
        simp only
        rw [← add_assoc, h2, add_assoc])
  have hτmk : ∀ s x, τ s (mk x) = mk (x.1, x.2 + s) := fun _ _ => rfl
  have hτc : ∀ s, Continuous (τ s) := fun s =>
    Continuous.quotient_lift (hmk.comp (continuous_fst.prodMk (continuous_snd.add
      continuous_const))) _
  have hτ0 : ∀ z, τ 0 z = z := by
    intro z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    rw [hτmk, add_zero]
  have hτa : ∀ s t z, τ s (τ t z) = τ (t + s) z := by
    intro s t z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    rw [hτmk, hτmk, hτmk, add_assoc]
  have hfree : ∀ s z, τ s z = z → s = 0 := by
    exact net_cover_action_free (S := S) N g covSetoid hexact τ hτmk
  let q : Z → S := Quotient.lift (fun x => N.φ x.1) fun _ _ h => h.1
  have hq : Continuous q :=
    Continuous.quotient_lift (N.quotientMap_φ.continuous.comp continuous_fst) _
  have hs : Function.Surjective q := fun y => by
    obtain ⟨a, rfl⟩ := N.quotientMap_φ.surjective y
    exact ⟨mk (a, 0), rfl⟩
  have hfib : ∀ z z', q z = q z' → ∃ s, z' = τ s z := by
    intro z z' he
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    obtain ⟨y, rfl⟩ := Quotient.exists_rep z'
    have h1 : N.φ x.1 = N.φ y.1 := he
    refine ⟨x.2 + g x.1 + g y.1 + y.2, ?_⟩
    rw [hτmk]
    refine hsound h1.symm ?_
    have hring : g x.1 + (x.2 + (x.2 + g x.1 + g y.1 + y.2)) =
        (g x.1 + g x.1) + (x.2 + x.2) + (g y.1 + y.2) := by ring
    rw [hring, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, zero_add]
  have hfib' : ∀ s z, q (τ s z) = q z := by
    intro s z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    rfl
  choose l hl using N.quotientMap_φ.surjective
  let σ : S → Z := fun y => mk (l y, g (l y))
  have hσ : ∀ y, q (σ y) = y := fun y => hl y
  have hσf : ∀ a : N.D, σ (N.φ a) = mk (a, g a) := fun a =>
    hsound (hl (N.φ a)) (by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero])
  obtain ⟨φ, V_cov, hV_cov, hφ_coc, hφs, hinv⟩ :=
    cocycle_of_cover τ hτc hτ0 hτa hfree q hq hs hfib hfib' σ hσ
  have hprim : Prim (pbk N.φ φ) univ g := by
    exact voltage_primitive_of_cover N g mk hmk τ hτmk σ hσf φ V_cov hV_cov hφs
      hinv
  have hbd_zero : ∃ N_bd : Set (S × S), NearDiag N_bd ∧
      ∀ x ∈ bd S, ∀ y ∈ bd S, (x, y) ∈ N_bd → φ x y = 0 := by
    obtain ⟨N_coc, hN_coc, hcoc⟩ := hφ_coc
    have hloc_S : ∀ p ∈ bd S, ∃ Ω : Set S, IsOpen Ω ∧ p ∈ Ω ∧ Ω ×ˢ Ω ⊆ N_coc ∧
        ∀ x ∈ Ω ∩ bd S, φ x p = 0 ∧ φ p x = 0 := by
      intro p hp
      have hloc_z : ∀ z : N.D, ∃ U : Set N.D, IsOpen U ∧ z ∈ U ∧
          (N.φ z = p → ∀ a ∈ U ∩ bd N.D, φ (N.φ a) p = 0 ∧ φ p (N.φ a) = 0) := by
        intro z
        by_cases hzp : N.φ z = p
        · have hzp_bd : N.φ z ∈ bd S := hzp.symm ▸ hp
          have hz_bd : z ∈ bd N.D := N.preimage_seamU ▸ N.bd_subset_seamU hzp_bd
          obtain ⟨W₁, hW₁, h1⟩ := hg_loc z ⟨hz_bd, hzp_bd⟩
          obtain ⟨W₂, hW₂, h2⟩ := hprim z trivial
          obtain ⟨U, hU_sub, hU_open, hzU⟩ := mem_nhds_iff.mp (Filter.inter_mem hW₁ hW₂)
          refine ⟨U, hU_open, hzU, fun _ a ⟨haU, habd⟩ => ?_⟩
          have hga : g a = g z := h1 a ⟨(hU_sub haU).1, habd⟩
          have hφ1 := h2 a ⟨(hU_sub haU).2, trivial⟩ z ⟨(hU_sub hzU).2, trivial⟩
          have hφ2 := h2 z ⟨(hU_sub hzU).2, trivial⟩ a ⟨(hU_sub haU).2, trivial⟩
          change φ (N.φ a) (N.φ z) = g a + g z at hφ1
          change φ (N.φ z) (N.φ a) = g z + g a at hφ2
          rw [hzp, hga, CharTwo.add_self_eq_zero] at hφ1 hφ2
          exact ⟨hφ1, hφ2⟩
        · exact ⟨univ, isOpen_univ, trivial, fun h => absurd h hzp⟩
      choose U_z hU_z_open hz_U hU_z_zero using hloc_z
      let U_p : Set N.D := ⋃ z ∈ N.φ ⁻¹' {p}, U_z z
      have hUp_open : IsOpen U_p := isOpen_biUnion fun z _ => hU_z_open z
      let Ω₀ : Set S := (N.φ '' U_pᶜ)ᶜ
      have hΩ₀_open : IsOpen Ω₀ :=
        (N.quotientMap_φ.continuous.isClosedMap U_pᶜ hUp_open.isClosed_compl).isOpen_compl
      have hp_Ω₀ : p ∈ Ω₀ := by
        rintro ⟨z, hz_not, hzp⟩
        exact hz_not (mem_biUnion (mem_singleton_iff.mpr hzp) (hz_U z))
      have hNcoc_p : N_coc ∈ 𝓝 (p, p) := hN_coc p
      rw [mem_nhds_prod_iff] at hNcoc_p
      obtain ⟨V₁, hV₁, V₂, hV₂, hV_sub⟩ := hNcoc_p
      obtain ⟨Ω, hΩ_sub, hΩ_open, hpΩ⟩ :=
        mem_nhds_iff.mp (Filter.inter_mem (hΩ₀_open.mem_nhds hp_Ω₀) (Filter.inter_mem hV₁ hV₂))
      refine ⟨Ω, hΩ_open, hpΩ, ?_, fun x ⟨hxΩ, hxbd⟩ => ?_⟩
      · rintro ⟨a, b⟩ ⟨ha, hb⟩
        exact hV_sub ⟨(hΩ_sub ha).2.1, (hΩ_sub hb).2.2⟩
      · obtain ⟨a, rfl⟩ := N.quotientMap_φ.surjective x
        have habd : a ∈ bd N.D := N.preimage_seamU ▸ N.bd_subset_seamU hxbd
        have ha_Up : a ∈ U_p := by
          by_contra hnot
          exact (hΩ_sub hxΩ).1 ⟨a, hnot, rfl⟩
        obtain ⟨z, hzp, ha_Uz⟩ := mem_iUnion₂.mp ha_Up
        exact hU_z_zero z hzp a ⟨ha_Uz, habd⟩
    have hloc_all : ∀ p : S, ∃ Ω : Set S, IsOpen Ω ∧ p ∈ Ω ∧
        (p ∈ bd S → Ω ×ˢ Ω ⊆ N_coc ∧ ∀ x ∈ Ω ∩ bd S, φ x p = 0 ∧ φ p x = 0) ∧
        (p ∉ bd S → Ω ⊆ (bd S)ᶜ) := by
      intro p
      by_cases hp : p ∈ bd S
      · obtain ⟨Ω, hΩ_open, hpΩ, hsub, hzero⟩ := hloc_S p hp
        exact ⟨Ω, hΩ_open, hpΩ, fun _ => ⟨hsub, hzero⟩, fun h => absurd hp h⟩
      · exact ⟨(bd S)ᶜ, (isClosed_bd S).isOpen_compl, hp, fun h => absurd h hp, fun _ => Subset.rfl⟩
    choose Ω hΩ_open hpΩ hΩ_bd hΩ_not using hloc_all
    let N_bd : Set (S × S) := ⋃ p : S, Ω p ×ˢ Ω p
    have hN_bd_open : IsOpen N_bd := isOpen_iUnion fun p => (hΩ_open p).prod (hΩ_open p)
    have hNear : NearDiag N_bd := fun p =>
      hN_bd_open.mem_nhds (mem_iUnion.mpr ⟨p, hpΩ p, hpΩ p⟩)
    refine ⟨N_bd, hNear, fun x hx y hy hxy => ?_⟩
    obtain ⟨p, hxp, hyp⟩ := mem_iUnion.mp hxy
    have hp_bd : p ∈ bd S := by
      by_contra hnot
      exact hΩ_not p hnot hxp hx
    obtain ⟨hsub_coc, hzero⟩ := hΩ_bd p hp_bd
    have h1 := (hzero x ⟨hxp, hx⟩).1
    have h2 := (hzero y ⟨hyp, hy⟩).2
    have h3 := hcoc x p y (hsub_coc ⟨hxp, hpΩ p⟩) (hsub_coc ⟨hpΩ p, hyp⟩) (hsub_coc ⟨hxp, hyp⟩)
    rw [← h3, h1, h2, add_zero]
  exact ⟨φ, g, hφ_coc, hbd_zero, hprim, hg_01⟩

end Net

local notation "K" => ZMod 2

/-- **(2.2)** (Euler's formula for seam graphs, page 216): if `N` is a net in a surface
`S ≃ₜ Σ(a, b, c)` and `J` is its seam graph, then `|E(J)| + 1 = |V(J)| + 2a + b + c`. -/
theorem seamGraph_euler_formula (S : Type u) [TopologicalSpace S]
    (hS : IsSurface S) (a b c : ℕ) (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (J : Drawing S) (hSeam : IsSeamGraph J) :
    J.E.ncard + 1 = J.V.ncard + 2 * a + b + c := by
  rcases he with ⟨e_surf⟩
  rcases hSeam with ⟨N, hJ⟩
  have : T2Space S := hS.2.1
  have hpos : 0 < N.r := N.r_pos_of_isSeamGraphFor hJ
  have hfin_V : N.seamV.Finite := N.finite_seamV
  have hfin_bdV : (bd S ∩ N.seamV).Finite := hfin_V.subset inter_subset_right
  obtain ⟨ht_model, f_ew, hf_ew⟩ := presents_ew a b c
  have hcuffs_eq : (cuffs S).ncard = c := by
    rw [ncard_cuffs_congr e_surf, ncard_cuffs hf_ew]
  have hkCl_eq : Nat.card (KCl S K) = 2 ^ (2 * a + b) := by
    rw [card_kCl_congr e_surf, GraphMinor.Surface.card_kCl (A := K) hf_ew, card_lam_two]
  choose φ_v g_v hφ_v_coc hφ_v_bd hg_v_prim hg_v_01 using N.exists_cocycle_of_net_volt hS
  choose N_bd_v hN_bd_v hbd_v using hφ_v_bd
  have hφ_v_mem : ∀ v : Fin N.r → K, φ_v v ∈ KSet S K := by
    intro v
    refine ⟨hφ_v_coc v, 0, N_bd_v v, hN_bd_v v, fun x hx y hy hxy => ?_⟩
    simp [hbd_v v x hx y hy hxy]
  let toKCl : (Fin N.r → K) → KCl S K := fun v =>
    Quotient.mk (kSetoid S K) ⟨φ_v v, hφ_v_mem v⟩
  have hrel_iff : ∀ v w : Fin N.r → K,
      CohRel (φ_v v) (φ_v w) ↔ (Submodule.quotientRel (LinearMap.range N.δ)).r v w := by
    intro v w
    rw [N.cohRel_iff_mem_range_δ hS hpos (hφ_v_coc v) (hφ_v_coc w)
      (hN_bd_v v) (hN_bd_v w) (hbd_v v) (hbd_v w) (hg_v_prim v) (hg_v_prim w)]
    rw [Submodule.quotientRel_def]
    have hfun : (fun i => g_v v (N.f i 0) + g_v v (N.f i 1) +
        (g_v w (N.f i 0) + g_v w (N.f i 1))) = v - w := by
      ext i
      rw [hg_v_01 v i, hg_v_01 w i]
      exact (CharTwo.sub_eq_add (v i) (w i)).symm
    rw [hfun]
  let Φ : ((Fin N.r → K) ⧸ LinearMap.range N.δ) → KCl S K :=
    Quotient.lift toKCl fun v w hvw => Quotient.sound ((hrel_iff v w).mpr hvw)
  have hΦ_bij : Function.Bijective Φ := by
    constructor
    · refine Quotient.ind₂ fun v w h => Quotient.sound ?_
      exact (hrel_iff v w).mp (Quotient.exact h)
    · intro q
      obtain ⟨⟨φ, hφ_coc, h_bd, N_bd, hN_bd, hbd⟩, rfl⟩ := Quotient.exists_rep q
      let φ' : S → S → K := fun x y => φ x y + h_bd x + h_bd y
      have hφ'_coc : IsCoc φ' := by
        obtain ⟨N_c, hN_c, hc⟩ := hφ_coc
        refine ⟨N_c, hN_c, fun x y z hxy hyz hxz => ?_⟩
        dsimp [φ']
        rw [← hc x y z hxy hyz hxz]
        have hring : (φ x y + h_bd x + h_bd y) + (φ y z + h_bd y + h_bd z) =
            (φ x y + φ y z + h_bd x + h_bd z) + (h_bd y + h_bd y) := by ring
        rw [hring, CharTwo.add_self_eq_zero, add_zero]
      have hφ'_bd : ∀ x ∈ bd S, ∀ y ∈ bd S, (x, y) ∈ N_bd → φ' x y = 0 := by
        intro x hx y hy hxy
        dsimp [φ']
        rw [hbd x hx y hy hxy, CharTwo.neg_eq]
        have hring : h_bd x + h_bd y + h_bd x + h_bd y =
            (h_bd x + h_bd x) + (h_bd y + h_bd y) := by ring
        rw [hring, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
      have hrel_φ : CohRel φ' φ := by
        refine ⟨h_bd, univ, fun _ => univ_mem, fun x y _ => ?_⟩
        dsimp [φ']
        rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
        have hring : (φ x y + h_bd x + h_bd y) + φ x y =
            (φ x y + φ x y) + (h_bd y + h_bd x) := by ring
        rw [hring, CharTwo.add_self_eq_zero, zero_add]
      have hpbk_coc : IsCoc (pbk N.φ φ') := by
        obtain ⟨N_c, hN_c, hc⟩ := hφ'_coc
        refine ⟨(fun p : N.D × N.D => (N.φ p.1, N.φ p.2)) ⁻¹' N_c, fun z => ?_,
          fun a b c hab hbc hac => hc _ _ _ hab hbc hac⟩
        exact ((N.quotientMap_φ.continuous.comp continuous_fst).prodMk
          (N.quotientMap_φ.continuous.comp continuous_snd)).continuousAt.preimage_mem_nhds
          (hN_c (N.φ z))
      obtain ⟨g', hg'_prim⟩ := Surface.exists_prim_disc hpbk_coc N.isClosedDisc_D
      let v : Fin N.r → K := fun i => g' (N.f i 0) + g' (N.f i 1)
      have hrel_v : CohRel (φ_v v) φ' := by
        rw [N.cohRel_iff_mem_range_δ hS hpos (hφ_v_coc v) hφ'_coc
          (hN_bd_v v) hN_bd (hbd_v v) hφ'_bd (hg_v_prim v) hg'_prim]
        have hzero : (fun i => g_v v (N.f i 0) + g_v v (N.f i 1) +
            (g' (N.f i 0) + g' (N.f i 1))) = 0 := by
          ext i
          rw [hg_v_01 v i]
          exact CharTwo.add_self_eq_zero (v i)
        rw [hzero]
        exact Submodule.zero_mem _
      refine ⟨Submodule.Quotient.mk v, Quotient.sound (hrel_v.trans hrel_φ)⟩
  have hcard_quot : Nat.card ((Fin N.r → K) ⧸ LinearMap.range N.δ) =
      2 ^ Module.finrank K ((Fin N.r → K) ⧸ LinearMap.range N.δ) := by
    have h : Nat.card ((Fin N.r → K) ⧸ LinearMap.range N.δ) =
        Nat.card K ^ Module.finrank K ((Fin N.r → K) ⧸ LinearMap.range N.δ) :=
      Module.natCard_eq_pow_finrank
    rwa [Nat.card_zmod] at h
  have hfinrank_quot : Module.finrank K ((Fin N.r → K) ⧸ LinearMap.range N.δ) = 2 * a + b := by
    have h1 : 2 ^ Module.finrank K ((Fin N.r → K) ⧸ LinearMap.range N.δ) = 2 ^ (2 * a + b) := by
      rw [← hcard_quot, ← hkCl_eq, Nat.card_congr (Equiv.ofBijective Φ hΦ_bij)]
    exact Nat.pow_right_injective (le_refl 2) h1
  have hquot_add := Submodule.finrank_quotient_add_finrank (LinearMap.range N.δ)
  rw [Module.finrank_fin_fun, hfinrank_quot] at hquot_add
  have hrange_δ := N.finrank_range_δ hS hpos
  have hW_bd := N.finrank_W_bd hS hpos
  have hE := N.ncard_E_seamGraph hS hJ
  have hV : J.V = N.seamV := hJ.2.2
  rw [hV] at hE ⊢
  rw [hcuffs_eq] at hW_bd
  omega

end GraphMinor.GM07

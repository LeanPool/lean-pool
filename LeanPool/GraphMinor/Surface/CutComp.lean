/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutGlue
import Mathlib.Topology.LocalAtTarget

/-!
# Components after cutting

A surface is locally connected, so its components are open and closed. An open and closed part of a
surface is a surface.
If `ψ` cuts a connected surface along `F`, then each component of the cut surface meets the preimage
of `F`, so there are
at most two components when this preimage has two connected pieces (`cut_comps`). Boundary points
off the preimage of `F`
map to boundary points (`bd_of_bd`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe u

section basic

variable {S : Type u} [TopologicalSpace S]

theorem IsSurface.locallyConnected (hS : IsSurface S) : LocallyConnectedSpace S := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨U₀, O, j, k, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (hS.2.2 x).exists_chart
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
  have hjx := h6 h3
  have hk0 : k (j x) = x := h8 h3
  have hcont : ContinuousWithinAt k (O ∩ halfPlane) (j x) := h5 _ hjx
  have hW' : k ⁻¹' W ∈ 𝓝[O ∩ halfPlane] j x := hcont.preimage_mem_nhdsWithin (hW.mem_nhds
    (by rw [hk0]; exact hxW))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hW'
  obtain ⟨r', hr', hsub'⟩ := Metric.isOpen_iff.mp h2 _ hjx.1
  set s := min r r' with hs
  have hs0 : 0 < s := lt_min hr hr'
  have hball : Metric.ball (j x) s ⊆ Metric.ball (j x) r := Metric.ball_subset_ball
    (min_le_left _ _)
  have hball' : Metric.ball (j x) s ⊆ O := (Metric.ball_subset_ball (min_le_right _ _)).trans hsub'
  have hV : U₀ ∩ W ∩ j ⁻¹' Metric.ball (j x) s = k '' (Metric.ball (j x) s ∩ halfPlane) := by
    ext z
    constructor
    · rintro ⟨⟨hz, -⟩, hz2⟩
      exact ⟨j z, ⟨hz2, (h6 hz).2⟩, h8 hz⟩
    · rintro ⟨w, ⟨hw, hw2⟩, rfl⟩
      have hwO : w ∈ O ∩ halfPlane := ⟨hball' hw, hw2⟩
      refine ⟨⟨h7 hwO, hsub ⟨hball hw, hwO⟩⟩, ?_⟩
      change j (k w) ∈ Metric.ball (j x) s
      rw [h9 hwO]
      exact hw
  refine ⟨U₀ ∩ W ∩ j ⁻¹' Metric.ball (j x) s, fun z hz => hWU hz.1.2, ?_, ⟨⟨h3, hxW⟩,
    Metric.mem_ball_self hs0⟩, ?_⟩
  · exact (h4.mono inter_subset_left).isOpen_inter_preimage (h1.inter hW) Metric.isOpen_ball
  · rw [hV]
    have hconv : Convex ℝ (Metric.ball (j x) s ∩ halfPlane) := by
      refine (convex_ball _ _).inter ?_
      intro a ha b hb c d hc hd _
      have ha' : 0 ≤ a.re := ha
      have hb' : 0 ≤ b.re := hb
      change 0 ≤ (c • a + d • b).re
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      positivity
    refine ⟨⟨k (j x), j x, ⟨Metric.mem_ball_self hs0, hjx.2⟩, rfl⟩, ?_⟩
    exact hconv.isPreconnected.image k (h5.mono fun z hz => ⟨hball' hz.1, hz.2⟩)

theorem isManifoldPoint_of_embed {x : S} {U : Set S} (hU : IsOpen U) (hx : x ∈ U) {f : U
  → EuclideanHalfSpace 2}
    (hf : IsOpenEmbedding f) : IsManifoldPoint x :=
  ⟨U, range f, hU, hf.isOpen_range, hx, ⟨hf.isEmbedding.toHomeomorph⟩⟩

variable {W : Set S}

/-- A point of an open part is a manifold point of this part. -/
theorem isManifoldPoint_sub (hW : IsOpen W) {x : W} (hx : IsManifoldPoint x.1) : IsManifoldPoint x
  := by
  obtain ⟨U, V, hU, hV, hxU, ⟨e⟩⟩ := hx
  have hU' : IsOpen (Subtype.val ⁻¹' U : Set W) := hU.preimage continuous_subtype_val
  let f : (Subtype.val ⁻¹' U : Set W) → EuclideanHalfSpace 2 := fun z => (e ⟨z.1.1, z.2⟩).1
  refine isManifoldPoint_of_embed hU' hxU (f := f) ?_
  have h1 : IsOpenEmbedding (fun z : (Subtype.val ⁻¹' U : Set W) => (⟨z.1.1, z.2⟩ : U)) := by
    refine IsOpenEmbedding.of_continuous_injective_isOpenMap (by fun_prop) ?_ ?_
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      simpa [Subtype.ext_iff] using h
    · intro T hT
      obtain ⟨T', hT', rfl⟩ := isOpen_induced_iff.mp hT
      obtain ⟨T'', hT'', rfl⟩ := isOpen_induced_iff.mp hT'
      refine isOpen_induced_iff.mpr ⟨T'' ∩ W, hT''.inter hW, ?_⟩
      ext ⟨z, hz⟩
      constructor
      · rintro ⟨h2, h3⟩
        exact ⟨⟨⟨z, h3⟩, hz⟩, h2, rfl⟩
      · rintro ⟨⟨⟨y, h3⟩, h4⟩, h5, h6⟩
        simp only [Subtype.mk.injEq] at h6
        subst h6
        exact ⟨h5, h3⟩
  exact (hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding).comp h1

theorem isSurface_sub (hS : IsSurface S) (hW : IsClopen W) : IsSurface W := by
  obtain ⟨h1, h2, h3⟩ := id hS
  exact ⟨isCompact_iff_compactSpace.mp hW.1.isCompact, inferInstance,
    fun x => isManifoldPoint_sub hW.2 (h3 _)⟩

/-- A homeomorphism from the preimage of a subset of an open part. -/
theorem exists_homeo_sub (U : Set S) (hU : U ⊆ W) : Nonempty ((Subtype.val ⁻¹' U : Set W) ≃ₜ U)
  := by
  refine ⟨(IsEmbedding.subtypeVal.homeomorphImage (Subtype.val ⁻¹' U : Set W)).trans
    (Homeomorph.setCongr ?_)⟩
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr hU]

theorem isInteriorPoint_sub (hW : IsOpen W) {x : W} : IsInteriorPoint x ↔ IsInteriorPoint x.1 := by
  constructor
  · rintro ⟨U, hU, hx, ⟨e⟩⟩
    have h1 : Subtype.val ⁻¹' (Subtype.val '' U) = U := preimage_image_eq _ Subtype.val_injective
    have h2 : Subtype.val '' U ⊆ W := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    obtain ⟨e'⟩ := exists_homeo_sub (Subtype.val '' U) h2
    refine ⟨Subtype.val '' U, hW.isOpenMap_subtype_val _ hU, ⟨x, hx, rfl⟩,
      ⟨e'.symm.trans ((Homeomorph.setCongr h1).trans e)⟩⟩
  · intro h
    obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := h.exists_subset hW x.2
    obtain ⟨e'⟩ := exists_homeo_sub U hsub
    exact ⟨_, hU.preimage continuous_subtype_val, hx, ⟨e'.trans e⟩⟩

theorem mem_bd_sub (hW : IsOpen W) {x : W} : x ∈ bd W ↔ x.1 ∈ bd S :=
  not_congr (isInteriorPoint_sub hW)

theorem spaceComponents_eq : spaceComponents S = range connectedComponent := by
  ext C
  simp [spaceComponents, componentsIn, connectedComponentIn_univ]

end basic

section cut

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace Y] [T2Space S]
  {ψ : Y → S} {F : Set S}

/-- An open and closed part of the cut surface that contains the preimage of `F` is everything. -/
theorem eq_univ_of_cut [ConnectedSpace S] (hψ : IsCutting ψ F) {W : Set Y} (hW : IsClopen W)
  (hne : W.Nonempty)
    (hsub : ψ ⁻¹' F ⊆ W) : W = univ := by
  obtain ⟨h1, h2, h3, -, -⟩ := hψ
  have hc : IsClosed (ψ '' W) := (hW.1.isCompact.image h1).isClosed
  have hc' : IsClosed (ψ '' Wᶜ) := (hW.compl.1.isCompact.image h1).isClosed
  have hd : Disjoint (ψ '' W) (ψ '' Wᶜ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
    have h4 : y' ∈ ψ ⁻¹' Fᶜ := fun h5 => hy' (hsub h5)
    have h5 : y ∈ ψ ⁻¹' Fᶜ := by
      change ψ y ∈ Fᶜ
      rw [← he]
      exact h4
    exact hy' ((h3 h4 h5 he) ▸ hy)
  have hu : ψ '' W ∪ ψ '' Wᶜ = univ := by
    rw [← image_union, union_compl_self, image_univ, h2.range_eq]
  have hcl : IsClopen (ψ '' W) := ⟨hc, by
    have h9 : (ψ '' Wᶜ)ᶜ = ψ '' W := (eq_compl_iff_isCompl.mpr (IsCompl.mk hd
      (codisjoint_iff.mpr hu))).symm
    rw [← h9]
    exact hc'.isOpen_compl⟩
  have h6 := hcl.eq_univ (hne.image ψ)
  by_contra h7
  obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem _).mp h7
  obtain ⟨z, hz, he⟩ : ψ y ∈ ψ '' W := h6 ▸ mem_univ _
  exact Set.disjoint_left.mp hd ⟨z, hz, he⟩ ⟨y, hy, rfl⟩

/-- A connected cut surface. -/
theorem connected_of_cut [ConnectedSpace S] (hψ : IsCutting ψ F) (hS : IsSurface Y) {Q : Set Y}
  (hQ : IsPreconnected Q)
    (hQe : Q = ψ ⁻¹' F) (hne : Q.Nonempty) : ConnectedSpace Y := by
  have := hS.locallyConnected
  obtain ⟨x, hx⟩ := hne
  have hsub : ψ ⁻¹' F ⊆ connectedComponent x := by
    rw [← hQe]
    exact hQ.subset_connectedComponent hx
  have hu := eq_univ_of_cut hψ ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩ ⟨x,
    mem_connectedComponent⟩ hsub
  have h1 : IsConnected (univ : Set Y) := hu ▸ isConnected_connectedComponent
  exact connectedSpace_iff_univ.mpr h1

/-- The surface after cutting has one component, or two components that each hold one lift. -/
theorem cut_comps [ConnectedSpace S] (hψ : IsCutting ψ F) (hS : IsSurface Y) {X X' : Set Y}
  (hX : IsPreconnected X)
    (hX' : IsPreconnected X') (hu : X ∪ X' = ψ ⁻¹' F) {x y : Y} (hx : x ∈ X) (hy : y ∈ X') :
    ConnectedSpace Y ∨ ∃ W₁ W₂ : Set Y, W₁ ≠ W₂ ∧ spaceComponents Y = {W₁, W₂} ∧ X ⊆ W₁ ∧ X' ⊆ W₂
      ∧ IsClopen W₁ ∧ IsClopen W₂ ∧
      W₁ ∪ W₂ = univ ∧ Disjoint W₁ W₂ ∧ ConnectedSpace W₁ ∧ ConnectedSpace W₂ := by
  have := hS.locallyConnected
  have h1 : IsClopen (connectedComponent x) := ⟨isClosed_connectedComponent,
    isOpen_connectedComponent⟩
  have h2 : IsClopen (connectedComponent y) := ⟨isClosed_connectedComponent,
    isOpen_connectedComponent⟩
  have h3 := hX.subset_connectedComponent hx
  have h4 := hX'.subset_connectedComponent hy
  have hun : connectedComponent x ∪ connectedComponent y = univ :=
    eq_univ_of_cut hψ (h1.union h2) ⟨x, .inl mem_connectedComponent⟩ (by
      rw [← hu]
      exact union_subset_union h3 h4)
  by_cases he : connectedComponent x = connectedComponent y
  · left
    rw [← he, union_self] at hun
    have h5 : IsConnected (univ : Set Y) := hun ▸ isConnected_connectedComponent
    exact connectedSpace_iff_univ.mpr h5
  · right
    refine ⟨_, _, he, ?_, h3, h4, h1, h2, hun, connectedComponent_disjoint he, ?_, ?_⟩
    · rw [spaceComponents_eq]
      ext C
      constructor
      · rintro ⟨z, rfl⟩
        rcases (hun ▸ mem_univ z : z ∈ connectedComponent x ∪ connectedComponent y) with hz | hz
        · exact .inl (connectedComponent_eq hz).symm
        · exact .inr (connectedComponent_eq hz).symm
      · rintro (rfl | rfl)
        · exact ⟨x, rfl⟩
        · exact ⟨y, rfl⟩
    · exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    · exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- A boundary point off the preimage of `F` maps to a boundary point. -/
theorem bd_of_bd (hψ : IsCutting ψ F) (hF : IsClosed F) {z : Y} (hz : z ∈ bd Y)
  (hzF : ψ z ∉ F) : ψ z ∈ bd S := by
  intro hi
  apply hz
  obtain ⟨h1, h2, h3, -, -⟩ := hψ
  obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := hi.exists_subset hF.isOpen_compl hzF
  have hcl : IsClosedMap ψ := h1.isClosedMap
  have hbij : Bijective (U.restrictPreimage ψ) := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ he
      have he' : ψ a = ψ b := congrArg Subtype.val he
      exact Subtype.ext (h3 (fun h => hsub ha h) (fun h => hsub hb h) he')
    · rintro ⟨w, hw⟩
      obtain ⟨y, rfl⟩ := h2 w
      exact ⟨⟨y, hw⟩, rfl⟩
  have hh : IsHomeomorph (U.restrictPreimage ψ) :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨h1.restrictPreimage,
      hcl.restrictPreimage U, hbij⟩
  exact ⟨ψ ⁻¹' U, hU.preimage h1, hx, ⟨hh.homeomorph.trans e⟩⟩

end cut

/-- A curve in the boundary, whose inside avoids the preimage of `F`, joins two points of the same
cuff. -/
theorem same_cuff_of_curve {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace
  Y] [T2Space S]
    {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F) (hF : IsClosed F) {γ : ℝ → Y} (hγ : ContinuousOn γ
      (Icc 0 1))
    (hb : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ bd Y) (hi : ∀ u ∈ Ioo (0 : ℝ) 1, ψ (γ u) ∉ F) (h0 : ψ
      (γ 0) ∈ bd S) (h1 : ψ (γ 1) ∈ bd S) :
    connectedComponentIn (bd S) (ψ (γ 0)) = connectedComponentIn (bd S) (ψ (γ 1)) := by
  have hcont : ContinuousOn (fun u => ψ (γ u)) (Icc 0 1) := hψ.1.comp_continuousOn hγ
  have hconn : IsPreconnected ((fun u => ψ (γ u)) '' Icc (0 : ℝ) 1) := isPreconnected_Icc.image _
    hcont
  have hs : (fun u => ψ (γ u)) '' Icc (0 : ℝ) 1 ⊆ bd S := by
    rintro _ ⟨u, hu, rfl⟩
    rcases eq_or_lt_of_le hu.1 with rfl | h2
    · exact h0
    rcases eq_or_lt_of_le hu.2 with rfl | h3
    · exact h1
    exact bd_of_bd hψ hF (hb u hu) (hi u ⟨h2, h3⟩)
  have hz0 : ψ (γ 0) ∈ (fun u => ψ (γ u)) '' Icc (0 : ℝ) 1 := ⟨0, by simp, rfl⟩
  have hz1 : ψ (γ 1) ∈ (fun u => ψ (γ u)) '' Icc (0 : ℝ) 1 := ⟨1, by simp, rfl⟩
  have h2 := hconn.subset_connectedComponentIn hz0 hs hz1
  exact connectedComponentIn_eq h2

end GraphMinor.Surface

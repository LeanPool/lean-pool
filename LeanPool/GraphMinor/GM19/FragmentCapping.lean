/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentCollapse
public import LeanPool.GraphMinor.GM19.CutFragment
public import LeanPool.GraphMinor.Surface.DiscMerge
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The capping of a surface depends only on its interior

Let `W` be a surface and `T` a closed surface. Suppose that the inside of `W` is homeomorphic to `T`
without a finite set `P`.
Then each capping of `W` is homeomorphic to `T`, and `W` has `|P|` cuffs (`capping_homeo`). The
reason: by
`exists_collapse` the inside of `W` is also a capping of `W` without a finite set of points, one
point for each cuff. And a
homeomorphism between two closed surfaces without finite sets extends over these sets
(`exists_homeomorph_of_punctures`),
since a small punctured neighbourhood of a point is connected.

This is the tool that identifies the capping of a fragment, also when the fragment has a corner, or
two sides of a cut
that touches a cuff.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

section Oph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous open injective map on an open set is a partial homeomorphism. -/
theorem exists_oph [Nonempty X] {f : X → Y} {s : Set X} {t : Set Y} (hs : IsOpen s)
  (hf : ContinuousOn f s)
    (hi : InjOn f s) (ho : ∀ u ⊆ s, IsOpen u → IsOpen (f '' u)) (ht : f '' s = t) :
    ∃ e : OpenPartialHomeomorph X Y, e.source = s ∧ e.target = t ∧ EqOn e f s := by
  classical
  let E : PartialEquiv X Y := hi.toPartialEquiv f s
  have hE : E.source = s := rfl
  have hEt : E.target = t := by rw [← ht]; rfl
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict E hf ?_ hs, hE, hEt, fun _ _ ↦ rfl⟩
  intro u hu
  have := ho (Subtype.val '' u) (by rintro _ ⟨x, -, rfl⟩; exact x.2) (hs.isOpenMap_subtype_val _ hu)
  rw [image_image] at this
  exact this

theorem IsCollapse.exists_oph [T2Space X] [CompactSpace X] [Nonempty X] {c : C(X, X)} {A P : Set X}
  (h : IsCollapse c A P) :
    ∃ e : OpenPartialHomeomorph X X, e.source = Aᶜ ∧ e.target = Pᶜ ∧ EqOn e c Aᶜ := by
  have hA : A = c ⁻¹' P := Subset.antisymm (fun x hx ↦ h.mapsTo hx) h.preimage
  have hcl : IsClosed A := hA ▸ h.finite.isClosed.preimage c.continuous
  refine GM19.exists_oph hcl.isOpen_compl c.continuous.continuousOn h.injOn (fun u hu huo ↦ ?_) ?_
  · have hcm : IsClosedMap c := c.continuous.isClosedMap
    have : c '' u = (c '' uᶜ)ᶜ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
        by_cases hzA : z ∈ A
        · exact hu hx (hA ▸ (show c x ∈ P from he ▸ h.mapsTo hzA))
        · exact hz (h.injOn hzA (hu hx) he ▸ hx)
      · intro hy
        obtain ⟨x, rfl⟩ := h.surjective y
        by_cases hxu : x ∈ u
        · exact ⟨x, hxu, rfl⟩
        · exact absurd ⟨x, hxu, rfl⟩ hy
    rw [this]
    exact (hcm _ huo.isClosed_compl).isOpen_compl
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      exact hx (h.preimage hy)
    · intro hy
      obtain ⟨x, rfl⟩ := h.surjective y
      exact ⟨x, fun hx ↦ hy (h.mapsTo hx), rfl⟩

end Oph

section Punctures

variable {T : Type*} [TopologicalSpace T]

theorem isPreconnected_ball_sdiff : IsPreconnected (ball (0 : ℂ) 1 \ {0}) := by
  have hs : IsPreconnected (sphere (0 : ℂ) 1) := isPreconnected_sphere
    (by simp [Complex.rank_real_complex]) 0 1
  have h := (isPreconnected_Ioo (a := (0 : ℝ)) (b := 1)).prod hs
  have hc : Continuous fun x : ℝ × ℂ ↦ (x.1 : ℂ) * x.2 := by fun_prop
  convert h.image _ hc.continuousOn using 1
  ext z
  constructor
  · rintro ⟨h₁, h₂⟩
    have hz : z ≠ 0 := h₂
    have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    refine ⟨(‖z‖, z / ‖z‖), ⟨⟨norm_pos_iff.2 hz, by simpa using h₁⟩, ?_⟩, ?_⟩
    · simp [hz]
    · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hz'
      field_simp
  · rintro ⟨⟨r, w⟩, ⟨⟨h₁, h₂⟩, hw⟩, rfl⟩
    have h₁' : 0 < r := h₁
    have h₂' : r < 1 := h₂
    have hw' : ‖w‖ = 1 := by simpa using hw
    have hr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg h₁'.le]
    refine ⟨?_, ?_⟩
    · change (r : ℂ) * w ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_mul, hr, hw', mul_one]
      exact h₂'
    · intro h0
      have h0' : (r : ℂ) * w = 0 := h0
      have := congrArg norm h0'
      rw [norm_mul, hr, hw', mul_one, norm_zero] at this
      linarith

/-- An interior point has small neighbourhoods that stay connected when the point is removed. -/
theorem exists_punctured {x : T} (hx : IsInteriorPoint x) {W : Set T} (hW : W ∈ 𝓝 x) :
    ∃ N, IsOpen N ∧ x ∈ N ∧ N ⊆ W ∧ IsPreconnected (N \ {x}) ∧ (N \ {x}).Nonempty := by
  obtain ⟨U, h, g, c, hU, h0⟩ := hx.exists_ballChart isOpen_interior (mem_interior_iff_mem_nhds.2
    hW) one_pos
  have h0m : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hxU : x ∈ U := h0 ▸ c.gm h0m
  have heq : U \ {x} = g '' (ball 0 1 \ {0}) := by
    ext y
    constructor
    · rintro ⟨hy, hne⟩
      refine ⟨h y, ⟨c.hm hy, fun h1 ↦ hne ?_⟩, c.gh hy⟩
      rw [← c.gh hy, h1, h0]
      rfl
    · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
      refine ⟨c.gm hz, fun he ↦ hz0 ?_⟩
      have h1 : h (g z) = z := c.hg hz
      have h2 : h (g 0) = 0 := c.hg h0m
      rw [show g z = g 0 from he.trans h0.symm] at h1
      exact h1.symm.trans h2
  refine ⟨U, c.isOpen, hxU, hU.trans interior_subset, ?_, ?_⟩
  · rw [heq]
    exact isPreconnected_ball_sdiff.image _ (c.gc.mono sdiff_subset)
  · rw [heq]
    refine ⟨g (1 / 2), _, ⟨?_, ?_⟩, rfl⟩
    · simp; norm_num
    · simp

theorem neBot_punctured (hT : ∀ x : T, IsInteriorPoint x) (x : T) : (𝓝[≠] x).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro W hW
  obtain ⟨N, -, -, hN, -, ⟨y, hy, hne⟩⟩ := exists_punctured (hT x) hW
  exact ⟨y, hN hy, hne⟩

theorem dense_compl_finite [T1Space T] (hT : ∀ x : T, IsInteriorPoint x) {P : Set T}
  (hP : P.Finite) : Dense Pᶜ := by
  have := neBot_punctured hT
  rw [compl_eq_univ_sdiff]
  exact dense_univ.sdiff_finite hP

variable {T₂ : Type*} [TopologicalSpace T₂]

/-- Near a removed point `p`, the map `e` stays near one removed point of the target. -/
theorem exists_eventually_mem [T2Space T] [CompactSpace T₂]
  (hT : ∀ x : T, IsInteriorPoint x) {P₁ : Set T} {P₂ : Set T₂}
    (hP₁ : P₁.Finite) (e : OpenPartialHomeomorph T T₂) (hs : e.source = P₁ᶜ) (ht : e.target
      = P₂ᶜ) {p : T}
    (hp : p ∈ P₁) {U : T₂ → Set T₂} (hU : ∀ q ∈ P₂, IsOpen (U q) ∧ q ∈ U q)
      (hd : P₂.PairwiseDisjoint U) :
    ∃ q ∈ P₂, ∀ᶠ x in 𝓝[P₁ᶜ] p, e x ∈ U q := by
  classical
  set O : Set T₂ := ⋃ q ∈ P₂, U q with hO
  have hOo : IsOpen O := isOpen_biUnion fun q hq ↦ (hU q hq).1
  have hsubt : Oᶜ ⊆ e.target := by
    rw [ht]
    intro y hy hq
    exact hy (mem_biUnion hq (hU y hq).2)
  have hK : IsCompact (e.symm '' Oᶜ) := hOo.isClosed_compl.isCompact.image_of_continuousOn
    (e.continuousOn_symm.mono hsubt)
  have hKs : e.symm '' Oᶜ ⊆ P₁ᶜ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hs]
    exact e.map_target (hsubt hy)
  have hW : (e.symm '' Oᶜ)ᶜ ∩ (P₁ \ {p})ᶜ ∈ 𝓝 p := by
    refine inter_mem (hK.isClosed.isOpen_compl.mem_nhds fun h ↦ hKs h hp) ?_
    exact (hP₁.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 rfl
  obtain ⟨N, hNo, hpN, hNW, hNc, ⟨a₀, ha₀⟩⟩ := exists_punctured (hT p) hW
  have hA : N \ {p} ⊆ P₁ᶜ := fun x hx hxP ↦ (hNW hx.1).2 ⟨hxP, hx.2⟩
  have hAO : e '' (N \ {p}) ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hn
    refine (hNW hx.1).1 ⟨e x, hn, ?_⟩
    exact e.left_inv (hs ▸ hA hx)
  obtain ⟨q₀, hq₀, ha⟩ := mem_iUnion₂.1 (hAO ⟨a₀, ha₀, rfl⟩)
  have hconn : IsPreconnected (e '' (N \ {p})) :=
    hNc.image _ (e.continuousOn.mono (hs ▸ hA))
  have hsub : e '' (N \ {p}) ⊆ U q₀ := by
    refine hconn.subset_left_of_subset_union (hU q₀ hq₀).1 (v := ⋃ q ∈ P₂ \ {q₀}, U q)
      (isOpen_biUnion fun q hq ↦ (hU q hq.1).1) ?_ (fun y hy ↦ ?_) ⟨_, ⟨a₀, ha₀, rfl⟩, ha⟩
    · refine disjoint_iUnion₂_right.2 fun q hq ↦ ?_
      exact hd hq₀ hq.1 (fun h ↦ hq.2 h.symm)
    · obtain ⟨q, hq, hy'⟩ := mem_iUnion₂.1 (hAO hy)
      by_cases hqe : q = q₀
      · exact Or.inl (hqe ▸ hy')
      · exact Or.inr (mem_biUnion (show q ∈ P₂ \ {q₀} from ⟨hq, hqe⟩) hy')
  refine ⟨q₀, hq₀, ?_⟩
  have hmem : N ∩ P₁ᶜ ∈ 𝓝[P₁ᶜ] p := by
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (hNo.mem_nhds hpN)
  refine mem_of_superset hmem fun x hx ↦ hsub ⟨x, ⟨hx.1, fun h ↦ hx.2 (h ▸ hp)⟩, rfl⟩

/-- Near a removed point `p`, the map `e` tends to a removed point of the target. -/
theorem exists_tendsto_puncture [T2Space T] [T2Space T₂] [CompactSpace T₂]
  (hT : ∀ x : T, IsInteriorPoint x) {P₁ : Set T} {P₂ : Set T₂}
    (hP₁ : P₁.Finite) (hP₂ : P₂.Finite) (e : OpenPartialHomeomorph T T₂) (hs : e.source = P₁ᶜ)
      (ht : e.target = P₂ᶜ) {p : T}
    (hp : p ∈ P₁) : ∃ q ∈ P₂, Tendsto e (𝓝[P₁ᶜ] p) (𝓝 q) := by
  classical
  have : (𝓝[P₁ᶜ] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 ((dense_compl_finite hT hP₁) p)
  obtain ⟨U, hU, hd⟩ := hP₂.t2_separation
  obtain ⟨q, hq, hev⟩ := exists_eventually_mem hT hP₁ e hs ht hp (U := U) (fun q _ ↦ ⟨(hU q).2,
    (hU q).1⟩) hd
  refine ⟨q, hq, tendsto_nhds.2 fun V hV hqV ↦ ?_⟩
  let U' : T₂ → Set T₂ := fun r ↦ if r = q then U r ∩ V else U r
  have hsub : ∀ r, U' r ⊆ U r := fun r ↦ by
    by_cases h : r = q
    · simp only [U', ite_eq_left h]
      exact inter_subset_left
    · simp only [U', ite_eq_right h]
      rfl
  have hU' : ∀ r ∈ P₂, IsOpen (U' r) ∧ r ∈ U' r := fun r _ ↦ by
    by_cases h : r = q
    · simp only [U', ite_eq_left h]
      exact ⟨(hU r).2.inter hV, (hU r).1, h ▸ hqV⟩
    · simp only [U', ite_eq_right h]
      exact ⟨(hU r).2, (hU r).1⟩
  obtain ⟨r, hr, hev'⟩ := exists_eventually_mem hT hP₁ e hs ht hp hU'
    (fun a ha b hb hab ↦ (hd ha hb hab).mono (hsub a) (hsub b))
  have hrq : r = q := by
    by_contra hne
    obtain ⟨x, hx, hx'⟩ := (hev.and hev').exists
    exact disjoint_left.1 (hd hq hr (Ne.symm hne)) hx (hsub r hx')
  subst hrq
  refine hev'.mono fun x hx ↦ ?_
  simp only [U', ite_true] at hx
  exact hx.2

theorem tendsto_of_source {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y) {A : Set X}
    (hA : e.source = A) (hX : ∀ x ∉ A, ∃ y, Tendsto e (𝓝[A] x) (𝓝 y)) (x : X) : ∃ y, Tendsto e
      (𝓝[A] x) (𝓝 y) := by
  by_cases hx : x ∈ A
  · exact ⟨e x, (e.continuousOn x (hA ▸ hx)).mono_left (by rw [hA])⟩
  · exact hX x hx

/-- A homeomorphism between two closed surfaces without finite sets extends to a homeomorphism of
the closed surfaces. -/
theorem exists_homeomorph_of_punctures [T2Space T] [T2Space T₂] [CompactSpace T] [CompactSpace T₂]
  (hT : ∀ x : T, IsInteriorPoint x)
    (hT₂ : ∀ x : T₂, IsInteriorPoint x) {P₁ : Set T} {P₂ : Set T₂} (hP₁ : P₁.Finite)
      (hP₂ : P₂.Finite)
    (e : OpenPartialHomeomorph T T₂) (hs : e.source = P₁ᶜ) (ht : e.target = P₂ᶜ) :
    ∃ f : T ≃ₜ T₂, EqOn f e P₁ᶜ ∧ f '' P₁ = P₂ := by
  classical
  have hd₁ := dense_compl_finite hT hP₁
  have hd₂ := dense_compl_finite hT₂ hP₂
  have h₁ : ∀ x, ∃ y, Tendsto e (𝓝[P₁ᶜ] x) (𝓝 y) := tendsto_of_source e hs fun x hx ↦ by
    obtain ⟨q, -, h⟩ := exists_tendsto_puncture hT hP₁ hP₂ e hs ht (not_not.1 hx)
    exact ⟨q, h⟩
  have h₂ : ∀ x, ∃ y, Tendsto e.symm (𝓝[P₂ᶜ] x) (𝓝 y) := tendsto_of_source e.symm
    (by simpa using ht) fun x hx ↦ by
    obtain ⟨q, -, h⟩ := exists_tendsto_puncture hT₂ hP₂ hP₁ e.symm (by simpa using ht)
      (by simpa using hs) (not_not.1 hx)
    exact ⟨q, h⟩
  have hc₁ : Continuous (extendFrom P₁ᶜ e) := continuous_extendFrom hd₁ h₁
  have hc₂ : Continuous (extendFrom P₂ᶜ e.symm) := continuous_extendFrom hd₂ h₂
  have he₁ : ∀ x ∈ P₁ᶜ, extendFrom P₁ᶜ e x = e x := extendFrom_extends (hs ▸ e.continuousOn)
  have he₂ : ∀ x ∈ P₂ᶜ, extendFrom P₂ᶜ e.symm x = e.symm x := extendFrom_extends
    (ht ▸ e.continuousOn_symm)
  have hl : ∀ x, extendFrom P₂ᶜ e.symm (extendFrom P₁ᶜ e x) = x := by
    refine congrFun (Continuous.ext_on hd₁ (hc₂.comp hc₁) continuous_id fun x hx ↦ ?_)
    rw [he₁ x hx, he₂ _ (ht ▸ e.map_source (hs ▸ hx)), e.left_inv (hs ▸ hx)]
  have hr : ∀ x, extendFrom P₁ᶜ e (extendFrom P₂ᶜ e.symm x) = x := by
    refine congrFun (Continuous.ext_on hd₂ (hc₁.comp hc₂) continuous_id fun x hx ↦ ?_)
    rw [he₂ x hx, he₁ _ (hs ▸ e.map_target (ht ▸ hx)), e.right_inv (ht ▸ hx)]
  have hm₁ : ∀ p ∈ P₁, extendFrom P₁ᶜ e p ∈ P₂ := fun p hp ↦ by
    obtain ⟨q, hq, h⟩ := exists_tendsto_puncture hT hP₁ hP₂ e hs ht hp
    rw [extendFrom_eq (hd₁ p) h]
    exact hq
  have hm₂ : ∀ p ∈ P₂, extendFrom P₂ᶜ e.symm p ∈ P₁ := fun p hp ↦ by
    obtain ⟨q, hq, h⟩ := exists_tendsto_puncture hT₂ hP₂ hP₁ e.symm (by simpa using ht)
      (by simpa using hs) hp
    rw [extendFrom_eq (hd₂ p) h]
    exact hq
  refine ⟨⟨⟨_, _, hl, hr⟩, hc₁, hc₂⟩, he₁, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact hm₁ p hp
  · intro q hq
    exact ⟨_, hm₂ q hq, hr q⟩

end Punctures

section Capping



variable {W What : Type} [TopologicalSpace W] [T2Space W] [TopologicalSpace What]

omit [T2Space W] in
/-- The inside of a surface is a capping without finitely many points, one point for each cuff. -/
theorem exists_cap_chart [Nonempty W] (hW : IsSurface W) (cap : IsCappedSurface W What) :
    ∃ (e : OpenPartialHomeomorph W What) (P : Set What), P.Finite ∧ e.source = (bd W)ᶜ ∧ e.target
      = Pᶜ ∧
      P.ncard = numCuffs W := by
  classical
  have hT := cap.isClosedSurface
  have : T2Space What := hT.2.1
  have : CompactSpace What := hT.1
  have hfc : (cuffs W).Finite := (cuff_statement W hW).2.1
  let 𝓐 : Set (Set What) := (fun Θ ↦ closure (cap.cuffDisc Θ)) '' cuffs W
  have hne : ∀ Θ ∈ cuffs W, (closure (cap.cuffDisc Θ)).Nonempty := fun Θ hΘ ↦
    (cap.cuffDisc_closedDisc Θ hΘ).nonempty_discInt.mono (discInt_subset _)
  have hinj : InjOn (fun Θ ↦ closure (cap.cuffDisc Θ)) (cuffs W) := fun Θ₁ h₁ Θ₂ h₂ he ↦ by
    by_contra hn
    have hd := cap.cuffDisc_disjoint Θ₁ h₁ Θ₂ h₂ hn
    simp only at he
    rw [← he, disjoint_self] at hd
    exact (hne Θ₁ h₁).ne_empty (by simpa using hd)
  have hpd : 𝓐.PairwiseDisjoint id := by
    rintro _ ⟨Θ₁, h₁, rfl⟩ _ ⟨Θ₂, h₂, rfl⟩ hn
    exact cap.cuffDisc_disjoint Θ₁ h₁ Θ₂ h₂ fun h ↦ hn (h ▸ rfl)
  have : Nonempty What := cap.connected.toNonempty
  obtain ⟨c, P, q, hc, -, rfl, hqi⟩ := exists_collapse hT (hfc.image _)
    (by rintro _ ⟨Θ, hΘ, rfl⟩; exact cap.cuffDisc_closedDisc Θ hΘ) hpd
  have hU : (⋃₀ 𝓐)ᶜ = cap.emb '' (bd W)ᶜ := by
    rw [← cap.compl_eq_image, sUnion_image]
  have hUo : IsOpen (⋃₀ 𝓐)ᶜ := by
    refine (Set.Finite.isClosed_sUnion (hfc.image _) ?_).isOpen_compl
    rintro _ ⟨Θ, -, rfl⟩
    exact isClosed_closure
  have ho : ∀ u ⊆ (bd W)ᶜ, IsOpen u → IsOpen (cap.emb '' u) := fun u hu huo ↦ by
    obtain ⟨O, hO, rfl⟩ := cap.isEmbedding.isInducing.isOpen_iff.1 huo
    have : cap.emb '' (cap.emb ⁻¹' O) = O ∩ (⋃₀ 𝓐)ᶜ := by
      apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨hx, hU ▸ mem_image_of_mem _ (hu hx)⟩
      · rintro y ⟨hy, hy'⟩
        rw [hU] at hy'
        obtain ⟨x, -, rfl⟩ := hy'
        exact ⟨x, hy, rfl⟩
    rw [this]
    exact hO.inter hUo
  obtain ⟨e₁, hs₁, ht₁, -⟩ := GM19.exists_oph (f := cap.emb) (cuff_statement W hW).1.isOpen_compl
    cap.isEmbedding.continuous.continuousOn cap.isEmbedding.injective.injOn ho hU.symm
  obtain ⟨e₂, hs₂, ht₂, -⟩ := hc.exists_oph
  refine ⟨e₁.trans' e₂ (ht₁.trans hs₂.symm), q '' 𝓐, (hfc.image _).image _, hs₁, ht₂, ?_⟩
  rw [numCuffs, InjOn.ncard_image hqi, InjOn.ncard_image hinj]

omit [T2Space W] in
/-- **The capping depends only on the inside.** If the inside of `W` is a closed surface `T` without
a finite set `P`, then
each capping of `W` is homeomorphic to `T`, and `W` has `|P|` cuffs. -/
theorem capping_homeo {T : Type*} [TopologicalSpace T] [Nonempty W] (hW : IsSurface W)
  (cap : IsCappedSurface W What)
    (hT : IsClosedSurface T) {P : Set T} (hP : P.Finite) (e : OpenPartialHomeomorph W T)
      (hs : e.source = (bd W)ᶜ)
    (ht : e.target = Pᶜ) : Nonempty (What ≃ₜ T) ∧ numCuffs W = P.ncard := by
  obtain ⟨e₁, Q, hQ, hs₁, ht₁, hn⟩ := exists_cap_chart hW cap
  have hC := cap.isClosedSurface
  have : T2Space What := hC.2.1
  have : CompactSpace What := hC.1
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  obtain ⟨f, -, hf⟩ := exists_homeomorph_of_punctures hC.2.2 hT.2.2 hQ hP (e₁.symm.trans' e
    (by simp [hs₁, hs]))
    (by simp [ht₁]) (by simp [ht])
  refine ⟨⟨f⟩, ?_⟩
  rw [← hn, ← hf, f.injective.injOn.ncard_image]

end Capping

end GraphMinor.GM19

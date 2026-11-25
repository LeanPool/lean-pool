/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentBridge

/-!
# The fragment outside a cell

Let `Z` be a closed set of `Σ̂` that holds `K` and collapses to a point (`IsCell`). Let `G` be an
open part of `Z` such that the rest of
`Z` lies in `K` and in the pasted discs. Then one fragment has image `Σ` without `G`, and it caps to
`Σ̂`. Each pasted disc outside `Z`
adds a cuff to the fragment, and the set `Z` adds one more. So if `Z` holds two pasted discs, the
fragment has fewer cuffs than `Σ`
(`exists_outer_fragment`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

section Frontier

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
/-- Each point of the boundary of a closed disc is a limit of points outside the disc. -/
theorem discBd_subset_closure_compl (hT : IsClosedSurface T) {D : Set T}
  (_hD : IsClosedDisc D) : discBd D ⊆ closure Dᶜ := by
  intro p hp
  rw [closure_compl]
  intro hi
  have := subset_discInt_of_isOpen (fun y _ ↦ hT.2.2 y) isOpen_interior interior_subset hi
  exact this.2 hp

/-- A line of a closed surface holds no open set, so each of its points is a limit of points off the
line. -/
theorem line_subset_closure_compl (hT : IsClosedSurface T) {L : Set T} {a b : T}
  (hl : IsLineWithEnds L a b) : L ⊆ closure Lᶜ := by
  intro p hp
  rw [closure_compl]
  intro hi
  have hO : IsOpen (interior L) := isOpen_interior
  have : LocallyConnectedSpace T := IsSurface.locallyConnected hT.isSurface
  set G := connectedComponentIn (interior L) p with hG
  have hGo : IsOpen G := hO.connectedComponentIn
  have hGc : IsPreconnected G := isPreconnected_connectedComponentIn
  have hGL : G ⊆ L := (connectedComponentIn_subset _ _).trans interior_subset
  have hpG : p ∈ G := mem_connectedComponentIn hi
  obtain ⟨f, -, -⟩ := hl
  let g : unitInterval → T := fun t ↦ (f t).1
  have hgi : IsEmbedding g := IsEmbedding.subtypeVal.comp f.isEmbedding
  have hrg : ∀ x ∈ L, ∃ t, g t = x := fun x hx ↦ ⟨f.symm ⟨x, hx⟩, by simp [g]⟩
  have hdn := dense_compl_finite hT.2.2 (finite_singleton p)
  obtain ⟨q, hqG, hqp⟩ := hdn.inter_open_nonempty G hGo ⟨p, hpG⟩
  obtain ⟨s, rfl⟩ := hrg p hp
  obtain ⟨t, rfl⟩ := hrg q (hGL hqG)
  have hst : s ≠ t := fun h ↦ hqp (by rw [h]; rfl)
  have key : ∀ {s t : unitInterval}, s < t → g s ∈ G → g t ∈ G → False := by
    intro s t hlt hs ht
    obtain ⟨m, hsm, hmt⟩ := exists_between hlt
    have him : ∀ {W : Set T}, W ⊆ range g → g '' (g ⁻¹' W) = W := fun h ↦
      image_preimage_eq_of_subset h
    have hGr : G ⊆ range g := fun x hx ↦ hrg x (hGL hx)
    have hJ : IsPreconnected (g ⁻¹' G) := by
      rw [← hgi.isInducing.isPreconnected_image, him hGr]
      exact hGc
    have hmG : g m ∈ G := hJ.ordConnected.out hs ht ⟨hsm.le, hmt.le⟩
    have hJ' : IsPreconnected (g ⁻¹' (G \ {g m})) := by
      rw [← hgi.isInducing.isPreconnected_image, him (sdiff_subset.trans hGr)]
      exact isPreconnected_sdiff_point hT hGo hGc _
    have hmem := hJ'.ordConnected.out (x := s) (y := t)
      ⟨hs, fun h ↦ hsm.ne (hgi.injective h)⟩ ⟨ht, fun h ↦ hmt.ne' (hgi.injective h)⟩ ⟨hsm.le,
        hmt.le⟩
    exact hmem.2 rfl
  rcases lt_or_gt_of_ne hst with h | h
  · exact key h hpG hqG
  · exact key h hqG hpG

omit [T2Space T] in
/-- If `Z = Z₁ ∪ Z₂`, a point of `Z₁` off `Z₂` that is a limit of points off `Z₁` is a limit of
points off `Z`. -/
theorem mem_closure_compl_union {Z₁ Z₂ : Set T} (h₂ : IsClosed Z₂) {p : T} (hp : p ∈ closure Z₁ᶜ)
  (hn : p ∉ Z₂) :
    p ∈ closure (Z₁ ∪ Z₂)ᶜ := by
  rw [_root_.mem_closure_iff] at hp ⊢
  intro O hO hpO
  obtain ⟨w, hw, hwn⟩ := hp (O ∩ Z₂ᶜ) (hO.inter h₂.isOpen_compl) ⟨hpO, hn⟩
  exact ⟨w, hw.1, fun h ↦ h.elim hwn hw.2⟩

omit [T2Space T] in
/-- The closure of the complement of a closed disc is the complement of the inside of the disc. -/
theorem closure_compl_disc (hT : IsClosedSurface T) {D : Set T} (hD : IsClosedDisc D) : closure Dᶜ
  = (discInt D)ᶜ := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  apply Subset.antisymm
  · refine closure_minimal ?_ (hD.isOpen_discInt hman).isClosed_compl
    exact fun x hx hi ↦ hx (discInt_subset D hi)
  · intro x hx
    by_cases hxD : x ∈ D
    · exact discBd_subset_closure_compl hT hD (by
        by_contra hn
        exact hx ⟨hxD, hn⟩)
    · exact subset_closure hxD

/-- A connected set that meets the closed disc `D` only in `b` and is not inside `D` meets it in a
boundary point. -/
theorem mem_discBd_of_cross (hT : IsClosedSurface T) {D L : Set T} (hD : IsClosedDisc D)
  (hc : IsPreconnected L) {a b : T} (ha : a ∈ L)
    (haD : a ∉ D) (hb : b ∈ L) (hL : L ∩ D = {b}) : b ∈ discBd D := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  by_contra hn
  have hbD : b ∈ D := by
    have : b ∈ L ∩ D := by rw [hL]; rfl
    exact this.2
  have hsub : L ⊆ discInt D ∪ Dᶜ := by
    intro x hx
    by_cases hxD : x ∈ D
    · have : x ∈ L ∩ D := ⟨hx, hxD⟩
      rw [hL] at this
      exact Or.inl (by rw [mem_singleton_iff.1 this]; exact ⟨hbD, hn⟩)
    · exact Or.inr hxD
  have hdj : Disjoint (discInt D) Dᶜ := disjoint_left.2 fun x hx hc ↦ hc (discInt_subset D hx)
  have := hc.subset_left_of_subset_union (hD.isOpen_discInt hman) hD.isClosed.isOpen_compl hdj hsub
    ⟨b, hb, hbD, hn⟩
  exact haD (discInt_subset D (this ha))

omit [T2Space T] in
/-- A point on the boundary of a closed disc, off a closed set `W`, is a limit of points off both.
-/
theorem discBd_closure_compl_union (hT : IsClosedSurface T) {D W : Set T} (hD : IsClosedDisc D)
  (hW : IsClosed W) {p : T}
    (hp : p ∈ discBd D) (hn : p ∉ W) : p ∈ closure (D ∪ W)ᶜ :=
  mem_closure_compl_union hW (discBd_subset_closure_compl hT hD hp) hn

theorem frontier_touch (hT : IsClosedSurface T) {D₁ D₂ : Set T} (h₁ : IsClosedDisc D₁)
  (h₂ : IsClosedDisc D₂) {a : T}
    (ha : D₁ ∩ D₂ = {a}) : (D₁ ∪ D₂) \ (discInt D₁ ∪ discInt D₂) ⊆ closure (D₁ ∪ D₂)ᶜ := by
  have hA : ∀ {x}, x ∈ D₁ → x ∈ D₂ → x = a := fun hx hy ↦ by
    have : _ ∈ D₁ ∩ D₂ := ⟨hx, hy⟩
    rwa [ha] at this
  have k₁ : ∀ {q}, q ∈ discBd D₁ → q ≠ a → q ∈ closure (D₁ ∪ D₂)ᶜ := fun hq hne ↦
    discBd_closure_compl_union hT h₁ h₂.isClosed hq fun h ↦ hne (hA (Surface.discBd_subset _ hq) h)
  have k₂ : ∀ {q}, q ∈ discBd D₂ → q ≠ a → q ∈ closure (D₁ ∪ D₂)ᶜ := fun hq hne ↦ by
    rw [union_comm]
    exact discBd_closure_compl_union hT h₂ h₁.isClosed hq fun h ↦ hne (hA h
      (Surface.discBd_subset _ hq))
  rintro p ⟨hp, hn⟩
  have hb : p ∈ discBd D₁ ∨ p ∈ discBd D₂ := by
    rcases hp with h | h
    · refine Or.inl ?_
      by_contra hb
      exact hn (Or.inl ⟨h, hb⟩)
    · refine Or.inr ?_
      by_contra hb
      exact hn (Or.inr ⟨h, hb⟩)
  rcases hb with h | h
  · by_cases hpa : p = a
    · refine closure_minimal ?_ isClosed_closure (mem_closure_oArc_sdiff h₁.isOArc_discBd h)
      rintro q ⟨hq, hqn⟩
      exact k₁ hq (fun he ↦ hqn (he.trans hpa.symm))
    · exact k₁ h hpa
  · by_cases hpa : p = a
    · refine closure_minimal ?_ isClosed_closure (mem_closure_oArc_sdiff h₂.isOArc_discBd h)
      rintro q ⟨hq, hqn⟩
      exact k₂ hq (fun he ↦ hqn (he.trans hpa.symm))
    · exact k₂ h hpa

theorem frontier_bridge (hT : IsClosedSurface T) {D₁ D₂ L : Set T}
  (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂)
    (hd : Disjoint D₁ D₂) {a b : T} (ha : a ∈ discBd D₁) (hb : b ∈ discBd D₂)
      (hl : IsLineWithEnds L a b) (hL₁ : L ∩ D₁ = {a})
    (hL₂ : L ∩ D₂ = {b}) : (D₁ ∪ L ∪ D₂) \ (discInt D₁ ∪ discInt D₂) ⊆ closure (D₁ ∪ L ∪ D₂)ᶜ := by
  have hLc : IsClosed L := by
    obtain ⟨f, -, -⟩ := hl
    have : L = range fun t ↦ (f t).1 := by
      ext x
      constructor
      · intro hx
        exact ⟨f.symm ⟨x, hx⟩, by simp⟩
      · rintro ⟨t, rfl⟩
        exact (f t).2
    rw [this]
    exact (isCompact_range (continuous_subtype_val.comp f.continuous)).isClosed
  have hmem₁ : ∀ {x}, x ∈ L → x ∈ D₁ → x = a := fun hx hy ↦ by
    have : _ ∈ L ∩ D₁ := ⟨hx, hy⟩
    rwa [hL₁] at this
  have hmem₂ : ∀ {x}, x ∈ L → x ∈ D₂ → x = b := fun hx hy ↦ by
    have : _ ∈ L ∩ D₂ := ⟨hx, hy⟩
    rwa [hL₂] at this
  have k₁ : ∀ {q}, q ∈ discBd D₁ → q ≠ a → q ∈ closure (D₁ ∪ L ∪ D₂)ᶜ := fun hq hne ↦ by
    rw [union_assoc]
    refine discBd_closure_compl_union hT h₁ (hLc.union h₂.isClosed) hq ?_
    rintro (h | h)
    · exact hne (hmem₁ h (Surface.discBd_subset _ hq))
    · exact disjoint_left.1 hd (Surface.discBd_subset _ hq) h
  have k₂ : ∀ {q}, q ∈ discBd D₂ → q ≠ b → q ∈ closure (D₁ ∪ L ∪ D₂)ᶜ := fun hq hne ↦ by
    rw [union_comm]
    refine discBd_closure_compl_union hT h₂ (h₁.isClosed.union hLc) hq ?_
    rintro (h | h)
    · exact disjoint_left.1 hd h (Surface.discBd_subset _ hq)
    · exact hne (hmem₂ h (Surface.discBd_subset _ hq))
  have k₃ : ∀ {q}, q ∈ discBd D₁ → q ∈ closure (D₁ ∪ L ∪ D₂)ᶜ := fun {q} hq ↦ by
    by_cases hqa : q = a
    · refine closure_minimal ?_ isClosed_closure (mem_closure_oArc_sdiff h₁.isOArc_discBd hq)
      rintro w ⟨hw, hwn⟩
      exact k₁ hw (fun he ↦ hwn (he.trans hqa.symm))
    · exact k₁ hq hqa
  have k₄ : ∀ {q}, q ∈ discBd D₂ → q ∈ closure (D₁ ∪ L ∪ D₂)ᶜ := fun {q} hq ↦ by
    by_cases hqb : q = b
    · refine closure_minimal ?_ isClosed_closure (mem_closure_oArc_sdiff h₂.isOArc_discBd hq)
      rintro w ⟨hw, hwn⟩
      exact k₂ hw (fun he ↦ hwn (he.trans hqb.symm))
    · exact k₂ hq hqb
  rintro p ⟨hp, hn⟩
  rcases hp with (h | h) | h
  · exact k₃ (by
      by_contra hb'
      exact hn (Or.inl ⟨h, hb'⟩))
  · by_cases hpa : p = a
    · exact k₃ (hpa ▸ ha)
    by_cases hpb : p = b
    · exact k₄ (hpb ▸ hb)
    have hoff : p ∉ D₁ ∪ D₂ := by
      rintro (h' | h')
      · exact hpa (hmem₁ h h')
      · exact hpb (hmem₂ h h')
    have hc := mem_closure_compl_union (h₁.isClosed.union h₂.isClosed)
      (line_subset_closure_compl hT hl h) hoff
    refine closure_mono ?_ hc
    rintro w hw ((h' | h') | h')
    · exact hw (Or.inr (Or.inl h'))
    · exact hw (Or.inl h')
    · exact hw (Or.inr (Or.inr h'))
  · exact k₄ (by
      by_contra hb'
      exact hn (Or.inr ⟨h, hb'⟩))

theorem isCell_touch_image [Nonempty T] (hT : IsClosedSurface T) {D₁ D₂ : Set T}
  (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂) {a : T}
    (ha : D₁ ∩ D₂ = {a}) (c : C(T, T)) (hc : InjOn c (D₁ ∪ D₂)) : IsCell T (c '' (D₁ ∪ D₂)) := by
  rw [image_union]
  obtain ⟨hd₁, -⟩ := isClosedDisc_image_injOn h₁ c.continuous.continuousOn
    (hc.mono subset_union_left)
  obtain ⟨hd₂, -⟩ := isClosedDisc_image_injOn h₂ c.continuous.continuousOn
    (hc.mono subset_union_right)
  refine isCell_touch hT hd₁ hd₂ (a := c a) ?_
  rw [← hc.image_inter subset_union_left subset_union_right, ha, image_singleton]

theorem isCell_bridge_image [ConnectedSpace T] (hT : IsClosedSurface T) {D₁ D₂ L : Set T}
  (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂)
    (hd : Disjoint D₁ D₂) {a b : T} (ha : a ∈ discBd D₁) (hb : b ∈ discBd D₂)
      (hl : IsLineWithEnds L a b) (hL₁ : L ∩ D₁ = {a})
    (hL₂ : L ∩ D₂ = {b}) (c : C(T, T)) (hc : InjOn c (D₁ ∪ L ∪ D₂)) : IsCell T (c '' (D₁ ∪ L ∪ D₂))
      := by
  have hs₁ : D₁ ⊆ D₁ ∪ L ∪ D₂ := subset_union_left.trans subset_union_left
  have hsL : L ⊆ D₁ ∪ L ∪ D₂ := subset_union_right.trans subset_union_left
  have hs₂ : D₂ ⊆ D₁ ∪ L ∪ D₂ := subset_union_right
  rw [image_union, image_union]
  obtain ⟨hd₁, hb₁⟩ := isClosedDisc_image_injOn h₁ c.continuous.continuousOn (hc.mono hs₁)
  obtain ⟨hd₂, hb₂⟩ := isClosedDisc_image_injOn h₂ c.continuous.continuousOn (hc.mono hs₂)
  have hline : IsLineWithEnds (c '' L) (c a) (c b) := by
    obtain ⟨u, hu, rfl, rfl, rfl⟩ := hl.exists_arc
    have h1 : IsArcMap (c ∘ u) := ⟨c.continuous.comp hu.1, fun x y h ↦ hu.2 (hc (hsL
      (mem_range_self x)) (hsL (mem_range_self y)) h)⟩
    have := h1.isLineWithEnds
    rwa [range_comp] at this
  refine isCell_bridge hT hd₁ hd₂ ?_ (hb₁ ▸ mem_image_of_mem _ ha) (hb₂ ▸ mem_image_of_mem _ hb)
    hline ?_ ?_
  · refine disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact disjoint_left.1 hd hx (hc (hs₁ hx) (hs₂ hy) he.symm ▸ hy)
  · rw [← hc.image_inter hsL hs₁, hL₁, image_singleton]
  · rw [← hc.image_inter hsL hs₂, hL₂, image_singleton]

end Frontier

section Outer

variable {S Shat Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  [TopologicalSpace Y]
  [T2Space Y] {ψ : Y → S} {K : Drawing S}

/-- The fragment wanted in the proof of (10.4), Graph Minors XIX, page 357: its image is `A`, it
caps to `Σ̂`, it has fewer cuffs than
`Σ`, and its inside is a closed surface `T'` homeomorphic to `Σ̂`, without a finite set. -/
def IsOuterFragment (_cap : IsCappedSurface S Shat) (ψ : Y → S) (A : Set S) : Prop :=
  ∃ y : Y, ψ '' connectedComponent y = A ∧
    (∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface (connectedComponent y) Shat₁
      → Nonempty (Shat₁ ≃ₜ Shat)) ∧
    numCuffs (connectedComponent y) < numCuffs S ∧
    ∃ (T' : Type) (_ : TopologicalSpace T') (e : OpenPartialHomeomorph (connectedComponent y) T')
      (P : Set T'),
      IsClosedSurface T' ∧ Nonempty (T' ≃ₜ Shat) ∧ P.Finite ∧ e.source = (bd
        (connectedComponent y))ᶜ ∧ e.target = Pᶜ

omit [T2Space Y] in
/-- The fragment outside a cell `Z` of `Σ̂`. Its capping is `Σ̂`, and its cuffs are the cuffs of `Σ`
not in `Z`, and one more. -/
theorem exists_outer_fragment_core (hS : IsSurface S) (cap : IsCappedSurface S Shat)
  (hY : IsSurface Y) (hψ : IsCutMap ψ K.U)
    {Z G : Set Shat} (hZc : IsClosed Z) (hG : IsOpen G) (hGZ : G ⊆ Z)
      (hcell : ∀ c : C(Shat, Shat), InjOn c Z → IsCell Shat (c '' Z))
    (hK : cap.emb '' K.U ⊆ Z) (hrest : Z \ G ⊆ cap.discs ∪ cap.emb '' K.U)
      (hfr : Z \ G ⊆ closure Zᶜ)
    (hm : ∀ Θ ∈ cuffs S, ¬ closure (cap.cuffDisc Θ) ⊆ Z → (closure (cap.cuffDisc Θ) ∩
      Z).Subsingleton) :
    ∃ y : Y, ψ '' connectedComponent y = cap.emb ⁻¹' Gᶜ ∧
      (∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface (connectedComponent y) Shat₁
        → Nonempty (Shat₁ ≃ₜ Shat)) ∧
      numCuffs (connectedComponent y) ≤ {Θ ∈ cuffs S | Disjoint (closure
        (cap.cuffDisc Θ)) Z}.ncard + 1 ∧
      ∃ (T' : Type) (_ : TopologicalSpace T') (e : OpenPartialHomeomorph (connectedComponent y) T')
        (P : Set T'),
        IsClosedSurface T' ∧ Nonempty (T' ≃ₜ Shat) ∧ P.Finite ∧ e.source = (bd
          (connectedComponent y))ᶜ ∧ e.target = Pᶜ := by
  classical
  have hT := cap.isClosedSurface
  have hconn : ConnectedSpace Shat := cap.connected
  have : CompactSpace Shat := hT.1
  have : CompactSpace S := hS.1
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  set 𝓑 : Set (Set S) := {Θ ∈ cuffs S | ¬ closure (cap.cuffDisc Θ) ⊆ Z} with h𝓑
  let E : Set S → Set Shat := fun Θ ↦ closure (cap.cuffDisc Θ)
  have hf𝓑 : 𝓑.Finite := hfc.subset fun _ h ↦ h.1
  have hdisj : (E '' 𝓑).PairwiseDisjoint id := by
    rintro _ ⟨Θ₁, h₁, rfl⟩ _ ⟨Θ₂, h₂, rfl⟩ hn
    exact cap.cuffDisc_disjoint Θ₁ h₁.1 Θ₂ h₂.1 fun h ↦ hn (h ▸ rfl)
  obtain ⟨T', tT', e, P, hT', ⟨hom⟩, hP, hcard, hs, ht⟩ := exists_cell_region hT hcell (hf𝓑.image E)
    (by
      rintro _ ⟨Θ, hΘ, rfl⟩
      exact cap.cuffDisc_closedDisc Θ hΘ.1) hdisj (by
      rintro _ ⟨Θ, hΘ, rfl⟩
      exact hm Θ hΘ.1 hΘ.2)
  set X : Set Shat := Z ∪ ⋃₀ (E '' 𝓑) with hX
  have hdc : IsClosed cap.discs := hfc.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hKc : IsClosed (cap.emb '' K.U) := (K.isClosed_U.isCompact.image
    cap.isEmbedding.continuous).isClosed
  have hAc : IsClosed (⋃₀ (E '' 𝓑)) := (hf𝓑.image E).isClosed_sUnion (by
    rintro _ ⟨Θ, -, rfl⟩
    exact isClosed_closure)
  have hsub : cap.discs ∪ cap.emb '' K.U ⊆ X := by
    rintro x (hx | hx)
    · obtain ⟨Θ, hΘ, hxΘ⟩ := mem_iUnion₂.1 hx
      by_cases h : closure (cap.cuffDisc Θ) ⊆ Z
      · exact Or.inl (h hxΘ)
      · exact Or.inr ⟨_, ⟨Θ, ⟨hΘ, h⟩, rfl⟩, hxΘ⟩
    · exact Or.inl (hK hx)
  have hop : IsOpen (X \ (cap.discs ∪ cap.emb '' K.U)) := by
    have : X \ (cap.discs ∪ cap.emb '' K.U) = G \ (cap.discs ∪ cap.emb '' K.U) := by
      ext x
      constructor
      · rintro ⟨hx | hx, hn⟩
        · refine ⟨?_, hn⟩
          by_contra hxG
          exact hn (hrest ⟨hx, hxG⟩)
        · obtain ⟨_, ⟨Θ, hΘ, rfl⟩, hxΘ⟩ := hx
          exact absurd (Or.inl (mem_biUnion hΘ.1 hxΘ)) hn
      · rintro ⟨hx, hn⟩
        exact ⟨Or.inl (hGZ hx), hn⟩
    rw [this]
    exact hG.sdiff (hdc.union hKc)
  have : ConnectedSpace T' := hom.symm.surjective.connectedSpace hom.symm.continuous
  obtain ⟨y, hy, hcap, hnum, e', hs', ht'⟩ := exists_fragment_of_region hS cap hY hψ hT' hP e
    (by rw [hs]) ht hsub hop
  refine ⟨y, ?_, fun Shat₁ _ cap₁ ↦ ?_, ?_, T', tT', e', P, hT', ⟨hom⟩, hP, hs', ht'⟩
  · rw [hy]
    have hXr : Xᶜ ⊆ range cap.emb := by
      rw [← compl_subset_compl, compl_compl, cap.compl_eq]
      intro x hx
      obtain ⟨Θ, hΘ, hxΘ⟩ := mem_iUnion₂.1 hx
      exact hsub (Or.inl (mem_biUnion hΘ (subset_closure hxΘ)))
    have hoff : ∀ {p}, p ∉ ⋃₀ (E '' 𝓑) → p ∈ Z → p ∉ G → p ∈ closure Xᶜ := fun hp hpZ hpG ↦
      mem_closure_compl_union hAc (hfr ⟨hpZ, hpG⟩) hp
    have hEout : ∀ {Θ}, Θ ∈ 𝓑 → ∀ {x}, cap.emb x ∈ E Θ → cap.emb x ∉ Z → cap.emb x ∈ closure Xᶜ
      := by
      intro Θ hΘ x hxE hxZ
      have hb : cap.emb x ∈ discBd (E Θ) := by
        rw [show discBd (E Θ) = _ from cap.cuffDisc_bd Θ hΘ.1]
        exact mem_image_of_mem _ (cap.mem_of_emb_mem hΘ.1 hxE)
      have hlim := discBd_subset_closure_compl hT (cap.cuffDisc_closedDisc Θ hΘ.1) hb
      have hrest' : IsClosed (Z ∪ ⋃₀ (E '' (𝓑 \ {Θ}))) :=
        hZc.union (((hf𝓑.subset sdiff_subset).image E).isClosed_sUnion (by
          rintro _ ⟨Θ, -, rfl⟩
          exact isClosed_closure))
      have hn : cap.emb x ∉ Z ∪ ⋃₀ (E '' (𝓑 \ {Θ})) := by
        rintro (h | ⟨_, ⟨Θ', hΘ', rfl⟩, hxΘ'⟩)
        · exact hxZ h
        · exact disjoint_left.1 (cap.cuffDisc_disjoint Θ hΘ.1 Θ' hΘ'.1.1
            (fun he ↦ hΘ'.2 he.symm)) hxE hxΘ'
      refine closure_mono ?_ (mem_closure_compl_union hrest' hlim hn)
      rintro w hw (hwZ | ⟨_, ⟨Θ', hΘ', rfl⟩, hwΘ'⟩)
      · exact hw (Or.inr (Or.inl hwZ))
      · by_cases he : Θ' = Θ
        · exact hw (Or.inl (he ▸ hwΘ'))
        · exact hw (Or.inr (Or.inr ⟨_, ⟨Θ', ⟨hΘ', he⟩, rfl⟩, hwΘ'⟩))
    have hcl : ∀ x, cap.emb x ∉ G → cap.emb x ∈ closure Xᶜ := by
      intro x hxG
      by_cases hxE : cap.emb x ∈ ⋃₀ (E '' 𝓑)
      · obtain ⟨_, ⟨Θ, hΘ, rfl⟩, hxΘ⟩ := hxE
        by_cases hxZ : cap.emb x ∈ Z
        · have hb : cap.emb x ∈ discBd (E Θ) := by
            rw [show discBd (E Θ) = _ from cap.cuffDisc_bd Θ hΘ.1]
            exact mem_image_of_mem _ (cap.mem_of_emb_mem hΘ.1 hxΘ)
          have hlim := mem_closure_oArc_sdiff (cap.cuffDisc_closedDisc Θ hΘ.1).isOArc_discBd hb
          refine closure_minimal ?_ isClosed_closure hlim
          rintro w ⟨hwb, hwn⟩
          rw [show discBd (E Θ) = _ from cap.cuffDisc_bd Θ hΘ.1] at hwb
          obtain ⟨z, hz, rfl⟩ := hwb
          have hzE : cap.emb z ∈ E Θ := Surface.discBd_subset (E Θ) (by
            rw [show discBd (E Θ) = _ from cap.cuffDisc_bd Θ hΘ.1]
            exact mem_image_of_mem _ hz)
          exact hEout hΘ hzE fun hzZ ↦ hwn (hm Θ hΘ.1 hΘ.2 ⟨hzE, hzZ⟩ ⟨hxΘ, hxZ⟩)
        · exact hEout hΘ hxΘ hxZ
      · by_cases hxZ : cap.emb x ∈ Z
        · exact hoff hxE hxZ hxG
        · exact subset_closure (fun h ↦ h.elim hxZ hxE)
    apply Subset.antisymm
    · refine closure_minimal ?_ (hG.isClosed_compl.preimage cap.isEmbedding.continuous)
      intro x hx hxG
      exact hx (Or.inl (hGZ hxG))
    · intro x hx
      rw [cap.isEmbedding.closure_eq_preimage_closure_image, mem_preimage,
        image_preimage_eq_of_subset hXr]
      exact hcl x hx
  · obtain ⟨f⟩ := hcap Shat₁ cap₁
    exact ⟨f.trans hom⟩
  · rw [hnum]
    have hfd : {Θ ∈ cuffs S | Disjoint (closure (cap.cuffDisc Θ)) Z}.Finite
      := hfc.subset fun _ h ↦ h.1
    have hsub' : {F ∈ E '' 𝓑 | Disjoint F Z} ⊆ E '' {Θ ∈ cuffs S | Disjoint (closure
      (cap.cuffDisc Θ)) Z} := by
      rintro _ ⟨⟨Θ, hΘ, rfl⟩, hd⟩
      exact ⟨Θ, ⟨hΘ.1, hd⟩, rfl⟩
    have h₅ := (ncard_le_ncard hsub' (hfd.image _)).trans (ncard_image_le hfd)
    omega

omit [T2Space Y] in
/-- **The fragment outside a cell.** -/
theorem exists_outer_fragment (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U)
    {Z G : Set Shat} (hZc : IsClosed Z) (hG : IsOpen G) (hGZ : G ⊆ Z)
      (hcell : ∀ c : C(Shat, Shat), InjOn c Z → IsCell Shat (c '' Z))
    (hK : cap.emb '' K.U ⊆ Z) (hrest : Z \ G ⊆ cap.discs ∪ cap.emb '' K.U)
      (hfr : Z \ G ⊆ closure Zᶜ)
    (hm : ∀ Θ ∈ cuffs S, ¬ closure (cap.cuffDisc Θ) ⊆ Z → (closure (cap.cuffDisc Θ) ∩
      Z).Subsingleton)
    {Θ₁ Θ₂ : Set S} (h₁ : Θ₁ ∈ cuffs S) (h₂ : Θ₂ ∈ cuffs S) (hne : Θ₁ ≠ Θ₂) (hZ₁ : closure
      (cap.cuffDisc Θ₁) ⊆ Z)
    (hZ₂ : closure (cap.cuffDisc Θ₂) ⊆ Z) :
    IsOuterFragment cap ψ (cap.emb ⁻¹' Gᶜ) := by
  classical
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  obtain ⟨y, hy, hcap, hnum, hrest'⟩ := exists_outer_fragment_core hS cap hY hψ hZc hG hGZ hcell hK
    hrest hfr hm
  refine ⟨y, hy, hcap, ?_, hrest'⟩
  set 𝓑 : Set (Set S) := {Θ ∈ cuffs S | Disjoint (closure (cap.cuffDisc Θ)) Z} with h𝓑
  have hne' : ∀ {Θ}, Θ ∈ cuffs S → (closure (cap.cuffDisc Θ)).Nonempty := fun hΘ ↦
    (cap.cuffDisc_closedDisc _ hΘ).nonempty_discInt.mono (discInt_subset _)
  have hsub𝓑 : 𝓑 ⊆ cuffs S \ {Θ₁, Θ₂} := by
    rintro Θ ⟨hΘ, hn⟩
    refine ⟨hΘ, ?_⟩
    rintro (rfl | h)
    · obtain ⟨x, hx⟩ := hne' hΘ
      exact disjoint_left.1 hn hx (hZ₁ hx)
    · rw [mem_singleton_iff.1 h] at hn
      obtain ⟨x, hx⟩ := hne' h₂
      exact disjoint_left.1 hn hx (hZ₂ hx)
  have h₃ : 𝓑.ncard ≤ (cuffs S \ {Θ₁, Θ₂}).ncard := ncard_le_ncard hsub𝓑 (hfc.subset sdiff_subset)
  have h₄ : (cuffs S \ {Θ₁, Θ₂}).ncard + 2 = (cuffs S).ncard := by
    have hsb : ({Θ₁, Θ₂} : Set (Set S)) ⊆ cuffs S := by
      rintro _ (rfl | h)
      · exact h₁
      · rw [mem_singleton_iff.1 h]
        exact h₂
    rw [← ncard_pair hne, ncard_sdiff_add_ncard_of_subset hsb hfc]
  change _ < (cuffs S).ncard
  omega

end Outer

end GraphMinor.GM19

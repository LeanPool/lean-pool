/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentCapping
public import LeanPool.GraphMinor.GM19.DiscSides
public import LeanPool.GraphMinor.GM19.CutTwo

/-!
# Fragments as regions of a closed surface

Let `ψ` undo a cut of `S` along `K`, and let `S ⊆ Shat` be a capping. A component of the complement
of `K` and of the pasted discs
is the inside of a fragment. So if this region is a closed surface `T'` without a finite set, then
by `capping_homeo` each
capping of the fragment is `T'` (`exists_fragment_of_region`). The second part finds such `T'`:
finitely many disjoint
closed discs collapse to points, also if they touch a given set in one point each
(`exists_cell_region`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

section Dense

variable {S : Type} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- The inside of a connected surface is dense. -/
theorem dense_interior (hS : IsSurface S) [ConnectedSpace S] : Dense (bd S)ᶜ := by
  obtain ⟨Shat, _, ⟨cap⟩⟩ := exists_cappedSurface _ S hS inferInstance rfl
  have hT := cap.isClosedSurface
  have : T2Space Shat := hT.2.1
  have hc := cap.isEmbedding
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
  intro x
  by_cases hx : x ∈ bd S
  · rw [← sUnion_cuffs] at hx
    obtain ⟨Θ, hΘ, hxΘ⟩ := hx
    have hE := cap.cuffDisc_closedDisc Θ hΘ
    set E := closure (cap.cuffDisc Θ) with hEdef
    have hxb : cap.emb x ∈ discBd E := cap.cuffDisc_bd Θ hΘ ▸ mem_image_of_mem _ hxΘ
    have hnot : cap.emb x ∉ interior E := fun h ↦ by
      have := subset_discInt_of_isOpen (fun y _ ↦ hT.2.2 y) isOpen_interior interior_subset h
      exact this.2 hxb
    have hcl : cap.emb x ∈ closure Eᶜ := by
      rw [closure_compl]
      exact hnot
    set V : Set Shat := (⋃ Θ' ∈ cuffs S \ {Θ}, closure (cap.cuffDisc Θ'))ᶜ with hV
    have hVo : IsOpen V := ((hfin.subset sdiff_subset).isClosed_biUnion fun _ _ ↦
      isClosed_closure).isOpen_compl
    have hxV : cap.emb x ∈ V := by
      intro hn
      obtain ⟨Θ', hΘ', hxΘ'⟩ := mem_iUnion₂.1 hn
      exact disjoint_left.1 (cap.cuffDisc_disjoint Θ hΘ Θ' hΘ'.1 (Ne.symm hΘ'.2))
        (discBd_subset _ hxb) hxΘ'
    rw [hc.closure_eq_preimage_closure_image, mem_preimage, ← cap.compl_eq_image hS]
    rw [_root_.mem_closure_iff] at hcl ⊢
    intro O hO hxO
    obtain ⟨y, hy, hyE⟩ := hcl (O ∩ V) (hO.inter hVo) ⟨hxO, hxV⟩
    refine ⟨y, hy.1, fun hn ↦ ?_⟩
    obtain ⟨Θ', hΘ', hyΘ'⟩ := mem_iUnion₂.1 hn
    by_cases he : Θ' = Θ
    · rw [he] at hyΘ'
      exact hyE hyΘ'
    · exact hy.2 (mem_biUnion (show Θ' ∈ cuffs S \ {Θ} from ⟨hΘ', he⟩) hyΘ')
  · exact subset_closure hx

omit [T2Space S] in
/-- The inside of a surface is dense. -/
theorem dense_interior' (hS : IsSurface S) : Dense (bd S)ᶜ := by
  have : LocallyConnectedSpace S := IsSurface.locallyConnected hS
  intro x
  have hWo : IsOpen (connectedComponent x) := isOpen_connectedComponent
  have hWc : IsClopen (connectedComponent x) := ⟨isClosed_connectedComponent, hWo⟩
  have : ConnectedSpace (connectedComponent x) := isConnected_iff_connectedSpace.mp
    isConnected_connectedComponent
  have hd := dense_interior (isSurface_sub hS hWc)
  have hx := hd ⟨x, mem_connectedComponent⟩
  rw [_root_.mem_closure_iff] at hx ⊢
  intro O hO hxO
  obtain ⟨y, hyO, hy⟩ := hx (Subtype.val ⁻¹' O) (hO.preimage continuous_subtype_val) hxO
  exact ⟨y.1, hyO, fun h ↦ hy ((mem_bd_sub hWo).2 h)⟩

end Dense

section Connected

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

omit [ConnectedSpace T] in
/-- An open connected set of a closed surface stays connected when a point is removed. -/
theorem isPreconnected_sdiff_point (hT : IsClosedSurface T) {G : Set T} (hG : IsOpen G)
  (hGc : IsPreconnected G) (x : T) :
    IsPreconnected (G \ {x}) := by
  by_cases hx : x ∈ G
  swap
  · rwa [sdiff_singleton_eq_self hx]
  obtain ⟨U, h, g, c, hU, h0⟩ := (hT.2.2 x).exists_ballChart hG hx one_pos
  have h0m : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hdisc := isClosedDisc_of_convex (K := closedBall (0 : ℂ) (1 / 2))
    (convex_closedBall 0 _)
    (by rw [interior_closedBall _ (by norm_num)]; exact ⟨0, by simp⟩)
    isBounded_closedBall isClosed_closedBall
  obtain ⟨hB, -⟩ := c.image_disc hdisc.1 hsub
  have hBU : g '' closedBall 0 (1 / 2) ⊆ U := image_subset_iff.2 fun z hz ↦ c.gm (hsub hz)
  have hxB : x ∈ g '' closedBall 0 (1 / 2) := ⟨0, by simp, h0⟩
  have hheq : U \ {x} = g '' (ball 0 1 \ {0}) := by
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
  have hc1 : IsPreconnected (U \ {x}) := hheq ▸ isPreconnected_ball_sdiff.image _
    (c.gc.mono sdiff_subset)
  have hc2 := isPreconnected_sdiff_disc hT hG hGc hB (hBU.trans hU)
  have hz : g (3 / 4) ∈ (U \ {x}) ∩ (G \ g '' closedBall 0 (1 / 2)) := by
    have hm : (3 / 4 : ℂ) ∈ ball (0 : ℂ) 1 := by simp; norm_num
    have hnot : g (3 / 4) ∉ g '' closedBall 0 (1 / 2) := by
      rintro ⟨w, hw, he⟩
      have := c.hg.injOn (hsub hw) hm he
      rw [this, mem_closedBall_zero_iff] at hw
      norm_num at hw
    refine ⟨⟨c.gm hm, fun he ↦ hnot (he ▸ hxB)⟩, hU (c.gm hm), hnot⟩
  have := hc1.union' ⟨_, hz.1, hz.2⟩ hc2
  convert this using 1
  ext y
  constructor
  · rintro ⟨hy, hne⟩
    by_cases hyB : y ∈ g '' closedBall 0 (1 / 2)
    · exact Or.inl ⟨hBU hyB, hne⟩
    · exact Or.inr ⟨hy, hyB⟩
  · rintro (⟨hy, hne⟩ | ⟨hy, hyB⟩)
    · exact ⟨hU hy, hne⟩
    · exact ⟨hy, fun he ↦ hyB (he ▸ hxB)⟩

omit [ConnectedSpace T] in
theorem isPreconnected_sdiff_finite (hT : IsClosedSurface T) {G : Set T} (hG : IsOpen G)
  (hGc : IsPreconnected G) {P : Set T}
    (hP : P.Finite) : IsPreconnected (G \ P) := by
  induction P, hP using Set.Finite.induction_on with
  | empty => simpa using hGc
  | @insert x P _ hP ih =>
    have hop : IsOpen (G \ P) := hG.sdiff hP.isClosed
    have := isPreconnected_sdiff_point hT hop ih x
    rwa [sdiff_sdiff, union_comm, ← insert_eq] at this

end Connected

section Fragment

variable {S Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y] [T2Space Y] {ψ : Y
  → S} {K : Drawing S}

omit [T2Space Y] in
/-- A component of the complement of `K` and of the boundary is the inside of a fragment. -/
theorem exists_fragment (hS : IsSurface S) (hY : IsSurface Y) (hψ : IsCutMap ψ K.U) {A : Set S}
    (hA : A ∈ componentsIn (bd S ∪ K.U)ᶜ) :
    ∃ y : Y, ψ '' connectedComponent y = closure A ∧ ∃ e : OpenPartialHomeomorph
      (connectedComponent y) S,
      e.source = (bd (connectedComponent y))ᶜ ∧ e.target = A := by
  classical
  have : CompactSpace Y := hY.1
  have : LocallyConnectedSpace Y := IsSurface.locallyConnected hY
  have hF : IsClosed K.U := K.isClosed_U
  obtain ⟨a, haD, rfl⟩ := hA
  obtain ⟨y, rfl⟩ := hψ.2.1 a
  have haD' : ψ y ∉ bd S ∧ ψ y ∉ K.U := by simpa using haD
  have hyb : y ∉ bd Y := fun h ↦ haD'.1 (bd_of_bd_cutMap hψ hF h haD'.2)
  refine ⟨y, ?_⟩
  have hWo : IsOpen (connectedComponent y) := isOpen_connectedComponent
  have hbdW : ∀ {x : connectedComponent y}, x ∈ bd (connectedComponent y) ↔ x.1 ∈ bd Y
    := mem_bd_sub hWo
  have hfrag := isCuttingFragment_of_cut hS hY hψ (K := K) rfl y
  set R := (fun x : connectedComponent y ↦ ψ x.1) '' (bd (connectedComponent y))ᶜ with hR
  have hRcomp : R = connectedComponentIn (bd S ∪ K.U)ᶜ (ψ y) := by
    obtain ⟨r, hr, hRe⟩ := hfrag.interior_component
    refine hRe.symm.trans (connectedComponentIn_eq ?_)
    rw [hRe]
    exact ⟨⟨y, mem_connectedComponent⟩, fun h ↦ hyb (hbdW.1 h), rfl⟩
  rw [← hRcomp]
  have hRW : R ⊆ ψ '' connectedComponent y := by
    rintro _ ⟨x, -, rfl⟩
    exact mem_image_of_mem ψ x.2
  have hoff : ∀ {x : connectedComponent y}, x ∉ bd (connectedComponent y) → ψ x.1 ∉ K.U
    := fun hx hn ↦
    hx (hbdW.2 (hψ.2.2.2.2 hn))
  have : Nonempty (connectedComponent y) := ⟨⟨y, mem_connectedComponent⟩⟩
  have hopen : ∀ u ⊆ (bd (connectedComponent y))ᶜ, IsOpen u → IsOpen ((fun x : connectedComponent y
    ↦ ψ x.1) '' u) := by
    intro u hu huo
    have : (fun x : connectedComponent y ↦ ψ x.1) '' u = ψ '' (Subtype.val '' u) := by
      rw [image_image]
    rw [this]
    refine isOpen_image_of_isCutMap hψ ?_ (hWo.isOpenMap_subtype_val _ huo)
    rintro _ ⟨x, hx, rfl⟩
    exact hoff (hu hx)
  obtain ⟨e, hs, ht, -⟩ := GM19.exists_oph (cuff_statement _ hfrag.isSurface).1.isOpen_compl
    (hψ.1.comp continuous_subtype_val).continuousOn hfrag.injOn_interior hopen rfl
  refine ⟨Subset.antisymm ?_ ?_, e, hs, ht⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hd := dense_interior' hY x
    rw [_root_.mem_closure_iff] at hd ⊢
    intro O hO hxO
    have hWm : connectedComponent y ∈ 𝓝 x := hWo.mem_nhds hx
    obtain ⟨z, ⟨hzO, hzW⟩, hzb⟩ := hd (ψ ⁻¹' O ∩ connectedComponent y)
      ((hO.preimage hψ.1).inter hWo) ⟨hxO, hx⟩
    exact ⟨ψ z, hzO, ⟨⟨z, hzW⟩, fun h ↦ hzb (hbdW.1 h), rfl⟩⟩
  · exact closure_minimal hRW (isClosedMap_of_isCutMap hψ _ isClosed_connectedComponent)

variable {Shat T' : Type} [TopologicalSpace Shat] [T2Space Shat] [TopologicalSpace T']

/-- The pasted discs. -/
def IsCappedSurface.discs (cap : IsCappedSurface S Shat) : Set Shat := ⋃ Θ ∈ cuffs S, closure
  (cap.cuffDisc Θ)

omit [T2Space Shat] in
omit [T2Space Y] in
/-- If the region off `X` is a component of the complement of `K` and of the pasted discs, and it is
a connected closed surface
`T'` without a finite set `P`, then there is a fragment with this inside. Each capping of the
fragment is `T'`, and the fragment has
`|P|` cuffs. -/
theorem exists_fragment_of_region (hS : IsSurface S) (cap : IsCappedSurface S Shat)
  (hY : IsSurface Y) (hψ : IsCutMap ψ K.U)
    (hT' : IsClosedSurface T') [ConnectedSpace T'] {P : Set T'} (hP : P.Finite) {X : Set Shat}
      (e : OpenPartialHomeomorph Shat T')
    (hs : e.source = Xᶜ) (ht : e.target = Pᶜ) (hsub : cap.discs ∪ cap.emb '' K.U ⊆ X)
    (hop : IsOpen (X \ (cap.discs ∪ cap.emb '' K.U))) :
    ∃ y : Y, ψ '' connectedComponent y = closure (cap.emb ⁻¹' Xᶜ) ∧
      (∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface (connectedComponent y) Shat₁
        → Nonempty (Shat₁ ≃ₜ T')) ∧
      numCuffs (connectedComponent y) = P.ncard ∧
      ∃ e' : OpenPartialHomeomorph (connectedComponent y) T', e'.source = (bd
        (connectedComponent y))ᶜ ∧ e'.target = Pᶜ := by
  classical
  have : T2Space T' := hT'.2.1
  have hcomp : cap.discsᶜ = cap.emb '' (bd S)ᶜ := cap.compl_eq_image hS
  have hXA : Xᶜ ⊆ cap.emb '' (bd S)ᶜ := by
    rw [← hcomp]
    exact compl_subset_compl.2 (subset_union_left.trans hsub)
  set A : Set S := cap.emb ⁻¹' Xᶜ with hA
  have hAim : cap.emb '' A = Xᶜ := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro x hx
    obtain ⟨z, -, rfl⟩ := hXA hx
    exact ⟨z, hx, rfl⟩
  have hXo : IsOpen Xᶜ := hs ▸ e.open_source
  have hAo : IsOpen A := hXo.preimage cap.isEmbedding.continuous
  have hconn : IsPreconnected A := by
    rw [← cap.isEmbedding.isInducing.isPreconnected_image, hAim]
    have h₁ : IsPreconnected Pᶜ := by
      have := isPreconnected_sdiff_finite hT' isOpen_univ isPreconnected_univ hP
      rwa [← compl_eq_univ_sdiff] at this
    have h₂ : e.symm '' Pᶜ = Xᶜ := by
      rw [← hs, ← ht]
      exact e.symm_image_target_eq_source
    rw [← h₂]
    exact h₁.image _ (ht ▸ e.continuousOn_symm)
  have hAD : A ⊆ (bd S ∪ K.U)ᶜ := by
    intro x hx
    have hx' : cap.emb x ∉ X := hx
    rintro (hb | hu)
    · refine hx' (hsub (Or.inl ?_))
      by_contra hn
      have : cap.emb x ∈ cap.emb '' (bd S)ᶜ := hcomp ▸ hn
      obtain ⟨z, hz, he⟩ := this
      exact hz (cap.isEmbedding.injective he ▸ hb)
    · exact hx' (hsub (Or.inr (mem_image_of_mem _ hu)))
  have : Nonempty T' := (inferInstance : ConnectedSpace T').toNonempty
  obtain ⟨z₀, hz₀⟩ : (Pᶜ).Nonempty := (dense_compl_finite hT'.2.2 hP).nonempty
  obtain ⟨a, ha⟩ : A.Nonempty := by
    have hm : e.symm z₀ ∈ Xᶜ := by rw [← hs]; exact e.map_target (ht ▸ hz₀)
    obtain ⟨z, -, he⟩ := hXA hm
    exact ⟨z, by rw [hA, mem_preimage, he]; exact hm⟩
  have hAcomp : A ∈ componentsIn (bd S ∪ K.U)ᶜ := by
    refine ⟨a, hAD ha, Subset.antisymm ?_ (hconn.subset_connectedComponentIn ha hAD)⟩
    have hco := isPreconnected_connectedComponentIn (F := (bd S ∪ K.U)ᶜ) (x := a)
    have hV : IsOpen (cap.emb ⁻¹' (X \ (cap.discs ∪ cap.emb '' K.U)))
      := hop.preimage cap.isEmbedding.continuous
    refine hco.subset_left_of_subset_union hAo hV ?_ (fun x hx ↦ ?_) ⟨a,
      mem_connectedComponentIn (hAD ha), ha⟩
    · exact disjoint_left.2 fun x hx hx' ↦ hx hx'.1
    · have hxD := connectedComponentIn_subset _ _ hx
      by_cases hxX : cap.emb x ∈ X
      · refine Or.inr ⟨hxX, ?_⟩
        rintro (hd | ⟨u, hu, he⟩)
        · have : cap.emb x ∉ cap.discsᶜ := fun h ↦ h hd
          rw [hcomp] at this
          exact this (mem_image_of_mem _ fun h ↦ hxD (Or.inl h))
        · exact hxD (Or.inr (cap.isEmbedding.injective he ▸ hu))
      · exact Or.inl hxX
  obtain ⟨y, hy, e₁, hs₁, ht₁⟩ := exists_fragment hS hY hψ hAcomp
  refine ⟨y, hy, ?_⟩
  have : Nonempty (connectedComponent y) := ⟨⟨y, mem_connectedComponent⟩⟩
  have : LocallyConnectedSpace Y := IsSurface.locallyConnected hY
  have hsW : IsSurface (connectedComponent y) := isSurface_sub hY ⟨isClosed_connectedComponent,
    isOpen_connectedComponent⟩
  have ho : ∀ u ⊆ A, IsOpen u → IsOpen (cap.emb '' u) := fun u hu huo ↦ by
    obtain ⟨O, hO, rfl⟩ := cap.isEmbedding.isInducing.isOpen_iff.1 huo
    have : cap.emb '' (cap.emb ⁻¹' O) = O ∩ Xᶜ := by
      apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨hx, hu hx⟩
      · rintro z ⟨hz, hz'⟩
        rw [← hAim] at hz'
        obtain ⟨x, -, rfl⟩ := hz'
        exact ⟨x, hz, rfl⟩
    rw [this]
    exact hO.inter hXo
  have : Nonempty S := ⟨a⟩
  obtain ⟨e₂, hs₂, ht₂, -⟩ := GM19.exists_oph hAo cap.isEmbedding.continuous.continuousOn
    cap.isEmbedding.injective.injOn ho hAim
  let e' := (e₁.trans' e₂ (ht₁.trans hs₂.symm)).trans' e (ht₂.trans hs.symm)
  have hs' : e'.source = (bd (connectedComponent y))ᶜ := hs₁
  have ht' : e'.target = Pᶜ := ht
  refine ⟨fun Shat₁ _ cap₁ ↦ (capping_homeo hsW cap₁ hT' hP e' hs' ht').1, ?_, e', hs', ht'⟩
  obtain ⟨Shat₁, _, ⟨cap₁⟩⟩ := exists_cappedSurface _ (connectedComponent y) hsW
    (isConnected_iff_connectedSpace.mp isConnected_connectedComponent) rfl
  exact (capping_homeo hsW cap₁ hT' hP e' hs' ht').2

end Fragment

section Cell

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- `Y` is cellular in `T`: `T` without `Y` is a closed surface homeomorphic to `T`, without at most
one point. -/
def IsCell (T : Type) [TopologicalSpace T] (Y : Set T) : Prop :=
  ∃ (T' : Type) (_ : TopologicalSpace T') (e : OpenPartialHomeomorph T T')
    (P : Set T'), IsClosedSurface T' ∧
    Nonempty (T' ≃ₜ T) ∧ P.Finite ∧ P.ncard ≤ 1 ∧ e.source = Yᶜ ∧ e.target = Pᶜ

theorem isCell_disc [Nonempty T] (hT : IsClosedSurface T) {D : Set T}
  (hD : IsClosedDisc D) : IsCell T D := by
  have : CompactSpace T := hT.1
  obtain ⟨c, p, hc⟩ := exists_collapse_disc hT hD
  obtain ⟨e, hs, ht, -⟩ := hc.exists_oph
  exact ⟨T, _, e, {p}, hT, ⟨.refl T⟩, finite_singleton _, by simp, hs, ht⟩

theorem isCell_touch [Nonempty T] (hT : IsClosedSurface T) {D₁ D₂ : Set T} (h₁ : IsClosedDisc D₁)
  (h₂ : IsClosedDisc D₂) {a : T}
    (ha : D₁ ∩ D₂ = {a}) : IsCell T (D₁ ∪ D₂) := by
  classical
  have : CompactSpace T := hT.1
  obtain ⟨c, p, hc⟩ := exists_collapse_disc hT h₁
  have hinj : InjOn c D₂ := by
    intro x hx y hy he
    by_cases hx₁ : x ∈ D₁
    · have hy₁ : y ∈ D₁ := hc.preimage (by rw [mem_preimage, ← he]; exact hc.mapsTo hx₁)
      have hxa : x = a := by
        have : x ∈ D₁ ∩ D₂ := ⟨hx₁, hx⟩
        rwa [ha] at this
      have hya : y = a := by
        have : y ∈ D₁ ∩ D₂ := ⟨hy₁,
          hy⟩
        rwa [ha] at this
      rw [hxa, hya]
    · have hy₁ : y ∉ D₁ := fun hy₁ ↦
        hx₁ (hc.preimage (by rw [mem_preimage, he]; exact hc.mapsTo hy₁))
      exact hc.injOn hx₁ hy₁ he
  obtain ⟨hd, -⟩ := isClosedDisc_image_injOn h₂ c.continuous.continuousOn hinj
  obtain ⟨c', p', hc'⟩ := exists_collapse_disc hT hd
  have hcomp := hc.comp hc'
  have hpre : D₁ ∪ c ⁻¹' (c '' D₂) = D₁ ∪ D₂ := by
    apply Subset.antisymm
    · rintro x (hx | ⟨z, hz, he⟩)
      · exact Or.inl
          hx
      · by_cases hx₁ : x ∈
          D₁
        · exact Or.inl hx₁
        · have hz₁ : z ∉ D₁ := fun hz₁ ↦
            hx₁ (hc.preimage (by rw [mem_preimage, ← he]; exact hc.mapsTo hz₁))
          exact Or.inr (hc.injOn hz₁ hx₁ he ▸ hz)
    · rintro x (hx | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨x, hx, rfl⟩
  have hp' : c' '' {p} ∪ {p'} = {p'} := by
    have hm : p ∈ c '' D₂ := by
      have hm : a ∈ D₁ ∩ D₂ := by rw [ha]; exact mem_singleton a
      exact ⟨a, hm.2, hc.mapsTo hm.1⟩
    rw [image_singleton, show c' p = p' from hc'.mapsTo hm]
    simp
  rw [hpre, hp'] at hcomp
  obtain ⟨e, hs, ht, -⟩ := hcomp.exists_oph
  exact ⟨T, _, e, {p'}, hT, ⟨.refl T⟩, finite_singleton _, by simp, hs, ht⟩

/-- Let `Y` be cellular, also after each continuous map that is one to one on `Y`. Let finitely many
pairwise disjoint closed
discs meet `Y` in at most one point each. Then `T` without `Y` and without the discs is a closed
surface homeomorphic to `T`,
without a finite set, with one point for each disc and at most one more. -/
theorem exists_cell_region [Nonempty T] (hT : IsClosedSurface T) {Y : Set T}
  (hY : ∀ c : C(T, T), InjOn c Y → IsCell T (c '' Y))
    {𝓐 : Set (Set T)} (hf : 𝓐.Finite) (hd : ∀ E ∈ 𝓐, IsClosedDisc E) (hp : 𝓐.PairwiseDisjoint id)
    (hm : ∀ E ∈ 𝓐, (E ∩ Y).Subsingleton) :
    ∃ (T' : Type) (_ : TopologicalSpace T') (e : OpenPartialHomeomorph T T')
      (P : Set T'), IsClosedSurface T' ∧
      Nonempty (T' ≃ₜ T) ∧ P.Finite ∧ P.ncard ≤ {E ∈ 𝓐 | Disjoint E Y}.ncard + 1 ∧ e.source =
        (Y ∪ ⋃₀ 𝓐)ᶜ ∧ e.target = Pᶜ := by
  classical
  have : CompactSpace T := hT.1
  obtain ⟨c, P₀, q, hc, hq, rfl, hqi⟩ := exists_collapse hT hf hd hp
  have hinj : InjOn c Y := by
    intro x hx y hy he
    by_cases hxA : x ∈ ⋃₀ 𝓐
    · obtain ⟨E, hE, hxE⟩ := hxA
      have hyA : y ∈ ⋃₀ 𝓐 := hc.preimage (by
        rw [mem_preimage, ← he, hq E hE x hxE]
        exact mem_image_of_mem q hE)
      obtain ⟨E', hE', hyE'⟩ := hyA
      have : E = E' := hqi hE hE' (by rw [← hq E hE x hxE, ← hq E' hE' y hyE',
        he])
      subst this
      exact hm E hE ⟨hxE, hx⟩ ⟨hyE', hy⟩
    · have hyA : y ∉ ⋃₀ 𝓐 := fun hyA ↦
        hxA (hc.preimage (by rw [mem_preimage, he]; exact hc.mapsTo hyA))
      exact hc.injOn hxA hyA he
  obtain ⟨T', tT', e₁, P₁, hT', hhom, hP₁, hc₁, hs₁, ht₁⟩ := hY c hinj
  obtain ⟨e₀, hs₀, ht₀, heq⟩ := hc.exists_oph
  have hT2' : T2Space T' := hT'.2.1
  refine ⟨T', tT', e₀.trans e₁, P₁ ∪ e₁ '' (q '' 𝓐 \ c '' Y), hT', hhom,
    hP₁.union (((hf.image _).subset sdiff_subset).image _),
    ?_, ?_, ?_⟩
  · refine (ncard_union_le _ _).trans ?_
    have hfd : {E ∈ 𝓐 | Disjoint E Y}.Finite := hf.subset fun _ h ↦ h.1
    have hsub : q '' 𝓐 \ c '' Y ⊆ q '' {E ∈ 𝓐 | Disjoint E Y} := by
      rintro _ ⟨⟨E, hE, rfl⟩, hn⟩
      refine ⟨E, ⟨hE, disjoint_left.2 fun x hxE hxY ↦ hn ⟨x, hxY, hq E hE x hxE⟩⟩, rfl⟩
    have h₂ : (e₁ '' (q '' 𝓐 \ c '' Y)).ncard ≤ {E ∈ 𝓐 | Disjoint E Y}.ncard :=
      (ncard_image_le ((hf.image _).subset sdiff_subset)).trans
        ((ncard_le_ncard hsub (hfd.image _)).trans (ncard_image_le hfd))
    omega
  · ext x
    rw [e₀.trans_source, hs₀, hs₁]
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_union, not_or]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨fun hxY ↦ hy ?_, hx⟩
      rw [heq hx]
      exact mem_image_of_mem c hxY
    · rintro ⟨hxY, hx⟩
      refine ⟨hx, fun hy ↦ ?_⟩
      rw [heq hx] at hy
      obtain ⟨z, hz, he⟩ := hy
      by_cases hzA : z ∈ ⋃₀ 𝓐
      · exact hx (hc.preimage (by rw [mem_preimage, ← he]; exact hc.mapsTo hzA))
      · exact hxY (hc.injOn hzA hx he ▸ hz)
  · ext z
    rw [e₀.trans_target, ht₁, ht₀]
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_union, not_or]
    constructor
    · rintro ⟨hz, hw⟩
      refine ⟨hz, ?_⟩
      rintro ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
      have hws : w ∈ e₁.source := by rw [hs₁]; exact hw₂
      rw [e₁.left_inv hws] at hw
      exact hw hw₁
    · rintro ⟨hz, hw⟩
      refine ⟨hz, fun hq' ↦ hw ?_⟩
      have hzt : z ∈ e₁.target := by rw [ht₁]; exact hz
      have hws : e₁.symm z ∈ e₁.source := e₁.map_target hzt
      rw [hs₁] at hws
      exact ⟨e₁.symm z, ⟨hq', hws⟩, e₁.right_inv hzt⟩

end Cell

end GraphMinor.GM19

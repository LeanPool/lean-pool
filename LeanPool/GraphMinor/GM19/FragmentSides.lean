/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentRegion
public import LeanPool.GraphMinor.GM19.RadialExists
public import LeanPool.GraphMinor.GM11.PerimeterPull
public import LeanPool.GraphMinor.GM11.GlueDiscs
public import LeanPool.GraphMinor.Surface.PushOff

/-!
# The inside of a disc of a capped surface

Let `D` be a closed disc of a capped surface, and take the region of `D` off the pasted discs in
`D`. We identify the boundary of `D`
to one point, and get a sphere in which the pasted discs are closed discs. So the region is a sphere
without a finite set
(`exists_inner_region`). This gives the fragment inside `D` (`exists_inner_fragment`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface GraphMinor.GM11 OnePoint

/-- The sphere is the model `Σ(0, 0, 0)`. -/
theorem nonempty_homeomorph_of_isSphere {T : Type} [TopologicalSpace T] (h : IsSphere T) : Nonempty
  (T ≃ₜ SurfaceModel 0 0 0) := by
  obtain ⟨e⟩ := h
  let f : OnePoint EuclideanPlane → SurfaceModel 0 0 0 := fun x ↦ Quot.mk _ ⟨x, fun i hi ↦ absurd
    hi (Nat.not_lt_zero i)⟩
  let g : SurfaceModel 0 0 0 → OnePoint EuclideanPlane := Quot.lift (fun p ↦ p.1) (fun p q hr ↦ by
    cases hr with
    | handle i hi => exact absurd hi (Nat.not_lt_zero i)
    | crosscap i hi => exact absurd hi (Nat.not_lt_zero i))
  have hfc : Continuous f := continuous_quot_mk.comp (Continuous.subtype_mk continuous_id _)
  have hgc : Continuous g := continuous_quot_lift _ continuous_subtype_val
  exact ⟨e.trans ⟨⟨f, g, fun x ↦ rfl, fun x ↦ by
    induction x using Quot.ind with
    | mk p => rfl⟩, hfc, hgc⟩⟩

section Inner

variable {T : Type} [TopologicalSpace T] [T2Space T]

theorem isCell_point [Nonempty T] (hT : IsClosedSurface T) (p : T) : IsCell T {p} := by
  obtain ⟨e, hs, ht, -⟩ := GM19.exists_oph (f := id) (s := {p}ᶜ) (t := {p}ᶜ) isOpen_compl_singleton
    continuous_id.continuousOn
    (injOn_id _) (fun u _ hu ↦ by simpa using hu) (by simp)
  exact ⟨T, _, e, {p}, hT, ⟨.refl T⟩, finite_singleton _, by simp, hs, ht⟩

/-- The inside of a closed disc of a closed surface, without finitely many disjoint closed discs in
the disc that touch the
boundary in at most one point, is a sphere without a finite set. -/
theorem exists_inner_region (hT : IsClosedSurface T) {D : Set T} (hD : IsClosedDisc D) {𝓘 : Set
  (Set T)} (hf : 𝓘.Finite)
    (hd : ∀ E ∈ 𝓘, IsClosedDisc E) (hp : 𝓘.PairwiseDisjoint id) (hsub : ∀ E ∈ 𝓘, E ⊆ D) (ht :
      (⋃₀ 𝓘 ∩ discBd D).Subsingleton) :
    ∃ (T' : Type) (_ : TopologicalSpace T') (e : OpenPartialHomeomorph T T')
      (P : Set T'), IsClosedSurface T' ∧
      ConnectedSpace T' ∧ Nonempty (T' ≃ₜ SurfaceModel 0 0 0) ∧ P.Finite ∧ e.source
        = discInt D \ ⋃₀ 𝓘 ∧ e.target = Pᶜ := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : CompactSpace T := hT.1
  set A := discInt D with hA
  have hAo : IsOpen A := hD.isOpen_discInt hman
  have hsph : IsSphere (OnePoint A) := isSphere_onePoint (isOpenDisc_discInt hman hD)
  have hT₀ := (IsSphere.isClosedSurface hsph).1
  have : T2Space (OnePoint A) := hT₀.2.1
  have hrc : Continuous (collapse A) := continuous_collapse hAo
  have hrinj : ∀ {x y}, x ∈ A → y ∈ A → collapse A x = collapse A y → x = y := fun hx hy he ↦ by
    rw [collapse_of_mem hx, collapse_of_mem hy] at he
    exact congrArg Subtype.val (OnePoint.coe_injective he)
  have hrne : ∀ {x y}, x ∈ A → y ∉ A → collapse A x ≠ collapse A y := fun hx hy he ↦ by
    rw [collapse_of_mem hx, collapse_of_notMem hy] at he
    exact OnePoint.coe_ne_infty _ he
  have hoff : ∀ {x E}, E ∈ 𝓘 → x ∈ E → x ∉ A → x ∈ ⋃₀ 𝓘 ∩ discBd D := fun {x E} hE hx hxA ↦ by
    refine ⟨⟨E, hE, hx⟩, ?_⟩
    by_contra hn
    exact hxA ⟨hsub E hE hx, hn⟩
  have hinjE : ∀ E ∈ 𝓘, InjOn (collapse A) E := fun E hE x hx y hy he ↦ by
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · exact hrinj hxA hyA he
    · exact absurd he (hrne hxA hyA)
    · exact absurd he.symm (hrne hyA hxA)
    · exact ht (hoff hE hx hxA) (hoff hE hy hyA)
  let 𝓐 : Set (Set (OnePoint A)) := (fun E ↦ collapse A '' E) '' 𝓘
  have hdA : ∀ E ∈ 𝓐, IsClosedDisc E := by
    rintro _ ⟨E, hE, rfl⟩
    exact (isClosedDisc_image_injOn (hd E hE) hrc.continuousOn (hinjE E hE)).1
  have hpA : 𝓐.PairwiseDisjoint id := by
    rintro _ ⟨E₁, h₁, rfl⟩ _ ⟨E₂, h₂, rfl⟩ hn
    have hne : E₁ ≠ E₂ := fun h ↦ hn (h ▸ rfl)
    refine disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · have : y = x := hrinj hyA hxA he
      exact disjoint_left.1 (hp h₁ h₂ hne) hx (this ▸ hy)
    · exact hrne hxA hyA he.symm
    · exact hrne hyA hxA he
    · have : x = y := ht (hoff h₁ hx hxA) (hoff h₂ hy hyA)
      exact disjoint_left.1 (hp h₁ h₂ hne) hx (this ▸ hy)
  have : Nonempty (OnePoint A) := ⟨∞⟩
  obtain ⟨T', tT', e₁, P, hT', ⟨hom⟩, hP, -, hs₁, ht₁⟩ := exists_cell_region hT₀ (Y := {∞})
    (fun c _ ↦ by rw [image_singleton]; exact isCell_point hT₀ _) (hf.image _) hdA hpA
    (fun E _ ↦ subsingleton_of_subset_singleton inter_subset_right)
  obtain ⟨hsn⟩ := nonempty_homeomorph_of_isSphere hsph
  have : Nonempty T := by
    obtain ⟨z, hz⟩ := hD.nonempty_discInt
    exact ⟨z⟩
  have him : ∀ u ⊆ A, collapse A '' u = (fun a : A ↦ (a : OnePoint A)) '' (Subtype.val ⁻¹' u)
    := fun u hu ↦ by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hu hx⟩, hx, (collapse_of_mem (hu hx)).symm⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a.1, ha, collapse_of_mem a.2⟩
  have ho : ∀ u ⊆ A, IsOpen u → IsOpen (collapse A '' u) := fun u hu huo ↦ by
    rw [him u hu]
    exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (huo.preimage continuous_subtype_val)
  have himg : collapse A '' A = {∞}ᶜ := by
    rw [him A Subset.rfl]
    ext z
    induction z using OnePoint.rec with
    | infty => simp
    | coe a => simp
  obtain ⟨e₀, hs₀, ht₀, heq⟩ := GM19.exists_oph hAo hrc.continuousOn (fun x hx y hy he ↦ hrinj hx
    hy he) ho himg
  · have := (IsSphere.isClosedSurface hsph).2
    refine ⟨T', tT', e₀.trans e₁, P, hT', hom.symm.surjective.connectedSpace hom.symm.continuous,
      ⟨hom.trans hsn⟩, hP, ?_, ?_⟩
    · ext x
      rw [e₀.trans_source, hs₀, hs₁]
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_union, mem_singleton_iff,
        not_or, Set.mem_sdiff]
      constructor
      · rintro ⟨hx, -, hn⟩
        refine ⟨hx, ?_⟩
        rintro ⟨E, hE, hxE⟩
        refine hn ⟨_, ⟨E, hE, rfl⟩, ?_⟩
        rw [heq hx]
        exact mem_image_of_mem _ hxE
      · rintro ⟨hx, hn⟩
        refine ⟨hx, ?_, ?_⟩
        · rw [heq hx, collapse_of_mem hx]
          exact OnePoint.coe_ne_infty _
        · rintro ⟨_, ⟨E, hE, rfl⟩, ⟨y, hy, he⟩⟩
          rw [heq hx] at he
          by_cases hyA : y ∈ A
          · exact hn ⟨E, hE, hrinj hyA hx he ▸ hy⟩
          · exact hrne hx hyA he.symm
    · ext z
      rw [e₀.trans_target, ht₁, ht₀]
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
      constructor
      · exact fun h ↦ h.1
      · intro hz
        refine ⟨hz, fun hi ↦ ?_⟩
        have hzt : z ∈ e₁.target := by rw [ht₁]; exact hz
        have := e₁.map_target hzt
        rw [hs₁] at this
        exact this (Or.inl hi)

/-- A point of an `O`-arc is a limit of the other points of the arc. -/
theorem mem_closure_oArc_sdiff {F : Set T} (hF : IsOArc F) {y : T} (hy : y ∈ F) : y ∈ closure
  (F \ {y}) := by
  obtain ⟨φ⟩ := hF
  have : ConnectedSpace F := φ.surjective.connectedSpace φ.continuous
  have : Nontrivial Circle := ⟨1, Circle.exp Real.pi, fun h ↦ by
    have := congrArg (fun z : Circle ↦ (z : ℂ)) h
    simp at this
    norm_num at this⟩
  have : Nontrivial F := φ.injective.nontrivial
  have hne : (𝓝[≠] (⟨y, hy⟩ : F)).NeBot :=
    ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space _
  have hcl : (⟨y, hy⟩ : F) ∈ closure ({⟨y, hy⟩}ᶜ : Set F) := mem_closure_iff_nhdsWithin_neBot.2 hne
  have := image_closure_subset_closure_image continuous_subtype_val (mem_image_of_mem _ hcl)
  refine closure_mono ?_ this
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z.2, fun h ↦ hz (Subtype.ext h)⟩

end Inner

section Fragment

variable {S Shat Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  [TopologicalSpace Y]
  [T2Space Y] {ψ : Y → S} {K : Drawing S}

omit [T2Space S] in
/-- If the boundary of a closed disc `D` lies in `S`, then a pasted disc is in `D` or misses the
inside of `D`. -/
theorem IsCappedSurface.side (hS : IsSurface S) (cap : IsCappedSurface S Shat) {D : Set Shat}
  (hD : IsClosedDisc D)
    (h : discBd D ⊆ range cap.emb) {Θ : Set S} (hΘ : Θ ∈ cuffs S) :
    closure (cap.cuffDisc Θ) ⊆ D ∨ Disjoint (closure (cap.cuffDisc Θ)) (discInt D) := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hE := cap.cuffDisc_closedDisc Θ hΘ
  have hC : IsPreconnected (cap.cuffDisc Θ) := by
    rw [cap.cuffDisc_eq_discInt hS hΘ]
    exact hE.isPreconnected_discInt
  have hbd : Disjoint (cap.cuffDisc Θ) (discBd D) := disjoint_left.2 fun x hx hb ↦ cap.notMem_range
    hΘ hx (h hb)
  rcases hD.side hman hC hbd with hin | hout
  · exact Or.inl (closure_minimal (hin.trans (discInt_subset _)) hD.isClosed)
  · refine Or.inr (disjoint_left.2 fun x hx hxi ↦ ?_)
    obtain ⟨z, hz, hzC⟩ := _root_.mem_closure_iff.1 hx _ (hD.isOpen_discInt hman) hxi
    exact disjoint_left.1 hout hzC (discInt_subset _ hz)

omit [T2Space Y] in
/-- **The fragment inside a disc.** Let `D` be a closed disc whose boundary lies in `S` and holds
`K`, and is otherwise in the pasted
discs. Let the pasted discs in `D` touch the boundary of `D` in at most one point. Then one fragment
has image `D ∩ S`, and it caps
to a sphere. -/
theorem exists_inner_fragment (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hY : IsSurface Y)
  (hψ : IsCutMap ψ K.U)
    {D : Set Shat} (hD : IsClosedDisc D) (hK : cap.emb '' K.U ⊆ discBd D)
      (hR : discBd D ⊆ cap.discs ∪ cap.emb '' K.U)
    (hrange : discBd D ⊆ range cap.emb)
    (ht : ((⋃ Θ ∈ {Θ ∈ cuffs S | closure (cap.cuffDisc Θ) ⊆ D}, closure
      (cap.cuffDisc Θ)) ∩ discBd D).Subsingleton) :
    ∃ y : Y, ψ '' connectedComponent y = cap.emb ⁻¹' D ∧ ∀ (Shat₁ : Type) [TopologicalSpace Shat₁],
      IsCappedSurface (connectedComponent y) Shat₁ → Nonempty (Shat₁ ≃ₜ SurfaceModel 0 0 0) := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hfc : (cuffs S).Finite := (cuff_statement S hS).2.1
  have : CompactSpace Shat := hT.1
  have : CompactSpace S := hS.1
  set 𝓣 : Set (Set S) := {Θ ∈ cuffs S | closure (cap.cuffDisc Θ) ⊆ D} with h𝓣
  have hf𝓣 : 𝓣.Finite := hfc.subset fun _ h ↦ h.1
  let E : Set S → Set Shat := fun Θ ↦ closure (cap.cuffDisc Θ)
  have hUn : ⋃₀ (E '' 𝓣) = ⋃ Θ ∈ 𝓣, E Θ := sUnion_image _ _
  have hdisj : (E '' 𝓣).PairwiseDisjoint id := by
    rintro _ ⟨Θ₁, h₁, rfl⟩ _ ⟨Θ₂, h₂, rfl⟩ hn
    exact cap.cuffDisc_disjoint Θ₁ h₁.1 Θ₂ h₂.1 fun h ↦ hn (h ▸ rfl)
  obtain ⟨T', tT', e, P, hT', hconn, ⟨hom⟩, hP, hs, ht'⟩ := exists_inner_region hT hD (𝓘 := E '' 𝓣)
    (hf𝓣.image _)
    (by rintro _ ⟨Θ, hΘ, rfl⟩; exact cap.cuffDisc_closedDisc Θ hΘ.1) hdisj
      (by rintro _ ⟨Θ, hΘ, rfl⟩; exact hΘ.2)
    (by rw [hUn]; exact ht)
  set X : Set Shat := (discInt D \ ⋃₀ (E '' 𝓣))ᶜ with hX
  have hdc : IsClosed cap.discs := hfc.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hKc : IsClosed (cap.emb '' K.U) := (K.isClosed_U.isCompact.image
    cap.isEmbedding.continuous).isClosed
  have hsub : cap.discs ∪ cap.emb '' K.U ⊆ X := by
    rintro x (hx | hx) ⟨hi, hn⟩
    · obtain ⟨Θ, hΘ, hxΘ⟩ := mem_iUnion₂.1 hx
      rcases cap.side hS hD hrange hΘ with h | h
      · exact hn ⟨_, ⟨Θ, ⟨hΘ, h⟩, rfl⟩, hxΘ⟩
      · exact disjoint_left.1 h hxΘ hi
    · exact hi.2 (hK hx)
  have hop : IsOpen (X \ (cap.discs ∪ cap.emb '' K.U)) := by
    have : X \ (cap.discs ∪ cap.emb '' K.U) = Dᶜ \ (cap.discs ∪ cap.emb '' K.U) := by
      ext x
      constructor
      · rintro ⟨hx, hn⟩
        refine ⟨fun hxD ↦ ?_, hn⟩
        by_cases hb : x ∈ discBd D
        · exact hn (hR hb)
        · by_contra -
          refine hx ⟨⟨hxD, hb⟩, ?_⟩
          rintro ⟨_, ⟨Θ, hΘ, rfl⟩, hxΘ⟩
          exact hn (Or.inl (mem_biUnion hΘ.1 hxΘ))
      · rintro ⟨hx, hn⟩
        exact ⟨fun h ↦ hx (discInt_subset _ h.1), hn⟩
    rw [this]
    exact hD.isClosed.isOpen_compl.sdiff (hdc.union hKc)
  obtain ⟨y, hy, hcap, -⟩ := exists_fragment_of_region hS cap hY hψ hT' hP e
    (by rw [hs, hX, compl_compl]) ht' hsub hop
  refine ⟨y, ?_, fun Shat₁ _ cap₁ ↦ ?_⟩
  · rw [hy]
    set A := cap.emb ⁻¹' Xᶜ with hA
    set G := cap.emb ⁻¹' discInt D with hG
    have hGo : IsOpen G := (hD.isOpen_discInt hman).preimage cap.isEmbedding.continuous
    have hGA : G ∩ (bd S)ᶜ ⊆ A := by
      rintro x ⟨hxG, hxb⟩
      change cap.emb x ∈ Xᶜ
      rw [hX, compl_compl]
      refine ⟨hxG, ?_⟩
      rintro ⟨_, ⟨Θ, hΘ, rfl⟩, hxΘ⟩
      have hn : cap.emb x ∈ cap.discsᶜ := by
        rw [show cap.discsᶜ = _ from cap.compl_eq_image hS]
        exact mem_image_of_mem _ hxb
      exact hn (mem_biUnion hΘ.1 hxΘ)
    have hGcl : closure G ⊆ closure A :=
      closure_minimal (((dense_interior' hS).open_subset_closure_inter hGo).trans
        (closure_mono hGA)) isClosed_closure
    have hAsub : A ⊆ cap.emb ⁻¹' D := by
      intro x hx
      have hx' : cap.emb x ∈ Xᶜ := hx
      rw [hX, compl_compl] at hx'
      exact discInt_subset D hx'.1
    have hnear : ∀ {x}, cap.emb x ∈ discBd D → cap.emb x ∉ ⋃ Θ ∈ 𝓣, E Θ → x ∈ closure G := by
      intro x hxb hxn
      have hV : IsOpen (⋃ Θ ∈ 𝓣, E Θ)ᶜ := (hf𝓣.isClosed_biUnion fun _ _ ↦
        isClosed_closure).isOpen_compl
      rw [cap.isEmbedding.closure_eq_preimage_closure_image, mem_preimage, _root_.mem_closure_iff]
      intro O hO hxO
      obtain ⟨w, hw, hwi⟩ := _root_.mem_closure_iff.1 (hD.subset_closure_discInt
        (Surface.discBd_subset _ hxb)) (O ∩ _) (hO.inter hV) ⟨hxO, hxn⟩
      refine ⟨w, hw.1, ?_⟩
      have hwr : w ∈ range cap.emb := by
        by_contra hn
        have hn' : w ∈ (range cap.emb)ᶜ := hn
        rw [cap.compl_eq] at hn'
        obtain ⟨Θ, hΘ, hwΘ⟩ := mem_iUnion₂.1 hn'
        rcases cap.side hS hD hrange hΘ with h | h
        · exact hw.2 (mem_biUnion (show Θ ∈ 𝓣 from ⟨hΘ, h⟩) (subset_closure hwΘ))
        · exact disjoint_left.1 h (subset_closure hwΘ) hwi
      obtain ⟨x', rfl⟩ := hwr
      exact ⟨x', hwi, rfl⟩
    apply Subset.antisymm
    · exact closure_minimal hAsub (hD.isClosed.preimage cap.isEmbedding.continuous)
    · intro x hx
      refine hGcl ?_
      by_cases hxi : x ∈ G
      · exact subset_closure hxi
      have hxb : cap.emb x ∈ discBd D := by
        by_contra hn
        exact hxi ⟨hx, hn⟩
      by_cases hxT : cap.emb x ∈ ⋃ Θ ∈ 𝓣, E Θ
      · have hlim := mem_closure_oArc_sdiff hD.isOArc_discBd hxb
        rw [cap.isEmbedding.closure_eq_preimage_closure_image, mem_preimage]
        refine closure_minimal ?_ isClosed_closure (closure_mono (Subset.rfl) hlim)
        rintro z ⟨hzb, hne⟩
        obtain ⟨x', rfl⟩ := hrange hzb
        have hx'n : cap.emb x' ∉ ⋃ Θ ∈ 𝓣, E Θ := fun h ↦ hne (ht ⟨h, hzb⟩ ⟨hxT, hxb⟩)
        have := hnear hzb hx'n
        rw [cap.isEmbedding.closure_eq_preimage_closure_image] at this
        exact this
      · exact hnear hxb hxT
  · obtain ⟨f⟩ := hcap Shat₁ cap₁
    exact ⟨f.trans hom⟩

end Fragment

end GraphMinor.GM19

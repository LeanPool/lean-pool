/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PullLift
public import LeanPool.GraphMinor.GM19.CapExists
public import LeanPool.GraphMinor.GM19.DiscSides
public import LeanPool.GraphMinor.GM19.RadialExists

/-!
# A component of a cut surface is a fragment

Cutting a surface along a closed set `F` gives a surface `Y` and a map `ψ`. We show that each
component of
`Y` is a fragment in the sense of `IsCuttingFragment`. The point that takes some work is that the
interior
of a connected surface is connected (`isConnected_interior`), which we get by removing the capping
discs
from the capped surface one at a time.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

section Interior

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]

omit [T2Space S] in
/-- Removing finitely many of the capping discs leaves a connected open set. -/
theorem IsCappedSurface.isPreconnected_compl (cap : IsCappedSurface S Shat) {𝓒 : Set (Set S)}
    (h𝓒 : 𝓒.Finite) (hsub : 𝓒 ⊆ cuffs S) :
    IsOpen (⋃ Θ ∈ 𝓒, closure (cap.cuffDisc Θ))ᶜ ∧
      IsPreconnected (⋃ Θ ∈ 𝓒, closure (cap.cuffDisc Θ))ᶜ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  induction 𝓒, h𝓒 using Set.Finite.induction_on with
  | empty => simpa using isPreconnected_univ
  | @insert Θ 𝓒 hΘ hfin ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (fun x hx ↦ hsub (mem_insert_of_mem _ hx))
    have hΘc : Θ ∈ cuffs S := hsub (mem_insert _ _)
    have heq : (⋃ Θ' ∈ insert Θ 𝓒, closure (cap.cuffDisc Θ'))ᶜ =
        (⋃ Θ' ∈ 𝓒, closure (cap.cuffDisc Θ'))ᶜ \ closure (cap.cuffDisc Θ) := by
      rw [biUnion_insert]
      ext x
      simp only [mem_compl_iff, mem_union, not_or, mem_sdiff]
      tauto
    rw [heq]
    refine ⟨ih₁.sdiff isClosed_closure, isPreconnected_sdiff_disc hT ih₁ ih₂
      (cap.cuffDisc_closedDisc Θ hΘc) ?_⟩
    intro x hx hxU
    obtain ⟨Θ', hΘ', hxΘ'⟩ := mem_iUnion₂.mp hxU
    have hne : Θ ≠ Θ' := fun h ↦ hΘ (h ▸ hΘ')
    exact disjoint_left.mp (cap.cuffDisc_disjoint Θ hΘc Θ' (hsub (mem_insert_of_mem _ hΘ')) hne) hx
      hxΘ'

omit [T2Space S] [T2Space Shat] in
/-- The complement of the capping discs is the image of the interior. -/
theorem IsCappedSurface.compl_eq_image (hS : IsSurface S) (cap : IsCappedSurface S Shat) :
    (⋃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ))ᶜ = cap.emb '' (bd S)ᶜ := by
  ext y
  constructor
  · intro hy
    have hyr : y ∈ range cap.emb := by
      by_contra hn
      have hn' : y ∈ (range cap.emb)ᶜ := hn
      rw [cap.compl_eq] at hn'
      obtain ⟨Θ, hΘ, hyΘ⟩ := mem_iUnion₂.mp hn'
      exact hy (mem_biUnion hΘ (subset_closure hyΘ))
    obtain ⟨x, rfl⟩ := hyr
    refine ⟨x, fun hxb ↦ ?_, rfl⟩
    rw [← sUnion_cuffs] at hxb
    obtain ⟨Θ, hΘ, hxΘ⟩ := hxb
    refine hy (mem_biUnion hΘ ?_)
    rw [cap.closure_cuffDisc hS hΘ]
    exact Or.inr (mem_image_of_mem _ hxΘ)
  · rintro ⟨x, hx, rfl⟩ hy
    obtain ⟨Θ, hΘ, hyΘ⟩ := mem_iUnion₂.mp hy
    rw [cap.closure_cuffDisc hS hΘ] at hyΘ
    rcases hyΘ with hy | ⟨z, hz, hzx⟩
    · have : cap.emb x ∈ (range cap.emb)ᶜ := by
        rw [cap.compl_eq]
        exact mem_biUnion hΘ hy
      exact this (mem_range_self x)
    · have := cap.isEmbedding.injective hzx
      exact hx (this ▸ sUnion_cuffs (S := S) ▸ ⟨Θ, hΘ, hz⟩)

omit [T2Space S] in
/-- A connected surface has an interior point. If it has a cuff, then a closed disc slightly larger
than
the capping disc has a boundary point outside all capping discs. -/
theorem nonempty_interior (hS : IsSurface S) [ConnectedSpace S] : (bd S)ᶜ.Nonempty := by
  by_cases hbd : (cuffs S).Nonempty
  · obtain ⟨Shat, _, ⟨cap⟩⟩ := exists_cappedSurface _ S hS inferInstance rfl
    have : T2Space Shat := cap.isSurface.2.1
    have hT := cap.isClosedSurface
    have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
    obtain ⟨Θ, hΘ⟩ := hbd
    have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
    set Δ := closure (cap.cuffDisc Θ) with hΔdef
    have hΔ : IsClosedDisc Δ := cap.cuffDisc_closedDisc Θ hΘ
    set W : Set Shat := (⋃ Θ' ∈ cuffs S \ {Θ}, closure (cap.cuffDisc Θ'))ᶜ with hW
    have hWo : IsOpen W := ((hfin.subset sdiff_subset).isClosed_biUnion fun _ _ ↦
      isClosed_closure).isOpen_compl
    have hsubW : Δ ⊆ W := by
      intro x hx hxU
      obtain ⟨Θ', hΘ', hxΘ'⟩ := mem_iUnion₂.mp hxU
      exact disjoint_left.mp (cap.cuffDisc_disjoint Θ hΘ Θ' hΘ'.1 (Ne.symm hΘ'.2)) hx hxΘ'
    obtain ⟨Δ', hΔ', hin, hsub⟩ := Surface.exists_disc_around hman hΔ (fun x _ ↦ hT.2.2 x) hWo
      ((Surface.discBd_subset _).trans hsubW)
    obtain ⟨p⟩ := hΔ'.isOArc_discBd
    have hy := (p 1).2
    set y := (p 1).1
    have hyΔ : y ∉ Δ := fun h ↦ (hin h).2 hy
    have hyW : y ∈ W := (hsub (Surface.discBd_subset _ hy)).elim (fun h ↦ absurd h hyΔ) id
    have hyG : y ∈ (⋃ Θ ∈ cuffs S, closure (cap.cuffDisc Θ))ᶜ := by
      intro hyU
      obtain ⟨Θ', hΘ', hyΘ'⟩ := mem_iUnion₂.mp hyU
      by_cases h : Θ' = Θ
      · exact hyΔ (by rw [hΔdef, ← h]; exact hyΘ')
      · exact hyW (mem_biUnion (show Θ' ∈ cuffs S \ {Θ} from ⟨hΘ', h⟩) hyΘ')
    rw [cap.compl_eq_image hS] at hyG
    obtain ⟨x, hx, -⟩ := hyG
    exact ⟨x, hx⟩
  · obtain ⟨x⟩ : Nonempty S := inferInstance
    refine ⟨x, fun hx ↦ hbd ?_⟩
    rw [← sUnion_cuffs] at hx
    obtain ⟨Θ, hΘ, -⟩ := hx
    exact ⟨Θ, hΘ⟩

omit [T2Space S] in
/-- **The interior of a connected surface is connected.** -/
theorem isConnected_interior (hS : IsSurface S) [ConnectedSpace S] : IsConnected (bd S)ᶜ := by
  obtain ⟨Shat, _, ⟨cap⟩⟩ := exists_cappedSurface _ S hS inferInstance rfl
  have : T2Space Shat := cap.isSurface.2.1
  have h := (cap.isPreconnected_compl (cuff_statement S hS).2.1 subset_rfl).2
  rw [cap.compl_eq_image hS, cap.isEmbedding.isInducing.isPreconnected_image] at h
  exact ⟨nonempty_interior hS, h⟩

end Interior

section Component

variable {S Y : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y] [T2Space Y]
  {ψ : Y → S} {F : Set S}

omit [T2Space Y] in
/-- An interior point off the preimage of `F` maps to an interior point, since `ψ` is a
homeomorphism off
`F`. -/
theorem bd_of_bd_cutMap [CompactSpace Y] (hψ : IsCutMap ψ F) (hF : IsClosed F) {z : Y}
  (hz : z ∈ bd Y) (hzF : ψ z ∉ F) : ψ z ∈ bd S := by
  intro hi
  apply hz
  obtain ⟨h1, h2, h3, -, -⟩ := hψ
  obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := hi.exists_subset hF.isOpen_compl hzF
  have hcl : IsClosedMap ψ := h1.isClosedMap
  have hbij : Function.Bijective (U.restrictPreimage ψ) := by
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

omit [T2Space Y] in
theorem isInteriorPoint_image [CompactSpace Y] (hψ : IsCutMap ψ F) (hF : IsClosed F) {z : Y}
    (hz : IsInteriorPoint z) (hzF : ψ z ∉ F) : IsInteriorPoint (ψ z) := by
  obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := hz.exists_subset (hF.isOpen_compl.preimage hψ.1) hzF
  have hV : IsOpen (ψ '' U) := isOpen_image_of_isCutMap hψ hsub hU
  have hpre : ψ ⁻¹' (ψ '' U) = U := by
    ext y
    constructor
    · rintro ⟨u, hu, huy⟩
      by_cases hyF : ψ y ∈ F
      · exact absurd (huy ▸ hyF) (hsub hu)
      · exact hψ.2.2.1 (hsub hu) hyF huy ▸ hu
    · exact fun hy ↦ mem_image_of_mem ψ hy
  have hbij : Function.Bijective ((ψ '' U).restrictPreimage ψ) := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ he
      have he' : ψ a = ψ b := congrArg Subtype.val he
      have ha' : a ∈ U := hpre ▸ ha
      have hb' : b ∈ U := hpre ▸ hb
      exact Subtype.ext (hψ.2.2.1 (hsub ha') (hsub hb') he')
    · rintro ⟨_, a, ha, rfl⟩
      exact ⟨⟨a, mem_image_of_mem ψ ha⟩, rfl⟩
  have hh : IsHomeomorph ((ψ '' U).restrictPreimage ψ) :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨hψ.1.restrictPreimage, (isClosedMap_of_isCutMap hψ).restrictPreimage _, hbij⟩
  exact ⟨ψ '' U, hV, mem_image_of_mem ψ hx,
    ⟨hh.homeomorph.symm.trans ((Homeomorph.setCongr hpre).trans e)⟩⟩

omit [T2Space Y] in
/-- **A component of a cut surface is a fragment.** -/
theorem isCuttingFragment_of_cut (_hS : IsSurface S) (hY : IsSurface Y)
  (hψ : IsCutMap ψ F) {K : Drawing S}
    (hK : K.U = F) (y : Y) :
    IsCuttingFragment S K (connectedComponent y) (fun x ↦ ψ x.1) := by
  have hF : IsClosed F := hK ▸ K.isClosed_U
  have : CompactSpace Y := hY.1
  have : LocallyConnectedSpace Y := IsSurface.locallyConnected hY
  have hWo : IsOpen (connectedComponent y) := isOpen_connectedComponent
  have hWc : IsClopen (connectedComponent y) := ⟨isClosed_connectedComponent, hWo⟩
  have hbdW : ∀ {x : connectedComponent y}, x ∈ bd (connectedComponent y) ↔ x.1 ∈ bd Y :=
    mem_bd_sub hWo
  have hoff : ∀ {x : Y}, x ∉ bd Y → ψ x ∉ F := fun hx hxF ↦ hx (hψ.2.2.2.2 hxF)
  have hint : ∀ {x : Y}, x ∉ bd Y → ψ x ∉ bd S := by
    intro x hx
    have hxi : IsInteriorPoint x := by
      by_contra hn
      exact hx hn
    exact fun hb ↦ hb (isInteriorPoint_image hψ hF hxi (hoff hx))
  have hbdmap : ∀ {x : Y}, x ∈ bd Y → ψ x ∈ bd S ∪ K.U := by
    intro x hx
    by_cases hxF : ψ x ∈ F
    · exact Or.inr (hK ▸ hxF)
    · exact Or.inl (bd_of_bd_cutMap hψ hF hx hxF)
  have hconn : ConnectedSpace (connectedComponent y) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hsurf : IsSurface (connectedComponent y) := isSurface_sub hY hWc
  have hdis : Disjoint ((fun x : connectedComponent y ↦ ψ x.1) '' (bd (connectedComponent y))ᶜ)
      (bd S ∪ K.U) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ (hb | hKU)
    · exact hint (fun h ↦ hx (hbdW.mpr h)) hb
    · exact hoff (fun h ↦ hx (hbdW.mpr h)) (hK ▸ hKU)
  have hcont : Continuous fun x : connectedComponent y ↦ ψ x.1 :=
    hψ.1.comp continuous_subtype_val
  refine ⟨hsurf, hconn, hcont, ?_, ?_, hdis, ?_, ?_⟩
  · intro a ha b hb hab
    exact Subtype.ext (hψ.2.2.1 (hoff fun h ↦ ha (hbdW.mpr h)) (hoff fun h ↦ hb (hbdW.mpr h)) hab)
  · intro v
    have hfin : (ψ ⁻¹' {v}).Finite := hψ.2.2.2.1 v
    exact Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset (by
      rintro _ ⟨x, hx, rfl⟩
      exact hx)) Subtype.val_injective.injOn
  · rintro _ ⟨x, hx, rfl⟩
    exact hbdmap (hbdW.mp hx)
  · -- The image of the interior is connected, and it is open and closed in the complement.
    set R := (fun x : connectedComponent y ↦ ψ x.1) '' (bd (connectedComponent y))ᶜ with hRdef
    obtain ⟨z, hz⟩ := nonempty_interior hsurf
    have hzZ : ψ z.1 ∈ (bd S ∪ K.U)ᶜ := fun h ↦
      disjoint_left.mp hdis (mem_image_of_mem _ hz) h
    have hRc : IsPreconnected R := (isConnected_interior hsurf).isPreconnected.image _
      hcont.continuousOn
    have hRsub : R ⊆ (bd S ∪ K.U)ᶜ := fun x hx h ↦ disjoint_left.mp hdis hx h
    have hRo : IsOpen R := by
      have hset : R = ψ '' (Subtype.val '' (bd (connectedComponent y))ᶜ) := by
        rw [hRdef, image_image]
      rw [hset]
      refine isOpen_image_of_isCutMap hψ ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact hoff fun h ↦ hx (hbdW.mpr h)
      · exact hWo.isOpenMap_subtype_val _ (cuff_statement _ hsurf).1.isOpen_compl
    have hRcl : closure R ∩ (bd S ∪ K.U)ᶜ ⊆ R := by
      rintro w ⟨hw, hwZ⟩
      have himg : IsClosed (ψ '' connectedComponent y) :=
        isClosedMap_of_isCutMap hψ _ isClosed_connectedComponent
      have hRW : R ⊆ ψ '' connectedComponent y := by
        rintro _ ⟨x, -, rfl⟩
        exact mem_image_of_mem ψ x.2
      obtain ⟨a, ha, rfl⟩ := closure_minimal hRW himg hw
      exact ⟨⟨a, ha⟩, fun hb ↦ hwZ (hbdmap (hbdW.mp hb)), rfl⟩
    refine ⟨ψ z.1, hzZ, ?_⟩
    apply Subset.antisymm
    · have hcomp := isPreconnected_connectedComponentIn (F := (bd S ∪ K.U)ᶜ) (x := ψ z.1)
      refine hcomp.subset_left_of_subset_union hRo isClosed_closure.isOpen_compl
        (disjoint_left.mpr fun w hw hn ↦ hn (subset_closure hw)) (fun x hx ↦ ?_)
        ⟨ψ z.1, mem_connectedComponentIn hzZ, mem_image_of_mem _ hz⟩
      by_cases hxc : x ∈ closure R
      · exact Or.inl (hRcl ⟨hxc, connectedComponentIn_subset _ _ hx⟩)
      · exact Or.inr hxc
    · exact hRc.subset_connectedComponentIn (mem_image_of_mem _ hz) hRsub

end Component

end GraphMinor.GM19

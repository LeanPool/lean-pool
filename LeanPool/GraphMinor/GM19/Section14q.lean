/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14p

/-!
# Graph Minors XIX, Section 14: the surface `Σ'`

Let `e` be an embedding of `Σ` in `Σ̂`, and let `𝒲` be a finite set of disjoint closed discs whose
boundaries lie in the interior of `Σ`,
such that the rest of `Σ̂`, and the boundary of `Σ`, lie inside the discs. We delete the insides of
the discs from `Σ`. The paper says
that the result `Σ'` is a surface with `Σ̂' ≅ Σ̂`. We prove this here, and we find the cuffs of
`Σ'`: they are the boundaries of the discs.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat]

/-- The hypotheses on the discs. -/
structure IsCutData (e : S → Shat) (𝒲 : Set (Set Shat)) : Prop where
  emb : IsClosedEmbedding e
  finite : 𝒲.Finite
  disc : ∀ W ∈ 𝒲, IsClosedDisc W
  disj : 𝒲.PairwiseDisjoint id
  bd_mem : ∀ W ∈ 𝒲, discBd W ⊆ e '' (bd S)ᶜ
  cover : (⋃ W ∈ 𝒲, discInt W)ᶜ ⊆ e '' (bd S)ᶜ

/-- The part of `Σ` that we delete. -/
def cutT (e : S → Shat) (𝒲 : Set (Set Shat)) : Set S := e ⁻¹' ⋃ W ∈ 𝒲, discInt W

/-- The boundary of `Σ'`, as a subset of `Σ`. -/
def cutF (e : S → Shat) (𝒲 : Set (Set Shat)) : Set S := e ⁻¹' ⋃ W ∈ 𝒲, discBd W

namespace IsCutData

variable {e : S → Shat} {𝒲 : Set (Set Shat)} (h : IsCutData e 𝒲)
include h

/-- `Σ'` and the complement of the insides of the discs are the same. -/
noncomputable def homeo : ↥(cutT e 𝒲)ᶜ ≃ₜ ↥(⋃ W ∈ 𝒲, discInt W)ᶜ :=
  IsEmbedding.toHomeomorphOfSurjective (f := fun x : ↥(cutT e 𝒲)ᶜ ↦ (⟨e x.1, x.2⟩ : ↥(⋃ W ∈ 𝒲,
    discInt W)ᶜ))
    (by
      refine IsEmbedding.of_comp (Continuous.subtype_mk (h.emb.continuous.comp
        continuous_subtype_val) _) continuous_subtype_val ?_
      exact h.emb.isEmbedding.comp IsEmbedding.subtypeVal)
    (by
      rintro ⟨y, hy⟩
      obtain ⟨x, -, rfl⟩ := h.cover hy
      exact ⟨⟨x, hy⟩, rfl⟩)

omit [T2Space S] [T2Space Shat] in
theorem homeo_val (x : ↥(cutT e 𝒲)ᶜ) : (h.homeo x).1 = e x.1 := rfl

omit [T2Space S] [T2Space Shat] in
theorem bd_subset_T : bd S ⊆ cutT e 𝒲 := fun x hx ↦ by
  by_contra hn
  obtain ⟨y, hy, hxy⟩ := h.cover hn
  exact hy (h.emb.injective hxy ▸ hx)

omit [T2Space S] in
theorem isClosed_bd' {W : Set Shat} (hW : W ∈ 𝒲) : IsClosed (discBd W) := by
  obtain ⟨f⟩ := (h.disc W hW).isOArc_discBd
  have hc : IsCompact (discBd W) := by
    have := isCompact_range (f := fun x : Circle ↦ (f x).1) (by fun_prop)
    rwa [show range (fun x : Circle ↦ (f x).1) = discBd W by
      ext y
      exact ⟨by rintro ⟨x, rfl⟩; exact (f x).2, fun hy ↦ ⟨f.symm ⟨y, hy⟩, by simp⟩⟩] at this
  exact hc.isClosed

variable {Shat' : Type} [TopologicalSpace Shat']

omit [T2Space S] [T2Space Shat] in
/-- `Σ'` is a surface, it is connected, and its boundary is the union of the boundaries of the
discs. -/
theorem surface_facts (hR : IsSurface Shat) [ConnectedSpace Shat] (hbd : bd Shat = ∅) :
    IsClosed (cutT e 𝒲)ᶜ ∧ IsSurface ↥(cutT e 𝒲)ᶜ ∧ bd ↥(cutT e 𝒲)ᶜ = Subtype.val ⁻¹' cutF e 𝒲
      ∧ ConnectedSpace ↥(cutT e 𝒲)ᶜ := by
  have hint : ∀ E ∈ 𝒲, ∀ x ∈ discBd E, IsInteriorPoint x := fun E _ x _ ↦ by
    by_contra hn
    have : x ∈ bd Shat := hn
    rw [hbd] at this
    exact this
  obtain ⟨h₁, h₂, h₃, h₄⟩ := remove_discs hR h.finite h.disc hint h.disj
  refine ⟨?_, isSurface_of_homeo h.homeo.symm h₂, ?_, ?_⟩
  · have : (cutT e 𝒲)ᶜ = e ⁻¹' (⋃ W ∈ 𝒲, discInt W)ᶜ := rfl
    rw [this]
    exact h₁.preimage h.emb.continuous
  · rw [hbd, empty_union] at h₃
    ext x
    have := image_bd h.homeo
    constructor
    · intro hx
      have hm : h.homeo x ∈ bd ↥(⋃ W ∈ 𝒲, discInt W)ᶜ := by
        rw [← this]
        exact mem_image_of_mem _ hx
      rw [h₃] at hm
      exact hm
    · intro hx
      have hm : h.homeo x ∈ bd ↥(⋃ W ∈ 𝒲, discInt W)ᶜ := by
        rw [h₃]
        exact hx
      rw [← this] at hm
      obtain ⟨y, hy, hxy⟩ := hm
      rwa [← h.homeo.injective hxy]
  · exact h.homeo.symm.surjective.connectedSpace h.homeo.symm.continuous

/-- The cuff of `Σ'` at a disc. -/
def cuffAt (e : S → Shat) (𝒲 : Set (Set Shat)) (W : Set Shat) : Set ↥(cutT e 𝒲)ᶜ := Subtype.val ⁻¹'
  (e ⁻¹' discBd W)

omit [T2Space S] [T2Space Shat] in
theorem image_cuffAt {W : Set Shat} (hW : W ∈ 𝒲) : (fun x : ↥(cutT e 𝒲)ᶜ ↦ e x.1) '' cuffAt e 𝒲 W
  = discBd W := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, -, rfl⟩ := h.bd_mem W hW hy
    refine ⟨⟨x, fun hT ↦ ?_⟩, hy, rfl⟩
    obtain ⟨W', hW', hi⟩ := mem_iUnion₂.mp hT
    by_cases e' : W = W'
    · subst e'
      exact hi.2 hy
    · exact disjoint_left.mp (h.disj hW hW' e') (Surface.discBd_subset _ hy) hi.1

omit [T2Space S] [T2Space Shat] in
theorem isPreconnected_cuffAt {W : Set Shat} (hW : W ∈ 𝒲) : IsPreconnected (cuffAt e 𝒲 W) := by
  have hem : IsEmbedding (fun x : ↥(cutT e 𝒲)ᶜ ↦ e x.1) := h.emb.isEmbedding.comp
    IsEmbedding.subtypeVal
  rw [hem.isInducing.isPreconnected_image.symm, h.image_cuffAt hW]
  exact (h.disc W hW).isOArc_discBd.isPreconnected

omit [T2Space S] in
theorem cuffs_eq (hR : IsSurface Shat) [ConnectedSpace Shat] (hbd : bd Shat
  = ∅) : cuffs ↥(cutT e 𝒲)ᶜ = cuffAt e 𝒲 '' 𝒲 := by
  classical
  have hb := (h.surface_facts hR hbd).2.2.1
  have hcl : ∀ W ∈ 𝒲, IsClosed (cuffAt e 𝒲 W) := fun W hW ↦ ((h.isClosed_bd' hW).preimage
    h.emb.continuous).preimage continuous_subtype_val
  have key : ∀ W ∈ 𝒲, ∀ x ∈ cuffAt e 𝒲 W, connectedComponentIn (bd ↥(cutT e 𝒲)ᶜ) x = cuffAt e 𝒲 W
    := by
    intro W hW x hx
    have hsub : cuffAt e 𝒲 W ⊆ bd ↥(cutT e 𝒲)ᶜ := fun y hy ↦ by
      rw [hb]
      exact mem_iUnion₂.mpr ⟨W, hW, hy⟩
    refine Subset.antisymm ?_ ((h.isPreconnected_cuffAt hW).subset_connectedComponentIn hx hsub)
    set R := ⋃ W' ∈ 𝒲 \ {W}, cuffAt e 𝒲 W' with hRdef
    have hRc : IsClosed R := (h.finite.subset sdiff_subset).isClosed_biUnion fun W' hW' ↦ hcl W'
      hW'.1
    have hdis : Disjoint (cuffAt e 𝒲 W) R := by
      refine disjoint_left.mpr fun y hy hyR ↦ ?_
      obtain ⟨W', hW', hyW⟩ := mem_iUnion₂.mp hyR
      exact disjoint_left.mp (h.disj hW hW'.1 (Ne.symm hW'.2)) (Surface.discBd_subset _ hy)
        (Surface.discBd_subset _ hyW)
    have hcov : bd ↥(cutT e 𝒲)ᶜ ⊆ cuffAt e 𝒲 W ∪ R := fun y hy ↦ by
      rw [hb] at hy
      obtain ⟨W', hW', hyW⟩ := mem_iUnion₂.mp hy
      by_cases e' : W' = W
      · exact .inl (e' ▸ hyW)
      · exact .inr (mem_iUnion₂.mpr ⟨W', ⟨hW', e'⟩, hyW⟩)
    intro y hy
    by_contra hny
    have hxb := mem_connectedComponentIn (hsub hx)
    have hsubb : connectedComponentIn (bd ↥(cutT e 𝒲)ᶜ) x ⊆ bd ↥(cutT e 𝒲)ᶜ
      := connectedComponentIn_subset _ _
    obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn _ _
      (hcl W hW) hRc (hsubb.trans hcov)
      ⟨x, hxb, hx⟩ ⟨y, hy, (hcov (hsubb hy)).resolve_left hny⟩
    exact disjoint_left.mp hdis hz₁ hz₂
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := hx
    rw [hb] at hx'
    obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp hx'
    exact ⟨W, hW, (key W hW x hxW).symm⟩
  · rintro ⟨W, hW, rfl⟩
    have hne : (discBd W).Nonempty := (IsOArc.isConnected' (h.disc W hW).isOArc_discBd).nonempty
    rw [← h.image_cuffAt hW] at hne
    obtain ⟨x, hx⟩ := hne.of_image
    refine ⟨x, ?_, key W hW x hx⟩
    rw [hb]
    exact mem_iUnion₂.mpr ⟨W, hW, hx⟩

omit [T2Space S] [T2Space Shat] in
theorem cuffAt_nonempty {W : Set Shat} (hW : W ∈ 𝒲) : (cuffAt e 𝒲 W).Nonempty := by
  have hne : (discBd W).Nonempty := (IsOArc.isConnected' (h.disc W hW).isOArc_discBd).nonempty
  rw [← h.image_cuffAt hW] at hne
  exact hne.of_image

omit [T2Space S] in
theorem closure_discInt {W : Set Shat} (hW : W ∈ 𝒲) : closure (discInt W) = W :=
  Subset.antisymm (closure_minimal (discInt_subset _) (h.disc W hW).isClosed)
    (h.disc W hW).subset_closure_discInt

omit [T2Space S] in
/-- The surface `Σ'` is capped by `Σ̂` itself, with the insides of the discs as the pasted discs. -/
theorem nonempty_capped (hR : IsSurface Shat) [ConnectedSpace Shat] (hbd : bd Shat = ∅) : Nonempty
  (IsCappedSurface ↥(cutT e 𝒲)ᶜ Shat) := by
  classical
  have hcu := h.cuffs_eq hR hbd
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h.surface_facts hR hbd
  have hem : IsEmbedding (fun x : ↥(cutT e 𝒲)ᶜ ↦ e x.1) := h.emb.isEmbedding.comp
    IsEmbedding.subtypeVal
  have hex : ∀ Θ ∈ cuffs ↥(cutT e 𝒲)ᶜ, ∃ W ∈ 𝒲, cuffAt e 𝒲 W = Θ := fun Θ hΘ ↦ by
    rw [hcu] at hΘ
    exact hΘ
  have hinj : ∀ W ∈ 𝒲, ∀ W' ∈ 𝒲, cuffAt e 𝒲 W = cuffAt e 𝒲 W' → W = W' := fun W hW W' hW' he ↦ by
    by_contra hne
    obtain ⟨x, hx⟩ := h.cuffAt_nonempty hW
    exact disjoint_left.mp (h.disj hW hW' hne) (Surface.discBd_subset _ hx)
      (Surface.discBd_subset _ (show x ∈ cuffAt e 𝒲 W' from he ▸ hx))
  let pick : Set ↥(cutT e 𝒲)ᶜ → Set Shat := fun Θ ↦ if hΘ : Θ ∈ cuffs ↥(cutT e 𝒲)ᶜ then
    (hex Θ hΘ).choose else ∅
  have hpick : ∀ Θ (hΘ : Θ ∈ cuffs ↥(cutT e 𝒲)ᶜ), pick Θ ∈ 𝒲 ∧ cuffAt e 𝒲 (pick Θ) = Θ
    := fun Θ hΘ ↦ by
    simp only [pick, dite_eq_left hΘ]
    exact (hex Θ hΘ).choose_spec
  refine ⟨{ isSurface := hR, connected := inferInstance, bd_empty := hbd, emb
    := fun x ↦ e x.1, isEmbedding := hem, cuffDisc := fun Θ ↦ discInt (pick Θ), cuffDisc_closedDisc
      := ?_, cuffDisc_bd := ?_, cuffDisc_disjoint := ?_, compl_eq := ?_ }⟩
  · intro Θ hΘ
    rw [h.closure_discInt (hpick Θ hΘ).1]
    exact h.disc _ (hpick Θ hΘ).1
  · intro Θ hΘ
    obtain ⟨h₅, h₆⟩ := hpick Θ hΘ
    rw [h.closure_discInt h₅, ← h.image_cuffAt h₅, h₆]
  · intro Θ₁ h₅ Θ₂ h₆ hne
    obtain ⟨h₇, h₈⟩ := hpick Θ₁ h₅
    obtain ⟨h₉, h₁₀⟩ := hpick Θ₂ h₆
    rw [h.closure_discInt h₇, h.closure_discInt h₉]
    exact h.disj h₇ h₉ fun he ↦ hne (h₈.symm.trans ((congrArg (cuffAt e 𝒲) he).trans h₁₀))
  · ext y
    constructor
    · intro hy
      have hin : y ∈ ⋃ W ∈ 𝒲, discInt W := by
        by_contra hn
        obtain ⟨x, -, rfl⟩ := h.cover hn
        exact hy ⟨⟨x, hn⟩, rfl⟩
      obtain ⟨W, hW, hyW⟩ := mem_iUnion₂.mp hin
      have hc : cuffAt e 𝒲 W ∈ cuffs ↥(cutT e 𝒲)ᶜ := by
        rw [hcu]
        exact mem_image_of_mem _ hW
      obtain ⟨h₅, h₆⟩ := hpick _ hc
      refine mem_iUnion₂.mpr ⟨_, hc, ?_⟩
      rwa [hinj _ h₅ _ hW h₆]
    · intro hy
      obtain ⟨Θ, hΘ, hyΘ⟩ := mem_iUnion₂.mp hy
      rintro ⟨x, rfl⟩
      exact x.2 (mem_iUnion₂.mpr ⟨_, (hpick Θ hΘ).1, hyΘ⟩)

end IsCutData

end GraphMinor.GM19

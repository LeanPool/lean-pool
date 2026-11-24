/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.AddHandle

/-!
# Adding a handle raises the Euler genus by two

We put together the pieces of `AddHandle.lean`: the surface `S₁` left by removing two open discs has
a model `Σ(a, b, 2)`, and the cylinder glues its two cuffs together. By the words for gluing two
cuffs in `CutLoop.lean`, the result is `Σ(a + 1, b, 0)` for an untwisted handle and `Σ(a, b + 2, 0)`
for a twisted one.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u

local notation "𝕀" => unitInterval

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']

/-- **Adding a handle, twisted or not, raises `2 a + b` by two.** -/
theorem handle_model [ConnectedSpace S] [ConnectedSpace S'] (hS : IsSurface S) (hb : bd S = ∅)
  (hS' : IsSurface S') (hb' : bd S' = ∅) {Λ₁ Λ₂ : Set S} {S₁ S₂ : Set S'}
    (hΛ₁ : IsOpenDisc Λ₁) (hΛ₂ : IsOpenDisc Λ₂) (hd : Disjoint (closure Λ₁) (closure Λ₂))
      (hu : S₁ ∪ S₂ = univ) (h1 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₁)
    (h2 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₂) (e₁ : ↥((univ : Set S) \ (Λ₁ ∪ Λ₂)) ≃ₜ S₁)
      (e₂ : ClosedCylinder ≃ₜ S₂) {a b : ℕ} (e : S ≃ₜ SurfaceModel a b 0) :
    ∃ a' b', Nonempty (S' ≃ₜ SurfaceModel a' b' 0) ∧ 2 * a' + b' = 2 * a + b + 2 := by
  have ht2 := hS.2.1
  have hcS := hS.1
  have ht2' := hS'.2.1
  obtain ⟨m⟩ := nonempty_cyl_homeo
  have hS₂ : IsSurface ↥S₂ := isSurface_of_homeo (m.trans e₂) (isSurface_model 0 0 2).1
  let e₁' : ↥(Λ₁ ∪ Λ₂)ᶜ ≃ₜ S₁ := (Homeomorph.setCongr (compl_eq_univ_sdiff _)).trans e₁
  have hXc : IsClosed (Λ₁ ∪ Λ₂)ᶜ := (hΛ₁.1.union hΛ₂.1).isClosed_compl
  have hcX : CompactSpace ↥(Λ₁ ∪ Λ₂)ᶜ := isCompact_iff_compactSpace.mp hXc.isCompact
  have hc₁ : CompactSpace ↥S₁ := e₁'.surjective.compactSpace e₁'.continuous
  have hS₁ : IsSurface ↥S₁ := piece_surface hS' hb' hc₁ hS₂ hu h1 h2
  have hX : IsSurface ↥(Λ₁ ∪ Λ₂)ᶜ := isSurface_of_homeo e₁'.symm hS₁
  have hval₂ : IsClosedEmbedding (Subtype.val : ↥S₂ → S') := (isCompact_iff_compactSpace.mpr
    hS₂.1).isClosed.isClosedEmbedding_subtypeVal
  have hval₁ : IsClosedEmbedding (Subtype.val : ↥S₁ → S') := (isCompact_iff_compactSpace.mpr
    hc₁).isClosed.isClosedEmbedding_subtypeVal
  have m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  let f₁ : Circle → S' := fun w => (e₂ (cylEnd 1 m1 w)).1
  let f₂ : Circle → S' := fun w => (e₂ (cylEnd 2 m2 w)).1
  have hf₁ : IsEmbedding f₁ := hval₂.isEmbedding.comp (e₂.isEmbedding.comp
    (isEmbedding_cylEnd 1 m1))
  have hf₂ : IsEmbedding f₂ := hval₂.isEmbedding.comp (e₂.isEmbedding.comp
    (isEmbedding_cylEnd 2 m2))
  have hbd₂ : Subtype.val '' bd ↥S₂ = range f₁ ∪ range f₂ := by
    rw [← image_bd_homeomorph e₂, bd_cylinder, image_union, image_union, ← range_comp,
      ← range_comp, ← range_comp, ← range_comp]
    rfl
  have hs : Subtype.val '' bd ↥S₁ = range f₁ ∪ range f₂ := h1.symm.trans (h2.trans hbd₂)
  have hsub₁ : range f₁ ⊆ S₁ := fun x hx => (show x ∈ S₁ ∩ S₂ by rw [h2, hbd₂]; exact .inl hx).1
  have hsub₂ : range f₂ ⊆ S₁ := fun x hx => (show x ∈ S₁ ∩ S₂ by rw [h2, hbd₂]; exact .inr hx).1
  set J₁ : Set ↥S₁ := Subtype.val ⁻¹' range f₁ with hJ₁
  set J₂ : Set ↥S₁ := Subtype.val ⁻¹' range f₂ with hJ₂
  have hvJ₁ : Subtype.val '' J₁ = range f₁ := by
    rw [hJ₁, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hsub₁
  have hvJ₂ : Subtype.val '' J₂ = range f₂ := by
    rw [hJ₂, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hsub₂
  have hOJ₁ : IsOArc J₁ := isOArc_of_image hval₁.isEmbedding (hvJ₁ ▸ ⟨hf₁.toHomeomorph⟩)
  have hOJ₂ : IsOArc J₂ := isOArc_of_image hval₁.isEmbedding (hvJ₂ ▸ ⟨hf₂.toHomeomorph⟩)
  have hJu : J₁ ∪ J₂ = bd ↥S₁ := by
    rw [hJ₁, hJ₂, ← preimage_union, ← hs, preimage_image_eq _ Subtype.val_injective]
  have hrd : Disjoint (range f₁) (range f₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, rfl⟩ ⟨w', he⟩
    have h3 := e₂.injective (Subtype.ext he)
    have h4 : (2 : ℝ) = 1 := congrArg (fun p : ClosedCylinder => p.1.1) h3
    norm_num at h4
  have hJd : Disjoint J₁ J₂ := Set.disjoint_left.mpr fun x h3 h4 => Set.disjoint_left.mp hrd h3 h4
  let P₁ : Set ↥(Λ₁ ∪ Λ₂)ᶜ := e₁'.symm '' J₁
  let P₂ : Set ↥(Λ₁ ∪ Λ₂)ᶜ := e₁'.symm '' J₂
  have hOP₁ : IsOArc P₁ := isOArc_image e₁'.symm.isEmbedding hOJ₁
  have hOP₂ : IsOArc P₂ := isOArc_image e₁'.symm.isEmbedding hOJ₂
  have hPu : P₁ ∪ P₂ = bd ↥(Λ₁ ∪ Λ₂)ᶜ := by
    rw [← image_union, hJu, image_bd_homeomorph]
  have hPd : Disjoint P₁ P₂ := (disjoint_image_iff e₁'.symm.injective).mpr hJd
  have hint : ∀ x : S, IsInteriorPoint x := fun x => by
    by_contra h
    have h3 : x ∈ bd S := h
    rw [hb] at h3
    exact h3
  have hbX : ∀ x : ↥(Λ₁ ∪ Λ₂)ᶜ, x ∈ bd ↥(Λ₁ ∪ Λ₂)ᶜ ↔ x.1 ∈ closure (Λ₁ ∪ Λ₂) := fun x => by
    have := bd_subset_iff hint x
    rwa [compl_compl] at this
  have hne : ∀ {Λ Λ' : Set S}, IsOpenDisc Λ → IsOpenDisc Λ' → Disjoint (closure Λ) (closure Λ') →
    (closure Λ \ Λ).Nonempty := by
    intro Λ Λ' h3 h4 h5
    by_contra h6
    have h7 : closure Λ ⊆ Λ := by
      intro z hz
      by_contra h8
      exact h6 ⟨z, hz, h8⟩
    have h8 : IsClosed Λ := isClosed_of_closure_subset h7
    have h9 : Λ = univ := IsClopen.eq_univ ⟨h8, h3.1⟩ (IsOpenDisc.isPathConnected h3).nonempty
    obtain ⟨z, hz⟩ := (IsOpenDisc.isPathConnected h4).nonempty
    exact Set.disjoint_left.mp h5 (h9 ▸ subset_closure (mem_univ z)) (subset_closure hz)
  obtain ⟨a₁, b₁, ⟨e₃⟩, ce⟩ : ∃ a₁ b₁, Nonempty (↥(Λ₁ ∪ Λ₂)ᶜ ≃ₜ SurfaceModel a₁ b₁ 2) ∧ 2 * a₁ + b₁
    = 2 * a + b := by
    rcases two_frontiers rfl hd (hne hΛ₁ hΛ₂ hd) (hne hΛ₂ hΛ₁ hd.symm) hbX hΛ₁.1 hΛ₂.1
      hOP₁.isPreconnected hOP₂.isPreconnected hPu with ⟨v1, v2⟩ | ⟨v1, v2⟩
    · exact handle_hole_model hS hb hΛ₁ hΛ₂ hd hX hOP₁ hOP₂ hPu hPd v1 v2 e
    · exact handle_hole_model hS hb hΛ₁ hΛ₂ hd hX hOP₂ hOP₁ ((union_comm _ _).trans hPu) hPd.symm
        v2 v1 e
  let e₄ : ↥S₁ ≃ₜ SurfaceModel a₁ b₁ 2 := e₁'.symm.trans e₃
  have hcJ₁ : J₁ ∈ cuffs ↥S₁ := cuff_of_split hOJ₁.isCompact.isClosed hOJ₂.isCompact.isClosed hJd
    hJu hOJ₁.isConnected'
  have hcJ₂ : J₂ ∈ cuffs ↥S₁ := cuff_of_split hOJ₂.isCompact.isClosed hOJ₁.isCompact.isClosed
    hJd.symm ((union_comm _ _).trans hJu) hOJ₂.isConnected'
  have hmem : ∀ p : Circle × 𝕀, (1 + (p.2 : ℝ), p.1) ∈ ClosedCylinder := fun p
    => ⟨⟨by linarith [p.2.2.1], by linarith [p.2.2.2]⟩, mem_univ _⟩
  let c : Circle × 𝕀 → S' := fun p => (e₂ ⟨(1 + (p.2 : ℝ), p.1), hmem p⟩).1
  have hcc : Continuous c := by
    refine continuous_subtype_val.comp (e₂.continuous.comp (Continuous.subtype_mk ?_ _))
    fun_prop
  have hci : Function.Injective c := by
    rintro ⟨w, t⟩ ⟨w', t'⟩ he
    have h3 := e₂.injective (Subtype.ext he)
    have h4 := Prod.ext_iff.mp (congrArg Subtype.val h3)
    have h5 : (t : ℝ) = t' := by
      have := h4.1
      simp only at this
      linarith
    exact Prod.ext h4.2 (Subtype.ext h5)
  have hc0 : ∀ w, c (w, 0) = f₁ w := fun w => by
    have : (⟨(1 + (((w, (0 : 𝕀)) : Circle × 𝕀).2 : ℝ), w), hmem (w, 0)⟩ : ClosedCylinder)
      = cylEnd 1 m1 w := Subtype.ext (Prod.ext (by simp [cylEnd]) rfl)
    simp only [c, this, f₁]
  have hc1 : ∀ w, c (w, 1) = f₂ w := fun w => by
    have : (⟨(1 + (((w, (1 : 𝕀)) : Circle × 𝕀).2 : ℝ), w), hmem (w, 1)⟩ :
        ClosedCylinder) = cylEnd 2 m2 w := by
      apply Subtype.ext
      refine Prod.ext ?_ rfl
      norm_num [cylEnd]
    simp only [c, this, f₂]
  let j₁ : Circle → ↥S₁ := fun w => ⟨f₁ w, hsub₁ ⟨w, rfl⟩⟩
  have hj₁ : IsEmbedding j₁ := IsEmbedding.of_comp (hf₁.continuous.subtype_mk _)
    continuous_subtype_val hf₁
  have hr₁ : range j₁ = J₁ := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, he⟩
      exact ⟨w, Subtype.ext he⟩
  let φ₁ : Circle ≃ₜ J₁ := hj₁.toHomeomorph.trans (Homeomorph.setCongr hr₁)
  have hφ₁ : ∀ w, (φ₁ w).1.1 = f₁ w := fun w => rfl
  have hm' : ∀ (y : ↥S₁) (p : Circle × 𝕀), y.1 = c p → ((p.2 : ℝ) = 0 ∧ y ∈ J₁) ∨ ((p.2 : ℝ) = 1
    ∧ y ∈ J₂) := by
    rintro y ⟨w, t⟩ he
    have h3 : y.1 ∈ S₁ ∩ S₂ := ⟨y.2, he ▸ (e₂ _).2⟩
    rw [h2, hbd₂] at h3
    rcases h3 with ⟨w', hw⟩ | ⟨w', hw⟩
    · left
      refine ⟨?_, ⟨w', hw⟩⟩
      have h4 : f₁ w' = c (w, t) := hw.trans he
      have h5 := e₂.injective (Subtype.ext h4)
      have h6 : (1 : ℝ) = 1 + t := congrArg (fun p : ClosedCylinder => p.1.1) h5
      simp only
      linarith
    · right
      refine ⟨?_, ⟨w', hw⟩⟩
      have h4 : f₂ w' = c (w, t) := hw.trans he
      have h5 := e₂.injective (Subtype.ext h4)
      have h6 : (2 : ℝ) = 1 + t := congrArg (fun p : ClosedCylinder => p.1.1) h5
      simp only
      linarith
  have hcov : ∀ x : S', x ∈ range (Subtype.val : ↥S₁ → S') ∨ x ∈ range c := fun x => by
    rcases (hu ▸ mem_univ x : x ∈ S₁ ∪ S₂) with h3 | h3
    · exact .inl ⟨⟨x, h3⟩, rfl⟩
    · right
      obtain ⟨⟨⟨r, w⟩, hr, hru⟩, he⟩ := e₂.surjective ⟨x, h3⟩
      have ht : r - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      refine ⟨(w, ⟨r - 1, ht⟩), ?_⟩
      have h4 : (⟨(1 + (((w, (⟨r - 1, ht⟩ : 𝕀)) : Circle × 𝕀).2 : ℝ), w), hmem
        (w, ⟨r - 1, ht⟩)⟩ : ClosedCylinder) = ⟨(r, w), hr, hru⟩ :=
        Subtype.ext (Prod.ext (by simp) rfl)
      simp only [c, h4, he]
  have h1' : Subtype.val '' J₂ = range fun w => c (w, 1) := by
    rw [hvJ₂]
    ext x
    simp only [mem_range, hc1]
  obtain ⟨ψ, hψ, b1, b2, hpre⟩ := handle_cut hS₁ continuous_subtype_val Subtype.val_injective hcc
    hci φ₁ hcJ₁ hOJ₂.isCompact.isClosed hJd (hJu ▸ subset_rfl)
    (fun w => (hφ₁ w).trans (hc0 w).symm) h1' hm' hcov
  obtain ⟨i, hi', j, hj, hij, φ, φ', g, hg, hs₁, hs₂⟩ := exists_two_holes e₄ hcJ₁ hcJ₂ (fun h => by
    obtain ⟨w, hw⟩ := hOJ₁.isConnected'.1
    exact Set.disjoint_left.mp hJd hw (show w ∈ J₂ by rw [← h]; exact hw))
  obtain ⟨hN, hLf⟩ := erase_erase_facts 2 i j
  obtain ⟨σ, g', hp⟩ := loop_two_aux hS₁ hψ hcJ₂ hOJ₁.isCompact.isClosed hOJ₂.isCompact.isClosed
    hJd hpre b1 b2 φ φ' hij hi' hj hLf hg hs₁ hs₂
  replace hp := hp.1
  have hn := nf_blkE (a := a₁) (b := b₁) (c := 2) hij hi' hj hN hLf σ
  have hlen := length_erase_erase hij hi' hj
  cases σ with
  | false =>
    obtain ⟨w, h5, h6⟩ := hn.1 rfl
    obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
    rw [hlen] at e'
    exact ⟨a₁ + 1, b₁, ⟨e'⟩, by omega⟩
  | true =>
    obtain ⟨w, h5, h6⟩ := hn.2 rfl
    obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
    rw [hlen] at e'
    exact ⟨a₁, b₁ + 2, ⟨e'⟩, by omega⟩

end GraphMinor.Surface

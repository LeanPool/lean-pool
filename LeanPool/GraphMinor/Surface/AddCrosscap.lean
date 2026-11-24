/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.HoleDisc
public import LeanPool.GraphMinor.Surface.Mobius

/-!
# Euler genus after adding a crosscap

We have a closed connected surface `S` with an open disc `Λ`, and a closed connected surface `S'`
that is the union of a copy `S₁` of `S` minus `Λ` and a Möbius band `S₂` that meet exactly along the
boundary of each. Nothing else is given: we do not know at the start that `S₁` is a surface, nor
that the closure of `Λ` is a closed disc.

We show that `S₁` is a surface (`piece_surface`), and so that the frontier of `Λ` is an `O`-arc.
Then the closure of `Λ` is a closed disc by `closure_disc`. So `S` is `S₁` with a disc pasted on,
and `S'` is `S₁` with a Möbius band pasted on. Comparing models gives `crosscap_model`: the number
`2 a + b` for the model `Σ(a, b, 0)` goes up by one.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology

universe u v

theorem isSurface_of_homeo {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
  (e : A ≃ₜ B) (h : IsSurface A) : IsSurface B := by
  have : CompactSpace A := h.1
  have : T2Space A := h.2.1
  refine ⟨e.surjective.compactSpace e.continuous, e.symm.isEmbedding.t2Space, fun x => ?_⟩
  simpa using isManifoldPoint_of_isOpenEmbedding e.isOpenEmbedding (h.2.2 (e.symm x))

theorem isOArc_image {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B] {f : A
  → B} (hf : IsEmbedding f) {X : Set A} (h : IsOArc X) : IsOArc (f '' X) := by
  obtain ⟨φ⟩ := h
  exact ⟨φ.trans (hf.homeomorphImage X)⟩

theorem isOArc_of_image {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B] {f : A
  → B} (hf : IsEmbedding f) {X : Set A} (h : IsOArc (f '' X)) : IsOArc X := by
  obtain ⟨φ⟩ := h
  exact ⟨φ.trans (hf.homeomorphImage X).symm⟩

variable {S : Type u} [TopologicalSpace S]

/-- A closed set is connected if its complement is covered by finitely many disjoint closed sets,
each of which meets the set in a nonempty connected set. -/
theorem connected_compl [ConnectedSpace S] {X : Set S} (hX : IsClosed X)
  (hne : X.Nonempty) {𝓖 : Set (Set S)} (hf : 𝓖.Finite) (hc : ∀ G ∈ 𝓖, IsClosed G)
    (hp : ∀ G ∈ 𝓖, IsPreconnected (G ∩ X)) (hn : ∀ G ∈ 𝓖, (G ∩ X).Nonempty)
      (hd : ∀ G ∈ 𝓖, ∀ G' ∈ 𝓖, G ≠ G' → Disjoint G G') (hu : X ∪ ⋃₀ 𝓖 = univ) :
    ConnectedSpace ↥X := by
  have : Nonempty ↥X := hne.to_subtype
  have hP : PreconnectedSpace ↥X := by
    refine preconnectedSpace_iff_clopen.mpr fun A hA => ?_
    have hcl := hX.isClosedEmbedding_subtypeVal.isClosedMap
    set A' : Set S := Subtype.val '' A with hA'
    set B' : Set S := Subtype.val '' Aᶜ with hB'
    have hAc : IsClosed A' := hcl _ hA.1
    have hBc : IsClosed B' := hcl _ hA.2.isClosed_compl
    have hAB : ∀ x, x ∈ A' → x ∈ B' → False := by
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
      exact hy (Subtype.ext he ▸ hx)
    have hcov : X ⊆ A' ∪ B' := fun x hx => by
      by_cases h : (⟨x, hx⟩ : ↥X) ∈ A
      · exact .inl ⟨_, h, rfl⟩
      · exact .inr ⟨_, h, rfl⟩
    have hAX : A' ⊆ X := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hBX : B' ⊆ X := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hone : ∀ G ∈ 𝓖, (G ∩ A').Nonempty → (G ∩ B').Nonempty → False := by
      rintro G hG ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩
      obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.mp (hp G hG) A' B' hAc hBc
        (inter_subset_right.trans hcov) ⟨x, ⟨hx1, hAX hx2⟩, hx2⟩ ⟨y, ⟨hy1, hBX hy2⟩, hy2⟩
      exact hAB z hz1 hz2
    set P : Set S := A' ∪ ⋃₀ {G ∈ 𝓖 | (G ∩ A').Nonempty} with hPd
    set P' : Set S := B' ∪ ⋃₀ {G ∈ 𝓖 | (G ∩ B').Nonempty} with hP'd
    have c1 : IsClosed P := hAc.union ((hf.subset (sep_subset _ _)).isClosed_sUnion fun G hG
      => hc G hG.1)
    have c2 : IsClosed P' := hBc.union ((hf.subset (sep_subset _ _)).isClosed_sUnion fun G hG
      => hc G hG.1)
    have hall : ∀ x, x ∈ P ∨ x ∈ P' := fun x => by
      rcases (hu ▸ mem_univ x : x ∈ X ∪ ⋃₀ 𝓖) with h | ⟨G, hG, hx⟩
      · rcases hcov h with h | h
        · exact .inl (.inl h)
        · exact .inr (.inl h)
      · obtain ⟨y, hy1, hy2⟩ := hn G hG
        rcases hcov hy2 with h | h
        · exact .inl (.inr ⟨G, ⟨hG, y, hy1, h⟩, hx⟩)
        · exact .inr (.inr ⟨G, ⟨hG, y, hy1, h⟩, hx⟩)
    have hdisj : ∀ x, x ∈ P → x ∈ P' → False := by
      rintro x (h1 | ⟨G, ⟨hG, h1⟩, hx⟩) (h2 | ⟨G', ⟨hG', h2⟩, hx'⟩)
      · exact hAB x h1 h2
      · exact hone G' hG' ⟨x, hx', h1⟩ h2
      · exact hone G hG h1 ⟨x, hx, h2⟩
      · by_cases he : G = G'
        · subst he
          exact hone G hG h1 h2
        · exact Set.disjoint_left.mp (hd G hG G' hG' he) hx hx'
    have hcon := isPreconnected_closed_iff.mp (isPreconnected_univ (α := S)) P P' c1 c2 (fun x _
      => hall x)
    by_cases h1 : A.Nonempty
    · right
      by_contra h2
      obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem _).mp h2
      obtain ⟨w, hw⟩ := h1
      obtain ⟨y, -, hy1, hy2⟩ := hcon ⟨w.1, mem_univ _, .inl ⟨w, hw, rfl⟩⟩ ⟨z.1, mem_univ _, .inl
        ⟨z, hz, rfl⟩⟩
      exact hdisj y hy1 hy2
    · exact .inl (not_nonempty_iff_eq_empty.mp h1)
  exact ⟨‹Nonempty ↥X›⟩

variable {S' : Type u} [TopologicalSpace S']

/-- The piece `S₁`, which is glued to the surface `S₂` along the boundaries of both, is a surface.
-/
theorem piece_surface [ConnectedSpace S'] (hS' : IsSurface S') (hb : bd S' = ∅) {S₁ S₂ : Set S'}
  (hc : CompactSpace ↥S₁) (hS₂ : IsSurface ↥S₂) (hu : S₁ ∪ S₂ = univ)
    (_h1 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₁) (h2 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₂) : IsSurface ↥S₁
      := by
  classical
  have ht2 := hS'.2.1
  have hc₂ : CompactSpace ↥S₂ := hS₂.1
  have hint : ∀ x : S', IsInteriorPoint x := fun x => by
    by_contra h
    have h3 : x ∈ bd S' := h
    rw [hb] at h3
    exact h3
  have hT : IsClosed S₁ := (isCompact_iff_compactSpace.mpr hc).isClosed
  have hZ : IsClosed S₂ := (isCompact_iff_compactSpace.mpr hc₂).isClosed
  have hval := hZ.isClosedEmbedding_subtypeVal
  refine ⟨hc, inferInstance, fun x => ?_⟩
  by_cases hx : x.1 ∈ S₂
  · have hk : x.1 ∈ Subtype.val '' bd ↥S₂ := h2 ▸ ⟨x.2, hx⟩
    obtain ⟨k, hk, hke⟩ := hk
    obtain ⟨hcl, hfin, hO⟩ := cuff_statement.{u} ↥S₂ hS₂
    set K : Set ↥S₂ := connectedComponentIn (bd ↥S₂) k with hKd
    have hKc : K ∈ cuffs ↥S₂ := ⟨k, hk, rfl⟩
    have hKb : K ⊆ bd ↥S₂ := connectedComponentIn_subset _ _
    have hD : IsClosed (bd ↥S₂ \ K) := by
      have e : bd ↥S₂ \ K = ⋃₀ (cuffs ↥S₂ \ {K}) := by
        ext y
        constructor
        · rintro ⟨hy, hyK⟩
          refine ⟨connectedComponentIn (bd ↥S₂) y, ⟨⟨y, hy, rfl⟩, fun h => hyK ?_⟩,
            mem_connectedComponentIn hy⟩
          rw [mem_singleton_iff] at h
          rw [← h]
          exact mem_connectedComponentIn hy
        · rintro ⟨C, ⟨hC, hne⟩, hy⟩
          obtain ⟨z, hz, rfl⟩ := id hC
          exact ⟨connectedComponentIn_subset _ _ hy, fun h => Set.disjoint_left.mp
            (cuffs_disjoint hC hKc hne) hy h⟩
      rw [e]
      exact (hfin.subset sdiff_subset).isClosed_sUnion fun C hC => (hO C hC.1).isCompact.isClosed
    have hmem : ∀ y ∈ Subtype.val '' K, y ∈ S₁ := fun y hy => by
      have h3 : y ∈ S₁ ∩ S₂ := h2 ▸ image_mono hKb hy
      exact h3.1
    have hclosure : ∀ y ∈ Subtype.val '' bd ↥S₂, y ∈ closure (S₁ \ S₂) ∧ y ∈ closure (S₂ \ S₁) := by
      rintro _ ⟨z, hz, rfl⟩
      constructor
      · have h3 := (bd_subset_iff hint z).mp hz
        have h4 : S₂ᶜ ⊆ S₁ \ S₂ := fun w hw => ⟨(hu ▸ mem_univ w : w ∈ S₁ ∪ S₂).resolve_right hw,
          hw⟩
        exact closure_mono h4 h3
      · have h3 := mem_closure_compl_bd (hS₂.2.2 z)
        have h4 := image_closure_subset_closure_image continuous_subtype_val ⟨z, h3, rfl⟩
        refine closure_mono ?_ h4
        rintro _ ⟨w, hw, rfl⟩
        refine ⟨w.2, fun h5 => hw ?_⟩
        have h6 : w.1 ∈ Subtype.val '' bd ↥S₂ := h2 ▸ ⟨h5, w.2⟩
        obtain ⟨v, hv, he⟩ := h6
        exact Subtype.ext he ▸ hv
    have hside := side_manifold hS' (T := S₁) (Z := S₂) (C := Subtype.val '' K) (D
      := Subtype.val '' (bd ↥S₂ \ K)) hT hZ hu
      (isOArc_image hval.isEmbedding (hO K hKc)) (by rw [hb]; exact disjoint_empty _) hmem
        (hval.isClosedMap _ hD)
      (by rw [h2, ← image_union, union_sdiff_cancel hKb])
      (Set.disjoint_left.mpr fun y ⟨p, hp, hpe⟩ ⟨q, hq, hqe⟩ => hq.2 (by
        rw [← Subtype.ext (hpe.trans hqe.symm)]
        exact hp))
      (fun y hy => (hclosure y (image_mono hKb hy)).1) (fun y hy => (hclosure y
        (image_mono hKb hy)).2)
      (x := x.1) ⟨k, mem_connectedComponentIn hk, hke⟩
    exact hside.1
  · have hsub : S₂ᶜ ⊆ S₁ := fun w hw => (hu ▸ mem_univ w : w ∈ S₁ ∪ S₂).resolve_right hw
    have hop : IsOpen S₂ᶜ := hZ.isOpen_compl
    exact isManifoldPoint_of_isOpenEmbedding (isOpenEmbedding_inclusion hsub hop) (x := ⟨x.1,
      hx⟩) (isManifoldPoint_sub hop (hS'.2.2 x.1))

theorem isOArc_bd_one {Z : Type u} [TopologicalSpace Z] {a b : ℕ} (e : SurfaceModel a b 1 ≃ₜ Z) :
  IsOArc (bd Z) := by
  obtain ⟨C, hC, hb⟩ := model_one_cuff a b
  have h1 := (cuff_statement.{0} _ (isSurface_model a b 1).1).2.2 C hC
  rw [← image_bd_homeomorph e, hb]
  exact isOArc_image e.isEmbedding h1

theorem IsOArc.isConnected' {Y : Type u} [TopologicalSpace Y] {C : Set Y}
  (h : IsOArc C) : IsConnected C := by
  obtain ⟨φ⟩ := id h
  exact ⟨⟨_, (φ 1).2⟩, h.isPreconnected⟩

theorem isCuff_of_oArc {Y : Type u} [TopologicalSpace Y] (h : IsOArc (bd Y)) : IsCuff (bd Y) := by
  have h1 : bd Y ∈ cuffs Y := by
    rw [cuffs_eq_of_isConnected h.isConnected']
    exact mem_singleton _
  exact h1

/-- **Adding a crosscap raises `2 a + b` by one.** -/
theorem crosscap_model [ConnectedSpace S] [ConnectedSpace S'] (hS : IsSurface S) (hb : bd S = ∅)
  (hS' : IsSurface S') (hb' : bd S' = ∅) {Λ : Set S} {S₁ S₂ : Set S'}
    (hΛ : IsOpenDisc Λ) (hu : S₁ ∪ S₂ = univ) (h1 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₁) (h2 : S₁ ∩ S₂
      = Subtype.val '' bd ↥S₂)
    (e₁ : ↥((univ : Set S) \ Λ) ≃ₜ S₁) (e₂ : MobiusBand ≃ₜ S₂) {a b : ℕ}
      (e : S ≃ₜ SurfaceModel a b 0) :
    ∃ a' b', Nonempty (S' ≃ₜ SurfaceModel a' b' 0) ∧ 2 * a' + b' = 2 * a + b + 1 := by
  have ht2 := hS.2.1
  have hcS := hS.1
  have ht2' := hS'.2.1
  obtain ⟨m⟩ := nonempty_mob_homeo
  let e₂' : SurfaceModel 0 1 1 ≃ₜ S₂ := m.trans e₂
  have hS₂ : IsSurface ↥S₂ := isSurface_of_homeo e₂' (isSurface_model 0 1 1).1
  let e₁' : ↥Λᶜ ≃ₜ S₁ := (Homeomorph.setCongr (compl_eq_univ_sdiff Λ)).trans e₁
  have hXc : IsClosed Λᶜ := hΛ.1.isClosed_compl
  have hcX : CompactSpace ↥Λᶜ := isCompact_iff_compactSpace.mp hXc.isCompact
  have hc₁ : CompactSpace ↥S₁ := e₁'.surjective.compactSpace e₁'.continuous
  have hS₁ : IsSurface ↥S₁ := piece_surface hS' hb' hc₁ hS₂ hu h1 h2
  have hX : IsSurface ↥Λᶜ := isSurface_of_homeo e₁'.symm hS₁
  have hint : ∀ x : S, IsInteriorPoint x := fun x => by
    by_contra h
    have h3 : x ∈ bd S := h
    rw [hb] at h3
    exact h3
  have hbX : ∀ x : ↥Λᶜ, x ∈ bd ↥Λᶜ ↔ x.1 ∈ closure Λ := fun x => by
    have := bd_subset_iff hint x
    rwa [compl_compl] at this
  have himg : Subtype.val '' bd ↥Λᶜ = closure Λ \ Λ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hbX y).mp hy, y.2⟩
    · rintro ⟨h3, h4⟩
      exact ⟨⟨x, h4⟩, (hbX _).mpr h3, rfl⟩
  have hval := hXc.isClosedEmbedding_subtypeVal
  have hval₂ : IsClosedEmbedding (Subtype.val : ↥S₂ → S') := (isCompact_iff_compactSpace.mpr
    hS₂.1).isClosed.isClosedEmbedding_subtypeVal
  have hval₁ : IsClosedEmbedding (Subtype.val : ↥S₁ → S') := (isCompact_iff_compactSpace.mpr
    hc₁).isClosed.isClosedEmbedding_subtypeVal
  have hOb₂ : IsOArc (bd ↥S₂) := isOArc_bd_one e₂'
  have hOF : IsOArc (Subtype.val '' bd ↥S₁) := by
    rw [← h1, h2]
    exact isOArc_image hval₂.isEmbedding hOb₂
  have hOb₁ : IsOArc (bd ↥S₁) := isOArc_of_image hval₁.isEmbedding hOF
  have hObX : IsOArc (bd ↥Λᶜ) := by
    rw [← image_bd_homeomorph e₁'.symm]
    exact isOArc_image e₁'.symm.isEmbedding hOb₁
  have hF : IsOArc (closure Λ \ Λ) := himg ▸ isOArc_image hval.isEmbedding hObX
  have hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ := by
    rw [← himg]
    rintro _ ⟨k, -, rfl⟩
    have h3 := mem_closure_compl_bd (hX.2.2 k)
    have h4 := image_closure_subset_closure_image continuous_subtype_val ⟨k, h3, rfl⟩
    refine closure_mono ?_ h4
    rintro _ ⟨w, hw, rfl⟩
    exact fun h5 => hw ((hbX w).mpr h5)
  obtain ⟨hG, hGb⟩ := closure_disc hS hΛ (by rw [hb]; exact disjoint_empty _) hF hout
  obtain ⟨φ⟩ := id hF
  have hcov : Λᶜ ∪ closure Λ = univ := by
    rw [eq_univ_iff_forall]
    intro z
    by_cases hz : z ∈ Λ
    · exact .inr (subset_closure hz)
    · exact .inl hz
  have hconn : ConnectedSpace ↥Λᶜ := connected_compl hXc ⟨_, (φ 1).2.2⟩ (finite_singleton
    (closure Λ)) (fun G hG => by
      rw [mem_singleton_iff.mp hG]
      exact isClosed_closure) (fun G hG => by
      rw [mem_singleton_iff.mp hG]
      exact hF.isPreconnected) (fun G hG => by
      rw [mem_singleton_iff.mp hG]
      exact ⟨_, (φ 1).2⟩) (fun G hG G' hG' hne => absurd ((mem_singleton_iff.mp hG).trans
        (mem_singleton_iff.mp hG').symm) hne) (by
      rw [sUnion_singleton]
      exact hcov)
  obtain ⟨a₁, b₁, c₁, ⟨e₃⟩⟩ := classification.{u} _ hX hconn
  have hran : range (Subtype.val : ↥Λᶜ → S) ∪ closure Λ = univ := by
    rw [Subtype.range_coe]
    exact hcov
  have hmeet : range (Subtype.val : ↥Λᶜ → S) ∩ closure Λ = Subtype.val '' bd ↥Λᶜ := by
    rw [Subtype.range_coe, himg, inter_comm]
    rfl
  obtain ⟨h0, ⟨e₄⟩⟩ := paste_model hX (isCuff_of_oArc hObX) hS hval hG hran hmeet
    (hGb.trans himg.symm) e₃
  obtain ⟨c0, ce, -⟩ := (modelCriterion.2 a₁ b₁ (c₁ - 1) a b 0).mp ⟨e₄.symm.trans e⟩
  obtain rfl : c₁ = 1 := by omega
  have hran₁ : range (Subtype.val : ↥S₁ → S') ∪ S₂ = univ := by
    rw [Subtype.range_coe]
    exact hu
  have hm₁ : range (Subtype.val : ↥S₁ → S') ∩ S₂ = Subtype.val '' bd ↥S₁ := by
    rw [Subtype.range_coe]
    exact h1
  have hBb : Subtype.val ⁻¹' (Subtype.val '' bd ↥S₁) ⊆ bd ↥S₂ := fun z hz => by
    have h3 : z.1 ∈ Subtype.val '' bd ↥S₂ := by
      rw [← h2, h1]
      exact hz
    obtain ⟨k, hk, he⟩ := h3
    exact Subtype.ext he ▸ hk
  obtain ⟨-, -, ⟨e₅⟩⟩ := glue_model hS₁ (isCuff_of_oArc hOb₁) hS₂ ht2' hval₁ hran₁ hm₁ hOF hBb
    (e₁'.symm.trans e₃) e₂'.symm
  exact ⟨0 + a₁, 1 + b₁, ⟨e₅⟩, by omega⟩

end GraphMinor.Surface

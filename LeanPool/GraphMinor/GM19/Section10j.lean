/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10i

import LeanPool.GraphMinor.GM19.FragmentOrient

/-!
# Graph Minors XIX, (10.4), from the data of a distance flaw
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


/-- The sides of the discs of a set of discs. -/
def discPairs (cap : IsCappedSurface S Shat) (𝓓 : Set (Set Shat)) : Set (Set S × Set S) :=
  (fun Δ ↦ (cap.emb ⁻¹' Δ, cap.emb ⁻¹' closure Δᶜ)) '' 𝓓

omit [T2Space S] [T2Space Shat] in
theorem iInter_discPairs (𝓓 : Set (Set Shat)) :
    ⋂ p ∈ discPairs cap 𝓓, Prod.snd p = ⋂ Δ ∈ 𝓓, cap.emb ⁻¹' closure Δᶜ := by
  ext x
  simp [discPairs]

/-- What the proof of (10.4) needs of a distance flaw: the discs `ins(C)`, the feature `K` that is
the part of `F` in `Σ`, and how
the two fit together. -/
structure IsOuterData (D : TangleDatum cap χ) (n : ℕ) (𝓓 : Set (Set Shat))
  (K : Drawing S) : Prop where
  shape : IsOuterShape cap K 𝓓
  finite : 𝓓.Finite
  card : 𝓓.ncard ≤ 2
  family : IsLinkedFamily D (n + 1) (discPairs cap 𝓓)
  feature : IsFeature χ.Φ K
  inter : D.P.Γ.U ∩ K.U ⊆ D.P.Γ.V ∩ K.V
  lines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
    ∧ IsLineWithEnds (closure e) u v
  size : K.V.ncard + K.E.ncard ≤ 8 * n
  pieces : ∃ 𝓞 𝓛 : Set (Set S), 𝓞.Finite ∧ 𝓛.Finite ∧ (∀ C ∈ 𝓞, IsOArc C) ∧
    (∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ bd S ∪ ⋃₀ 𝓞 ∧ t ∈ bd S ∪ ⋃₀ 𝓞) ∧ K.U
      = ⋃₀ 𝓞 ∪ ⋃₀ 𝓛
  roots : ∀ Δ ∈ 𝓓, ∀ v ∈ D.P.Γ.V, cap.emb v ∈ Δ → cap.emb v ∈ closure Δᶜ → v ∈ K.U
  outer : ∀ v ∈ K.U, ∀ Δ ∈ 𝓓, cap.emb v ∈ closure Δᶜ
  anchored : IsAnchored D.P.Γ K

omit [T2Space S] in
theorem IsAnchored.image {f : S ≃ₜ S} {Γ Γ' : Painting S} {K K' : Drawing S} (h : IsAnchored Γ K)
  (hU : f '' K'.U = K.U)
    (hV : Γ.V = f '' Γ'.V) : IsAnchored Γ' K' := by
  intro u x hx hne
  obtain ⟨C, hC, hxC, hp, z, hz, hzV⟩ := h (f u) (f x) (hU ▸ mem_image_of_mem _ hx) fun h' ↦ hne
    (f.injective h')
  refine ⟨f.symm '' C, ?_, ⟨_, hxC, by simp⟩, hp.image _ f.symm.continuous.continuousOn,
    f.symm z, mem_image_of_mem _ hz, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyK, hyu⟩ := hC hy
    rw [← hU] at hyK
    obtain ⟨w, hw, rfl⟩ := hyK
    rw [f.symm_apply_apply]
    exact ⟨hw, fun h' ↦ hyu (by rw [mem_singleton_iff.1 h']; rfl)⟩
  · rw [hV] at hzV
    obtain ⟨w, hw, rfl⟩ := hzV
    rwa [f.symm_apply_apply]

omit [T2Space S] in
/-- Pulling back a feature preserves the intersection and anchoring conditions for placement and
gives a list of the common vertices. -/
theorem IsColouredImage.exists_feature_placement_data {f : S ≃ₜ S} {P Q : ColouredPainting χ}
    {Kc K : Drawing S} (hQ : IsColouredImage f.symm P Q)
    (hU : f '' Kc.U = K.U) (hV : f '' Kc.V = K.V)
    (hinter : P.Γ.U ∩ K.U ⊆ P.Γ.V ∩ K.V) (hanc : IsAnchored P.Γ K) :
    ∃ l : List S, Q.Γ.U ∩ Kc.U ⊆ Q.Γ.V ∩ Kc.V ∧ IsAnchored Q.Γ Kc ∧
      ∀ v, v ∈ l ↔ v ∈ Kc.V ∩ Q.Γ.V := by
  classical
  have hfin : (Kc.V ∩ f ⁻¹' P.Γ.V).Finite := Kc.finite_V.subset inter_subset_left
  refine ⟨hfin.toFinset.toList, hQ.feature_inter_subset hU hV hinter,
    hanc.image hU hQ.symm.V, fun v => ?_⟩
  rw [Finset.mem_toList, hfin.mem_toFinset, hQ.V]
  refine ⟨fun h => ⟨h.1, _, h.2, f.symm_apply_apply v⟩, ?_⟩
  rintro ⟨h₁, u, hu, rfl⟩
  exact ⟨h₁, by simpa using hu⟩

omit [T2Space S] [T2Space Shat] in
/-- The shape moves to the cap twisted by a homeomorphism. -/
theorem IsOuterShape.ofHomeo {K K' : Drawing S} {𝓓 : Set (Set Shat)}
  (h : IsOuterShape cap K' 𝓓) (f : S ≃ₜ S)
    (hU : f '' K.U = K'.U) : IsOuterShape (cap.ofHomeo f) K 𝓓 := by
  have hsym : ∀ A : Set S, f '' (f.symm '' A) = A := fun A ↦ by
    rw [image_image]
    simp
  have hran : range (cap.ofHomeo f).emb = range cap.emb := by
    rw [← image_univ, cap.ofHomeo_emb_image, image_univ, f.range_coe, image_univ]
  have hbd : (cap.ofHomeo f).emb '' bd S = cap.emb '' bd S := by
    rw [cap.ofHomeo_emb_image, image_bd]
  have hne : ∀ {Θ Θ' : Set S}, Θ ≠ Θ' → f.symm '' Θ ≠ f.symm '' Θ' := fun h₁ h₂ ↦ h₁
    (f.symm.injective.image_injective h₂)
  have hline : ∀ {L : Set S} {a b : S}, IsLineWithEnds L a b → IsLineWithEnds (f.symm '' L)
    (f.symm a) (f.symm b) := fun {L a b} hl ↦ by
    refine isLine_comap f.isClosedEmbedding ?_
    rw [hsym, f.apply_symm_apply, f.apply_symm_apply]
    exact hl
  have hL : ∀ L : Set S, (cap.ofHomeo f).emb '' (f.symm '' L) = cap.emb '' L := fun L ↦ by
    rw [cap.ofHomeo_emb_image, hsym]
  have hpt : ∀ a : S, (cap.ofHomeo f).emb (f.symm a) = cap.emb a := fun a ↦ by
    change cap.emb (f (f.symm a)) = _
    rw [f.apply_symm_apply]
  have hKU : (cap.ofHomeo f).emb '' K.U = cap.emb '' K'.U := by
    rw [cap.ofHomeo_emb_image, hU]
  have hbdL : ∀ {L : Set S} {s : S}, L ∩ bd S ⊆ {s} → f.symm '' L ∩ bd S ⊆ {f.symm s}
    := fun {L s} h ↦ by
    rintro x ⟨⟨y, hy, rfl⟩, hb⟩
    have hb' : y ∈ bd S := by
      have := mem_image_of_mem f hb
      rw [image_bd] at this
      rwa [f.apply_symm_apply] at this
    rw [mem_singleton_iff.1 (h ⟨hy, hb'⟩)]
    rfl
  rcases h with ⟨Δ, rfl, hΔ, hform, Θ₁, h₁, Θ₂, h₂, hn, hm₁, hm₂⟩ | ⟨Δ, L, s, u, Θ, Θ', rfl, hΔ,
    hr, h₁, h₂, hn, hs, hL₀, hK, hm, hb, hb', hd, hm'⟩ |
    ⟨Δ₁, Δ₂, L, a, b, Θ₁, Θ₂, rfl, hne₀, hΔ₁, hΔ₂, hr₁, hr₂, hL₀, hK, hm₁, hm₂, hd₁, hd₂, hin, h₁,
      h₂, hn, hc₁, hc₂⟩
  · refine Or.inl ⟨Δ, rfl, hΔ, hform.ofHomeo f hU, _, (cap.ofHomeo_cuffDisc_symm f h₁).1,
      _, (cap.ofHomeo_cuffDisc_symm f h₂).1, hne hn, ?_, ?_⟩
    · rwa [(cap.ofHomeo_cuffDisc_symm f h₁).2]
    · rwa [(cap.ofHomeo_cuffDisc_symm f h₂).2]
  · refine Or.inr (Or.inl ⟨Δ, f.symm '' L, f.symm s, f.symm u, _, _, rfl, hΔ, hran ▸ hr,
      (cap.ofHomeo_cuffDisc_symm f h₁).1, (cap.ofHomeo_cuffDisc_symm f h₂).1, hne hn,
      mem_image_of_mem _ hs, ?_, ?_, ?_, hbdL hb, ?_, ?_, ?_⟩)
    · rcases hL₀ with ⟨rfl, rfl⟩ | hl
      · exact Or.inl ⟨image_singleton, rfl⟩
      · exact Or.inr (hline hl)
    · rw [hKU, hL]
      exact hK
    · rw [hL, hpt]
      exact hm
    · rw [hbd, hpt]
      exact hb'
    · rw [(cap.ofHomeo_cuffDisc_symm f h₁).2]
      exact hd
    · rw [(cap.ofHomeo_cuffDisc_symm f h₂).2]
      exact hm'
  · refine Or.inr (Or.inr ⟨Δ₁, Δ₂, f.symm '' L, f.symm a, f.symm b, _, _, rfl, hne₀, hΔ₁, hΔ₂,
      hran ▸ hr₁, hran ▸ hr₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (cap.ofHomeo_cuffDisc_symm f h₁).1, (cap.ofHomeo_cuffDisc_symm f h₂).1, hne hn, ?_, ?_⟩)
    · rcases hL₀ with ⟨rfl, rfl⟩ | hl
      · exact Or.inl ⟨image_singleton, rfl⟩
      · exact Or.inr (hline hl)
    · rw [hKU, hL]
      exact hK
    · rw [hL, hpt]
      exact hm₁
    · rw [hL, hpt]
      exact hm₂
    · rw [hbd, hL]
      exact hd₁
    · rw [hbd]
      exact hd₂
    · rw [hpt]
      exact hin
    · rw [(cap.ofHomeo_cuffDisc_symm f h₁).2]
      exact hc₁
    · rw [(cap.ofHomeo_cuffDisc_symm f h₂).2]
      exact hc₂

/-- One well-behaved set for all distance flaws with a given feature. -/
theorem exists_class_outer (hS : IsSurface S) (hd : χ.IsDisjoint)
    {𝒮 : Set (ColouredPainting χ)} (hcl : IsPaintingClass χ 𝒮) (n : ℕ) (a₀ : β)
      (hS3 : ConditionS3 χ cap) {Kc : Drawing S}
    (hg : ∃ (D : TangleDatum cap χ) (𝓓 : Set (Set Shat)), IsOuterData D n 𝓓 Kc) :
    ∃ B : Set (Place χ), IsWellBehavedPlaces B ∧ ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 → n + 1 ≤ D.ord →
      ∀ (𝓓 : Set (Set Shat)) (K : Drawing S) (α : S ≃ₜ S), IsOuterData D n 𝓓 K
        → IsFramePreservingHomeo χ.Φ α →
      α '' Kc.U = K.U → α '' Kc.V = K.V →
      ∃ L : RootedLocation D.P.Γ, L.Isolates D.tb (n + 1) D.ord D.𝒯 ∧ (⟨hd, D.P, L⟩ : Place χ) ∈ B
        := by
  classical
  have : ConnectedSpace S := χ.connected
  obtain ⟨D₀, 𝓓₀, hp⟩ := hg
  have hKne : Kc.V ⊆ ⋃ e ∈ arcComponentsIn (Kc.U \ Kc.V), closure e := fun v hv ↦ by
    obtain ⟨e, he, hve⟩ := hp.feature.no_isolated_vertices v hv
    exact mem_biUnion he hve.1
  obtain ⟨𝓞, 𝓛, h𝓞, h𝓛, hO, hL, hU⟩ := hp.pieces
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hsheet, -⟩ := exists_pullData_of_shape hS D₀.P.fits hp.inter
    hp.lines hKne h𝓞 h𝓛 hO hL hU
  obtain ⟨B, hB, hmem⟩ := exists_class_cut (χ := χ) (K := Kc) hY (ψ := ψ) 2
    (fun c ↦ (∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface c Shat₁ → Nonempty
      (Shat₁ ≃ₜ Shat)) ∧
      numCuffs c < numCuffs S ∧ (IsOrientableSurface c → IsOrientableSurface S)) (fun X ↦ X.P ∈ 𝒮)
    (fun y l h ↦ wellBehaved_S3 hS hp.feature hcl hp.lines hY hψ hsheet y l 2 a₀ hS3 h.1 h.2.1
      h.2.2)
  refine ⟨_, theorem_9_4_proof hB, ?_⟩
  rintro D hmem𝒮 hord 𝓓 K α hK hα hαU hαV
  obtain ⟨y, hy, hhat, hc, hO'⟩ := GraphMinor.GM19.outerSide S Shat (cap.ofHomeo α) Kc 𝓓 hS
    (hK.shape.ofHomeo α hαU) Y tY t2Y ψ hY hψ
  let Q : ColouredPainting χ := D.P.image α.symm hα.symm
  have hQ : IsColouredImage α.symm D.P Q := ColouredPainting.isImage_image _ _ _
  have I : IsColouredImage α Q D.P := hQ.symm
  have hrange : range (fun x : connectedComponent y ↦ ψ x.1) = α ⁻¹' ⋂ p ∈ discPairs cap 𝓓,
    Prod.snd p := by
    have : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
      ext z
      simp
    rw [this, hy, iInter_discPairs]
    ext x
    simp [IsCappedSurface.ofHomeo]
  obtain ⟨_, hinter, hanc, hl⟩ := hQ.exists_feature_placement_data hαU hαV hK.inter hK.anchored
  have hr : ∀ v, v ∈ Kc.U → v ∈ range (fun x : connectedComponent y ↦ ψ x.1) := fun v hv ↦ by
    rw [hrange]
    have hvK : α v ∈ K.U := hαU ▸ mem_image_of_mem _ hv
    rw [mem_preimage, iInter_discPairs]
    exact mem_iInter₂.2 fun Δ hΔ ↦ hK.outer _ hvK Δ hΔ
  have hπ : ∀ p ∈ discPairs cap 𝓓, ∀ v ∈ D.P.Γ.V, v ∈ p.1 → v ∈ p.2 → α.symm v ∈ Kc.U := by
    rintro _ ⟨Δ, hΔ, rfl⟩ v hv h₁ h₂
    have := hK.roots Δ hΔ v hv h₁ h₂
    rw [← hαU] at this
    obtain ⟨z, hz, rfl⟩ := this
    rwa [α.symm_apply_apply]
  have hm : (discPairs cap 𝓓).ncard ≤ 2 := le_trans (ncard_image_le hK.finite) hK.card
  obtain ⟨X, hXP, hX, hXim⟩ := hK.family.exists_place (K := Kc) hd hα I hrange hinter hanc hl hr hπ
    hm
  have hX𝒮 : X.P ∈ 𝒮 := hXP ▸ hcl.image_mem _ hmem𝒮 _ _ hα.symm hQ
  refine ⟨hK.family.location, hK.family.isolates hS (by omega) hord, X, hmem y _ X ⟨hhat, hc,
    ?_⟩ ?_ hX hX𝒮, α, hXim⟩
  · exact hO'
  · exact fun v hv ↦ ((hl v).1 hv).1

end GraphMinor.GM19

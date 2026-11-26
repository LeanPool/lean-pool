/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.UniverseLift1
public import LeanPool.GraphMinor.GM12.Section3HomeoWalks

/-!
# Universe-polymorphic transport of capped surfaces, radial drawings, and colour schemes

This file transports capped surfaces, radial drawings, `Painting.rep`, colour schemes, coloured
paintings, surface orientations, refinements, and conditions `S₁`–`S₄` across homeomorphisms
between surfaces in arbitrary universes `Type u₁` and `Type u₂`. Using `Surface.classification.{u}`,
this lifts `Theorem62Statement.{0}` to `Theorem62Statement.{u}`, `Theorem55Statement.{0, w}` to
`Theorem55Statement.{u, w}`, and `Theorem41Statement.{0, w}` to `Theorem41Statement.{u, w}`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM12

universe u u₁ u₂ w

/-! ### Capped surfaces and radial drawings under homeomorphisms -/

section CappedAndRadial

variable {S : Type u₁} {Shat : Type u₁} {S' : Type u₂} {Shat' : Type u₂}
  [TopologicalSpace S] [TopologicalSpace Shat] [TopologicalSpace S'] [TopologicalSpace Shat']
  (eS : S ≃ₜ S') (eShat : Shat ≃ₜ Shat')

theorem image_subBd_u {X : Type u₁} {Y : Type u₂} [TopologicalSpace X] [TopologicalSpace Y]
    (ψ : X ≃ₜ Y) (Δ : Set X) : subBd (ψ '' Δ) = ψ '' subBd Δ := by
  have h1 : univ \ ψ '' Δ = ψ '' (univ \ Δ) := by
    rw [image_sdiff ψ.injective, image_univ_of_surjective ψ.surjective]
  rw [subBd, subBd, h1, image_inter ψ.injective, ψ.image_closure, ψ.image_closure]

/-- Transport an `IsCappedSurface` along homeomorphisms `eS : S ≃ₜ S'` and `eShat : Shat ≃ₜ Shat'`.
-/
noncomputable def IsCappedSurface.mapHomeo (cap : IsCappedSurface S Shat) :
    IsCappedSurface S' Shat' where
  isSurface := isSurface_of_homeo eShat cap.isSurface
  connected := by
    have := cap.connected
    exact eShat.surjective.connectedSpace eShat.continuous
  bd_empty := by
    rw [← image_bd eShat, cap.bd_empty, image_empty]
  emb := eShat ∘ cap.emb ∘ eS.symm
  isEmbedding := eShat.isEmbedding.comp (cap.isEmbedding.comp eS.symm.isEmbedding)
  cuffDisc Θ' := eShat '' cap.cuffDisc (eS.symm '' Θ')
  cuffDisc_closedDisc Θ' hΘ' := by
    have hΘ : eS.symm '' Θ' ∈ cuffs S := by
      rw [cuffs_eq_image_u eS.symm]
      exact mem_image_of_mem _ hΘ'
    rw [← eShat.image_closure]
    exact image_isClosedDisc_u eShat (cap.cuffDisc_closedDisc _ hΘ)
  cuffDisc_bd Θ' hΘ' := by
    have hΘ : eS.symm '' Θ' ∈ cuffs S := by
      rw [cuffs_eq_image_u eS.symm]
      exact mem_image_of_mem _ hΘ'
    rw [← eShat.image_closure, image_discBd_u, cap.cuffDisc_bd _ hΘ, image_comp, image_comp]
  cuffDisc_disjoint Θ₁' hΘ₁' Θ₂' hΘ₂' hne := by
    have hΘ₁ : eS.symm '' Θ₁' ∈ cuffs S := by
      rw [cuffs_eq_image_u eS.symm]
      exact mem_image_of_mem _ hΘ₁'
    have hΘ₂ : eS.symm '' Θ₂' ∈ cuffs S := by
      rw [cuffs_eq_image_u eS.symm]
      exact mem_image_of_mem _ hΘ₂'
    rw [← eShat.image_closure, ← eShat.image_closure]
    exact (disjoint_image_iff eShat.injective).mpr
      (cap.cuffDisc_disjoint _ hΘ₁ _ hΘ₂ (fun h ↦ hne (image_injective.2 eS.symm.injective h)))
  compl_eq := by
    have hrange : range (eShat ∘ cap.emb ∘ eS.symm) = eShat '' range cap.emb := by
      rw [range_comp, (Function.Surjective.range_comp eS.symm.surjective cap.emb)]
    rw [hrange, ← image_compl_eq eShat.bijective, cap.compl_eq, image_iUnion₂,
      cuffs_eq_image_u eS, biUnion_image]
    ext x
    simp [symm_image_image_u]

theorem Painting.hatU_mapHomeo (cap : IsCappedSurface S Shat) (Γ : Painting S) :
    (Γ.mapHomeo eS).hatU (cap.mapHomeo eS eShat) = eShat '' (Γ.hatU cap) := by
  change (eShat ∘ cap.emb ∘ eS.symm) '' (eS '' Γ.U) = eShat '' (cap.emb '' Γ.U)
  rw [image_comp, image_comp, symm_image_image_u]

theorem Painting.hatV_mapHomeo (cap : IsCappedSurface S Shat) (Γ : Painting S) :
    (Γ.mapHomeo eS).hatV (cap.mapHomeo eS eShat) = eShat '' (Γ.hatV cap) := by
  change (eShat ∘ cap.emb ∘ eS.symm) '' (eS '' Γ.V) = eShat '' (cap.emb '' Γ.V)
  rw [image_comp, image_comp, symm_image_image_u]

theorem isPreRadial_mapHomeo {U V : Set Shat} {G : Drawing Shat}
    (h : IsPreRadial U V G) :
    IsPreRadial (eShat '' U) (eShat '' V) (mapDrawingHomeo eShat G) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have hcomp : componentsIn (eShat '' U)ᶜ = (fun r ↦ eShat '' r) '' componentsIn Uᶜ := by
    rw [← image_compl_eq eShat.bijective, image_componentsIn_u]
  refine ⟨?_, image_mono h₂, ?_, ?_, ?_, ?_⟩
  · change eShat '' U ∩ eShat '' G.U = eShat '' V
    rw [← image_inter eShat.injective, h₁]
  · rw [hcomp]
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨w, ⟨hwr, hwV⟩, huniq⟩ := h₃ r hr
    refine ⟨eShat w, ⟨mem_image_of_mem _ hwr, mem_image_of_mem _ hwV⟩, ?_⟩
    rintro _ ⟨⟨y, hyr, rfl⟩, hyV⟩
    have hyV' : y ∈ G.V := (eShat.injective.mem_set_image).mp hyV
    rw [huniq y ⟨hyr, hyV'⟩]
  · rintro _ ⟨⟨w, hwV, rfl⟩, hwU⟩
    have hwU' : w ∉ V := fun h ↦ hwU (mem_image_of_mem _ h)
    obtain ⟨r, hr, hwr⟩ := h₄ w ⟨hwV, hwU'⟩
    rw [hcomp]
    exact ⟨eShat '' r, ⟨r, hr, rfl⟩, mem_image_of_mem _ hwr⟩
  · rw [mapDrawingHomeo_edges]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨v, hv, w, ⟨hwV, hwU⟩, hcl⟩ := h₅ e he
    refine ⟨eShat v, mem_image_of_mem _ hv, eShat w,
      ⟨mem_image_of_mem _ hwV, fun h ↦ hwU ((eShat.injective.mem_set_image).mp h)⟩, ?_⟩
    change closure (eShat '' e) ∩ eShat '' G.V = {eShat v, eShat w}
    rw [← eShat.image_closure, ← image_inter eShat.injective, hcl, image_pair]
  · rw [mapDrawingHomeo_edges, hcomp]
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hne _ ⟨v, hv, rfl⟩ _ ⟨r, hr, rfl⟩
      _ ⟨⟨w, hwr, rfl⟩, hwV⟩ hcle hclf ⟨Δ', hΔ', hsub', hbd'⟩
    have hwV' : w ∈ G.V := (eShat.injective.mem_set_image).mp hwV
    have hne₀ : e ≠ f := fun h ↦ hne (by rw [h])
    have hcle₀ : closure e ∩ G.V = {v, w} := by
      apply image_injective.2 eShat.injective
      rw [image_inter eShat.injective, eShat.image_closure, image_pair]
      exact hcle
    have hclf₀ : closure f ∩ G.V = {v, w} := by
      apply image_injective.2 eShat.injective
      rw [image_inter eShat.injective, eShat.image_closure, image_pair]
      exact hclf
    refine h₆ e he f hf hne₀ v hv r hr w ⟨hwr, hwV'⟩ hcle₀ hclf₀
      ⟨eShat.symm '' Δ', image_isClosedDisc_u eShat.symm hΔ', ?_, ?_⟩
    · rw [← image_subset_image_iff eShat.injective, image_symm_image_u, image_union,
        image_singleton]
      exact hsub'
    · apply image_injective.2 eShat.injective
      rw [← image_subBd_u eShat, image_symm_image_u, hbd', image_union,
        ← eShat.image_closure, ← eShat.image_closure]

theorem isSubdrawing_mapDrawingHomeo {G₁ G₂ : Drawing Shat} (h : G₁.IsSubdrawing G₂) :
    (mapDrawingHomeo eShat G₁).IsSubdrawing (mapDrawingHomeo eShat G₂) := by
  refine ⟨image_mono h.1, ?_⟩
  rw [mapDrawingHomeo_edges, mapDrawingHomeo_edges]
  exact image_mono h.2

/-- Transport a `RadialDrawing` along homeomorphisms `eS : S ≃ₜ S'` and `eShat : Shat ≃ₜ Shat'`. -/
noncomputable def RadialDrawing.mapHomeo {cap : IsCappedSurface S Shat} {Γ : Painting S}
    (rad : RadialDrawing cap Γ) :
    RadialDrawing (cap.mapHomeo eS eShat) (Γ.mapHomeo eS) where
  G := mapDrawingHomeo eShat rad.G
  isPreRadial := by
    rw [Painting.hatU_mapHomeo, Painting.hatV_mapHomeo]
    exact isPreRadial_mapHomeo eShat rad.isPreRadial
  maximal G' hpre hsub := by
    rw [Painting.hatU_mapHomeo, Painting.hatV_mapHomeo] at hpre
    have hpre₀ := isPreRadial_mapHomeo eShat.symm hpre
    rw [symm_image_image_u, symm_image_image_u] at hpre₀
    have hsub₀ : rad.G.IsSubdrawing (mapDrawingHomeo eShat.symm G') := by
      have := isSubdrawing_mapDrawingHomeo eShat.symm hsub
      rwa [mapDrawingHomeo_symm] at this
    have hmax₀ := rad.maximal (mapDrawingHomeo eShat.symm G') hpre₀ hsub₀
    have := isSubdrawing_mapDrawingHomeo eShat.symm.symm hmax₀
    rwa [mapDrawingHomeo_symm eShat.symm] at this

theorem exists_walk_mapDrawingHomeo_edges (H : Drawing Shat) {x y : Shat}
    (W : GraphWalk H.toGraph x y) :
    ∃ W' : GraphWalk (mapDrawingHomeo eShat H).toGraph (eShat x) (eShat y),
      W'.support = W.support.map eShat ∧ W'.edges = W.edges.map (image eShat) := by
  induction W with
  | nil hx => exact ⟨.nil ⟨_, hx, rfl⟩, rfl, rfl⟩
  | cons hl rest ih =>
    obtain ⟨R, h1, h2⟩ := ih
    exact ⟨.cons (isLink_mapDrawingHomeo eShat H hl) R,
      congrArg (List.cons _) h1, congrArg (List.cons _) h2⟩

theorem isCircuit_mapDrawingHomeo {F : Drawing Shat} (h : F.IsCircuit) :
    (mapDrawingHomeo eShat F).IsCircuit := by
  obtain ⟨u, W, ⟨htail, hedges⟩, hlen, hV, hE⟩ := h
  obtain ⟨W', hsupp, hedg⟩ := exists_walk_mapDrawingHomeo_edges eShat F W
  refine ⟨eShat u, W', ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hsupp, ← List.map_tail]
    exact htail.map eShat.injective
  · rw [hedg]
    exact hedges.map (image_injective.2 eShat.injective)
  · change 0 < W'.edges.length
    rw [hedg, List.length_map]
    exact hlen
  · change eShat '' F.V = {x | x ∈ W'.support}
    rw [hV, hsupp]
    ext x; simp
  · rw [mapDrawingHomeo_edges, hE, hedg]
    ext e; simp

theorem isCircuitOf_mapDrawingHomeo
    {F G : Drawing Shat} (h : IsCircuitOf F G) :
    IsCircuitOf (mapDrawingHomeo eShat F) (mapDrawingHomeo eShat G) :=
  ⟨isSubdrawing_mapDrawingHomeo eShat h.1, isCircuit_mapDrawingHomeo eShat h.2⟩

theorem isNullHomotopicOArc_image_u {F : Set Shat} (h : IsNullHomotopicOArc F) :
    IsNullHomotopicOArc (eShat '' F) := by
  obtain ⟨φ, c, -, H, -, h0, h1⟩ := h
  refine ⟨φ.trans (eShat.image F), eShat c, trivial,
    ⟨fun p ↦ eShat (H p), eShat.continuous.comp H.continuous⟩,
    fun _ ↦ trivial, fun x ↦ ?_, fun x ↦ ?_⟩
  · change eShat (H (x, 0)) = eShat (φ x).1
    rw [h0]; rfl
  · change eShat (H (x, 1)) = eShat c
    rw [h1]; rfl

theorem isNullHomotopicOArc_image_iff_u {F : Set Shat} :
    IsNullHomotopicOArc (eShat '' F) ↔ IsNullHomotopicOArc F := by
  constructor
  · intro h
    have := isNullHomotopicOArc_image_u eShat.symm h
    rwa [symm_image_image_u] at this
  · exact isNullHomotopicOArc_image_u eShat

theorem Painting.rep_mapHomeo
    {cap : IsCappedSurface S Shat} {Γ : Painting S} (rad : RadialDrawing cap Γ) :
    Painting.rep (rad.mapHomeo eS eShat) = Painting.rep rad := by
  unfold Painting.rep
  congr 1
  ext n
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨F', hcirc', hnull', rfl⟩
    refine ⟨mapDrawingHomeo eShat.symm F', ?_, ?_, ?_⟩
    · have := isCircuitOf_mapDrawingHomeo eShat.symm hcirc'
      change IsCircuitOf _ (mapDrawingHomeo eShat.symm (mapDrawingHomeo eShat rad.G)) at this
      rwa [mapDrawingHomeo_symm] at this
    · change ¬ IsNullHomotopicOArc (eShat.symm '' F'.U)
      rw [isNullHomotopicOArc_image_iff_u]
      exact hnull'
    · rw [mapDrawingHomeo_edges, ncard_image_of_injective _ (image_injective.2
      eShat.symm.injective)]
  · rintro ⟨F, hcirc, hnull, rfl⟩
    refine ⟨mapDrawingHomeo eShat F, isCircuitOf_mapDrawingHomeo eShat hcirc, ?_, ?_⟩
    · change ¬ IsNullHomotopicOArc (eShat '' F.U)
      rw [isNullHomotopicOArc_image_iff_u]
      exact hnull
    · rw [mapDrawingHomeo_edges, ncard_image_of_injective _ (image_injective.2 eShat.injective)]

end CappedAndRadial

/-! ### Lifting `Theorem62Statement` from universe `0` to universe `u` -/

/-- `Theorem62Statement` in universe `0` implies `Theorem62Statement` in any universe `u`. -/
theorem theorem_6_2_lift (h0 : Theorem62Statement.{0}) : Theorem62Statement.{u} := by
  intro S Shat _ _ _ _ cap hS
  have := cap.connected
  obtain ⟨a, b, c, ⟨eShat⟩⟩ := classification.{u} Shat cap.isSurface cap.connected
  let Shat₀ : Type 0 := SurfaceModel a b c
  have : T2Space Shat₀ := (isSurface_model a b c).1.2.1
  let S₀ : Type 0 := ↥(eShat '' range cap.emb)
  let eS : S ≃ₜ S₀ := cap.isEmbedding.toHomeomorph.trans (eShat.image (range cap.emb))
  have hS₀ : IsSurface S₀ := isSurface_of_homeo eS hS
  let cap₀ : IsCappedSurface S₀ Shat₀ := cap.mapHomeo eS eShat
  obtain ⟨n, hn⟩ := h0 S₀ Shat₀ cap₀ hS₀
  refine ⟨n, fun Φ Γ₁ Γ₂ rad hfit₁ hfit₂ hrep σv σe hinf hresp ↦ ?_⟩
  have hrep₀ : (n : ℕ∞) ≤ Painting.rep (rad.mapHomeo eS eShat) := by
    rwa [Painting.rep_mapHomeo]
  obtain ⟨σv₀', hlin₀, hsub₀⟩ := hn (Φ.mapHomeo eS) (Γ₁.mapHomeo eS) (Γ₂.mapHomeo eS)
    (rad.mapHomeo eS eShat) (hfit₁.mapHomeo eS) (hfit₂.mapHomeo eS) hrep₀
    _ _ (hinf.mapHomeo eS) (hresp.mapHomeo eS)
  refine ⟨fun v ↦ eS.symm '' σv₀' (eS v), ?_, ?_⟩
  · have hlin := hlin₀.mapHomeo eS.symm
    rw [Γ₁.mapHomeo_symm_mapHomeo eS, Γ₂.mapHomeo_symm_mapHomeo eS] at hlin
    have hσe : (fun e' ↦ eS.symm '' (eS '' σe (eS.symm '' (eS.symm.symm '' e')))) = σe := by
      funext e
      change eS.symm '' (eS '' σe (eS.symm '' (eS '' e))) = σe e
      rw [symm_image_image_u, symm_image_image_u]
    rwa [hσe] at hlin
  · intro v hv
    have h₁ := hsub₀ (eS v) (mem_image_of_mem _ hv)
    rw [eS.symm_apply_apply] at h₁
    have h₂ := image_mono (f := eS.symm) h₁
    rwa [symm_image_image_u] at h₂

/-! ### Colour schemes, orientations, refinements, and conditions `S₁`–`S₄` under homeomorphisms -/

section ColourSchemeAndOrientation

variable {S : Type u₁} {S' : Type u₂} [TopologicalSpace S] [TopologicalSpace S']
  {α : Type w} (ψ : S ≃ₜ S')

/-- Transport a `ColourScheme` along a homeomorphism `ψ : S ≃ₜ S'`. -/
noncomputable def ColourScheme.mapHomeo (χ : ColourScheme S α) : ColourScheme S' α where
  isSurface := isSurface_of_homeo ψ χ.isSurface
  connected := by
    have := χ.connected
    exact ψ.surjective.connectedSpace ψ.continuous
  Φ := χ.Φ.mapHomeo ψ
  Ω2 := χ.Ω2
  Ω3 := χ.Ω3
  ΩS s' := χ.ΩS (ψ.symm '' s')
  shortElem s' := χ.shortElem (ψ.symm '' s')
  isWQO_2 := χ.isWQO_2
  isWQO_3 := χ.isWQO_3
  isWQO_S := by
    rw [χ.Φ.mapHomeo_sides ψ]
    rintro _ ⟨s, hs, rfl⟩
    rw [symm_image_image_u]
    exact χ.isWQO_S s hs
  short_singleton := by
    rw [χ.Φ.mapHomeo_shortSides ψ]
    rintro _ ⟨s, hs, rfl⟩
    rw [symm_image_image_u]
    exact χ.short_singleton s hs

/-- Transport a `ColouredPainting` along a homeomorphism `ψ : S ≃ₜ S'`. -/
noncomputable def ColouredPainting.mapHomeo {χ : ColourScheme S α} (P : ColouredPainting χ) :
    ColouredPainting (χ.mapHomeo ψ) where
  Γ := P.Γ.mapHomeo ψ
  φ e' := P.φ (ψ.symm '' e')
  fits := P.fits.mapHomeo ψ
  internal_2_mem := by
    rw [P.Γ.mapHomeo_E ψ]
    rintro _ ⟨e, he, rfl⟩ hi h2
    rw [symm_image_image_u]
    exact P.internal_2_mem e he ((isInternal_image_u ψ).mp hi) (by rwa [ncard_tilde_image_u] at h2)
  internal_3_mem := by
    rw [P.Γ.mapHomeo_E ψ]
    rintro _ ⟨e, he, rfl⟩ hi h3
    rw [symm_image_image_u]
    exact P.internal_3_mem e he ((isInternal_image_u ψ).mp hi) (by rwa [ncard_tilde_image_u] at h3)
  border_mem := by
    change ∀ e ∈ (P.Γ.mapHomeo ψ).E, ∀ s ∈ (χ.Φ.mapHomeo ψ).sides, _
    rw [P.Γ.mapHomeo_E ψ, χ.Φ.mapHomeo_sides ψ]
    rintro _ ⟨e, he, rfl⟩ _ ⟨s, hs, rfl⟩ ⟨hb, hsub⟩
    dsimp only [ColourScheme.mapHomeo]
    rw [symm_image_image_u, symm_image_image_u]
    exact P.border_mem e he s hs ⟨(isBorder_image_u ψ).mp hb,
      (image_subset_image_iff ψ.injective).mp hsub⟩

theorem IsColouredLinearInflation.mapHomeo {χ : ColourScheme S α}
    {P₁ P₂ : ColouredPainting χ} {σv : S → Set S} {σe : Set S → Set S}
    (h : IsColouredLinearInflation χ P₁ P₂ σv σe) :
    IsColouredLinearInflation (χ.mapHomeo ψ) (P₁.mapHomeo ψ) (P₂.mapHomeo ψ)
      (fun v' ↦ ψ '' σv (ψ.symm v')) (fun e' ↦ ψ '' σe (ψ.symm '' e')) where
  isInflation := h.isInflation.mapHomeo ψ
  respects := h.respects.mapHomeo ψ
  le_internal_2 := by
    change ∀ e ∈ (P₁.Γ.mapHomeo ψ).E, _
    rw [P₁.Γ.mapHomeo_E ψ]
    rintro _ ⟨e, he, rfl⟩ hi h2
    dsimp only [ColouredPainting.mapHomeo, ColourScheme.mapHomeo]
    rw [symm_image_image_u, symm_image_image_u]
    exact h.le_internal_2 e he ((isInternal_image_u ψ).mp hi) (by rwa [ncard_tilde_image_u] at h2)
  le_internal_3 := by
    change ∀ e ∈ (P₁.Γ.mapHomeo ψ).E, _
    rw [P₁.Γ.mapHomeo_E ψ]
    rintro _ ⟨e, he, rfl⟩ hi h3
    dsimp only [ColouredPainting.mapHomeo, ColourScheme.mapHomeo]
    rw [symm_image_image_u, symm_image_image_u]
    exact h.le_internal_3 e he ((isInternal_image_u ψ).mp hi) (by rwa [ncard_tilde_image_u] at h3)
  le_border := by
    change ∀ e ∈ (P₁.Γ.mapHomeo ψ).E, ∀ s ∈ (χ.Φ.mapHomeo ψ).sides, _
    rw [P₁.Γ.mapHomeo_E ψ, χ.Φ.mapHomeo_sides ψ]
    rintro _ ⟨e, he, rfl⟩ _ ⟨s, hs, rfl⟩ ⟨hb, hsub⟩
    dsimp only [ColouredPainting.mapHomeo, ColourScheme.mapHomeo]
    rw [symm_image_image_u, symm_image_image_u, symm_image_image_u]
    exact h.le_border e he s hs ⟨(isBorder_image_u ψ).mp hb,
      (image_subset_image_iff ψ.injective).mp hsub⟩
  isLinear := h.isLinear.mapHomeo ψ

theorem IsColouredLinearInflation.unmapHomeo {χ : ColourScheme S α}
    {P₁ P₂ : ColouredPainting χ} {σv' : S' → Set S'} {σe' : Set S' → Set S'}
    (h : IsColouredLinearInflation (χ.mapHomeo ψ) (P₁.mapHomeo ψ) (P₂.mapHomeo ψ) σv' σe') :
    IsColouredLinearInflation χ P₁ P₂
      (fun v ↦ ψ.symm '' σv' (ψ v)) (fun e ↦ ψ.symm '' σe' (ψ '' e)) := by
  have h₁ := h.mapHomeo ψ.symm
  have hΓ₁ : (P₁.mapHomeo ψ).Γ.mapHomeo ψ.symm = P₁.Γ := P₁.Γ.mapHomeo_symm_mapHomeo ψ
  have hΓ₂ : (P₂.mapHomeo ψ).Γ.mapHomeo ψ.symm = P₂.Γ := P₂.Γ.mapHomeo_symm_mapHomeo ψ
  have hΦ : (χ.mapHomeo ψ).Φ.mapHomeo ψ.symm = χ.Φ := χ.Φ.mapHomeo_symm_mapHomeo ψ
  refine
    { isInflation := hΓ₁ ▸ hΓ₂ ▸ h.isInflation.mapHomeo ψ.symm
      respects := hΦ ▸ hΓ₁ ▸ h.respects.mapHomeo ψ.symm
      le_internal_2 := fun e he hi h2 ↦ by
        have := h.le_internal_2 (ψ '' e) (P₁.Γ.mapHomeo_mem ψ he)
          ((isInternal_image_u ψ).mpr hi) (by rwa [ncard_tilde_image_u])
        dsimp only [ColouredPainting.mapHomeo, ColourScheme.mapHomeo] at this
        rwa [symm_image_image_u] at this
      le_internal_3 := fun e he hi h3 ↦ by
        have := h.le_internal_3 (ψ '' e) (P₁.Γ.mapHomeo_mem ψ he)
          ((isInternal_image_u ψ).mpr hi) (by rwa [ncard_tilde_image_u])
        dsimp only [ColouredPainting.mapHomeo, ColourScheme.mapHomeo] at this
        rwa [symm_image_image_u] at this
      le_border := fun e he s hs ⟨hb, hsub⟩ ↦ by
        have hs' : ψ '' s ∈ (χ.mapHomeo ψ).Φ.sides := by
          change ψ '' s ∈ (χ.Φ.mapHomeo ψ).sides
          rw [χ.Φ.mapHomeo_sides ψ]
          exact ⟨s, hs, rfl⟩
        have := h.le_border (ψ '' e) (P₁.Γ.mapHomeo_mem ψ he) (ψ '' s) hs'
          ⟨(isBorder_image_u ψ).mpr hb, image_mono hsub⟩
        dsimp only [ColouredPainting.mapHomeo, ColourScheme.mapHomeo] at this
        rwa [symm_image_image_u, symm_image_image_u] at this
      isLinear := hΓ₁ ▸ hΓ₂ ▸ h.isLinear.mapHomeo ψ.symm }

theorem IsBadSequence.mapHomeo {χ : ColourScheme S α} {P : ℕ → ColouredPainting χ}
    (h : IsBadSequence χ P) :
    IsBadSequence (χ.mapHomeo ψ) (fun i ↦ (P i).mapHomeo ψ) := by
  intro i j hij ⟨σv', σe', hlin⟩
  exact h i j hij ⟨_, _, hlin.unmapHomeo ψ⟩

theorem IsBadSequence.unmapHomeo {χ : ColourScheme S α} {P' : ℕ → ColouredPainting (χ.mapHomeo ψ)}
    (h : IsBadSequence (χ.mapHomeo ψ) P') :
    IsBadSequence (χ.mapHomeo ψ |>.mapHomeo ψ.symm) (fun i ↦ (P' i).mapHomeo ψ.symm) :=
  h.mapHomeo ψ.symm

theorem ColourScheme.IsBad.mapHomeo {χ : ColourScheme S α} (h : χ.IsBad) :
    (χ.mapHomeo ψ).IsBad := by
  obtain ⟨P, hP⟩ := h
  exact ⟨fun i ↦ (P i).mapHomeo ψ, hP.mapHomeo ψ⟩

/-- Transport a `SurfaceOrientation` along a homeomorphism `ψ : S ≃ₜ S'`. -/
def SurfaceOrientation.mapHomeo (ω : SurfaceOrientation S) : SurfaceOrientation S' where
  pos Δ' a' b' c' := ω.pos (ψ.symm '' Δ') (ψ.symm a') (ψ.symm b') (ψ.symm c')
  isDirection Δ' hΔ' := by
    obtain ⟨φ, hcont, hinj, hrange, hpos⟩ :=
      ω.isDirection (ψ.symm '' Δ') (image_isClosedDisc_u ψ.symm hΔ')
    refine ⟨ψ ∘ φ, ψ.continuous.comp hcont, ψ.injective.comp hinj, ?_, ?_⟩
    · rw [range_comp, hrange, ← image_discBd_u, image_symm_image_u]
    · intro a b c hab hbc hac
      dsimp only [Function.comp_apply]
      rw [ψ.symm_apply_apply, ψ.symm_apply_apply, ψ.symm_apply_apply]
      exact hpos a b c hab hbc hac
  agree Δ₁' Δ₂' h₁ h₂ hsub a' b' c' ha' hb' hc' hab hbc hac := by
    have hbd : ∀ {x' : S'} {D' : Set S'}, x' ∈ discBd D' → ψ.symm x' ∈ discBd (ψ.symm '' D') := by
      intro x' D' hx'
      rw [image_discBd_u]
      exact mem_image_of_mem _ hx'
    exact ω.agree (ψ.symm '' Δ₁') (ψ.symm '' Δ₂')
      (image_isClosedDisc_u ψ.symm h₁) (image_isClosedDisc_u ψ.symm h₂) (image_mono hsub)
      (ψ.symm a') (ψ.symm b') (ψ.symm c')
      ⟨hbd ha'.1, hbd ha'.2⟩ ⟨hbd hb'.1, hbd hb'.2⟩ ⟨hbd hc'.1, hbd hc'.2⟩
      (fun h ↦ hab (ψ.symm.injective h))
      (fun h ↦ hbc (ψ.symm.injective h))
      (fun h ↦ hac (ψ.symm.injective h))

include ψ in
theorem isOrientableSurface_iff_u : IsOrientableSurface S' ↔ IsOrientableSurface S :=
  ⟨fun ⟨ω'⟩ ↦ ⟨ω'.mapHomeo ψ.symm⟩, fun ⟨ω⟩ ↦ ⟨ω.mapHomeo ψ⟩⟩

theorem IsSimilarlyOriented.mapHomeo {χ : ColourScheme S α} {P : ℕ → ColouredPainting χ}
    (h : IsSimilarlyOriented χ P) :
    IsSimilarlyOriented (χ.mapHomeo ψ) (fun i ↦ (P i).mapHomeo ψ) := by
  rcases h with hno | ⟨ω, hω⟩
  · exact Or.inl (mt (isOrientableSurface_iff_u ψ).mp hno)
  · refine Or.inr ⟨ω.mapHomeo ψ, fun i e' he' h3 a' b' c' hγ' ↦ ?_⟩
    change e' ∈ ((P i).Γ.mapHomeo ψ).E at he'
    rw [(P i).Γ.mapHomeo_E ψ] at he'
    obtain ⟨e, he, rfl⟩ := he'
    rw [ncard_tilde_image_u] at h3
    change ((P i).Γ.mapHomeo ψ).γ (ψ '' e) = [a', b', c'] at hγ'
    rw [(P i).Γ.mapHomeo_γ ψ] at hγ'
    have hγ : (P i).Γ.γ e = [ψ.symm a', ψ.symm b', ψ.symm c'] := by
      have := congrArg (List.map ψ.symm) hγ'
      rw [List.map_map, show (ψ.symm ∘ ψ : S → S) = id from funext (by simp), List.map_id] at this
      exact this
    change ω.pos (ψ.symm '' closure (ψ '' e)) (ψ.symm a') (ψ.symm b') (ψ.symm c')
    rw [ψ.symm.image_closure, symm_image_image_u]
    exact hω i e he h3 (ψ.symm a') (ψ.symm b') (ψ.symm c') hγ

theorem ColourScheme.IsOrientedlyBad.mapHomeo {χ : ColourScheme S α} (h : χ.IsOrientedlyBad) :
    (χ.mapHomeo ψ).IsOrientedlyBad := by
  obtain ⟨P, hbad, hor⟩ := h
  exact ⟨fun i ↦ (P i).mapHomeo ψ, hbad.mapHomeo ψ, hor.mapHomeo ψ⟩

end ColourSchemeAndOrientation

/-! ### Transporting conditions `S₁`–`S₄` to `Type 0` and lifting `(5.5)` and `(4.1)` -/

section ConditionsAndLifts

variable {S Shat : Type u} [TopologicalSpace S] [TopologicalSpace Shat]
  {S₀ Shat₀ : Type 0} [TopologicalSpace S₀] [TopologicalSpace Shat₀]
  {β : Type w} (eS : S ≃ₜ S₀) (eShat : Shat ≃ₜ Shat₀)

theorem isSimplerThan_of_homeo_both {X : Type u₁} {Y : Type u₂} {X' : Type*} {Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (eX : X ≃ₜ X') (eY : Y ≃ₜ Y') (h : IsSimplerThan X Y) : IsSimplerThan X' Y' := by
  obtain ⟨a, b, c, a', b', c', ⟨hX⟩, ⟨hY⟩, h1, h2, h3⟩ := h
  exact ⟨a, b, c, a', b', c', ⟨eX.symm.trans hX⟩, ⟨eY.symm.trans hY⟩, h1, h2, h3⟩

include eShat in
theorem ConditionS1.mapHomeo (h1 : ConditionS1.{u, w} Shat) :
    ConditionS1.{0, w} Shat₀ := by
  intro S' Shat' _ _ γ χ' ⟨cap'⟩ hsimp hbad
  let uS : S' ≃ₜ ULift.{u} S' := Homeomorph.ulift.symm
  let uShat : Shat' ≃ₜ ULift.{u} Shat' := Homeomorph.ulift.symm
  exact h1 (ULift.{u} S') (ULift.{u} Shat') γ (χ'.mapHomeo uS)
    ⟨cap'.mapHomeo uS uShat⟩
    (isSimplerThan_of_homeo_both uShat eShat.symm hsimp)
    (hbad.mapHomeo uS)

theorem ConditionS2.mapHomeo {cap : IsCappedSurface S Shat} {χ : ColourScheme S β}
    (h2 : ConditionS2 χ cap) :
    ConditionS2 (χ.mapHomeo eS) (cap.mapHomeo eS eShat) := by
  intro S' Shat' _ _ χ' ⟨cap'⟩ ⟨hiso⟩ h3sub h2sub hstrict hobad
  let uS : S' ≃ₜ ULift.{u} S' := Homeomorph.ulift.symm
  let uShat : Shat' ≃ₜ ULift.{u} Shat' := Homeomorph.ulift.symm
  exact h2 (ULift.{u} S') (ULift.{u} Shat') (χ'.mapHomeo uS)
    ⟨cap'.mapHomeo uS uShat⟩
    ⟨uShat.symm.trans (hiso.trans eShat.symm)⟩
    h3sub h2sub hstrict (hobad.mapHomeo uS)

theorem ConditionS3.mapHomeo {cap : IsCappedSurface S Shat} {χ : ColourScheme S β}
    (h3 : ConditionS3 χ cap) :
    ConditionS3 (χ.mapHomeo eS) (cap.mapHomeo eS eShat) := by
  intro S' Shat' _ _ χ' ⟨cap'⟩ ⟨hiso⟩ hΩ2 hΩ3 hcuffs hobad
  let uS : S' ≃ₜ ULift.{u} S' := Homeomorph.ulift.symm
  let uShat : Shat' ≃ₜ ULift.{u} Shat' := Homeomorph.ulift.symm
  have hcuffs' : numCuffs (ULift.{u} S') < numCuffs S := by
    rw [← numCuffs_eq_u uS, numCuffs_eq_u eS]
    exact hcuffs
  exact h3 (ULift.{u} S') (ULift.{u} Shat') (χ'.mapHomeo uS)
    ⟨cap'.mapHomeo uS uShat⟩
    ⟨uShat.symm.trans (hiso.trans eShat.symm)⟩
    hΩ2 hΩ3 hcuffs' (hobad.mapHomeo uS)

theorem ConditionS4.mapHomeo {χ : ColourScheme S β} (h4 : ConditionS4 χ) :
    ConditionS4 (χ.mapHomeo eS) := by
  intro S' _ χ' href hobad
  let uS : S' ≃ₜ ULift.{u} S' := Homeomorph.ulift.symm
  obtain ⟨⟨hiso⟩, hΩ2, hΩ3, f, hmaps, hsub, hstrict, hshort⟩ := href
  have href_u : (χ'.mapHomeo uS).IsRefinement χ := by
    refine ⟨⟨uS.symm.trans (hiso.trans eS.symm)⟩, hΩ2, hΩ3,
      fun R_u ↦ eS.symm '' f (uS.symm '' R_u), ?_, ?_, ?_, ?_⟩
    · intro R_u hR_u
      change R_u ∈ (χ'.Φ.mapHomeo uS).longSides at hR_u
      rw [χ'.Φ.mapHomeo_longSides uS] at hR_u
      obtain ⟨R, hR, rfl⟩ := hR_u
      dsimp only
      rw [symm_image_image_u]
      have hfR := hmaps hR
      change f R ∈ (χ.Φ.mapHomeo eS).longSides at hfR
      rw [χ.Φ.mapHomeo_longSides eS] at hfR
      obtain ⟨s, hs, hs_eq⟩ := hfR
      rw [← hs_eq, symm_image_image_u]
      exact hs
    · intro R_u hR_u
      change R_u ∈ (χ'.Φ.mapHomeo uS).longSides at hR_u
      rw [χ'.Φ.mapHomeo_longSides uS] at hR_u
      obtain ⟨R, hR, rfl⟩ := hR_u
      dsimp only [ColourScheme.mapHomeo]
      rw [symm_image_image_u]
      exact hsub R hR
    · intro R₁_u hR₁_u R₂_u hR₂_u hne heq
      change R₁_u ∈ (χ'.Φ.mapHomeo uS).longSides at hR₁_u
      change R₂_u ∈ (χ'.Φ.mapHomeo uS).longSides at hR₂_u
      rw [χ'.Φ.mapHomeo_longSides uS] at hR₁_u hR₂_u
      obtain ⟨R₁, hR₁, rfl⟩ := hR₁_u
      obtain ⟨R₂, hR₂, rfl⟩ := hR₂_u
      dsimp only [ColourScheme.mapHomeo] at heq ⊢
      rw [symm_image_image_u, symm_image_image_u] at heq
      rw [symm_image_image_u]
      exact hstrict R₁ hR₁ R₂ hR₂ (fun h ↦ hne (by rw [h]))
        (image_injective.2 eS.symm.injective heq)
    · intro hall
      have hcard₁ : (χ'.mapHomeo uS).Φ.shortSides.ncard = χ'.Φ.shortSides.ncard := by
        change (χ'.Φ.mapHomeo uS).shortSides.ncard = _
        rw [χ'.Φ.mapHomeo_shortSides uS,
          ncard_image_of_injective _ (image_injective.2 uS.injective)]
      have hcard₂ : (χ.mapHomeo eS).Φ.shortSides.ncard = χ.Φ.shortSides.ncard := by
        change (χ.Φ.mapHomeo eS).shortSides.ncard = _
        rw [χ.Φ.mapHomeo_shortSides eS,
          ncard_image_of_injective _ (image_injective.2 eS.injective)]
      rw [hcard₁, ← hcard₂]
      refine hshort (fun s₀ hs₀ ↦ ?_)
      change s₀ ∈ (χ.Φ.mapHomeo eS).longSides at hs₀
      rw [χ.Φ.mapHomeo_longSides eS] at hs₀
      obtain ⟨s, hs, rfl⟩ := hs₀
      obtain ⟨R_u, hR_u, hf_eq, hE_eq⟩ := hall s hs
      change R_u ∈ (χ'.Φ.mapHomeo uS).longSides at hR_u
      rw [χ'.Φ.mapHomeo_longSides uS] at hR_u
      obtain ⟨R, hR, rfl⟩ := hR_u
      dsimp only [ColourScheme.mapHomeo] at hf_eq hE_eq ⊢
      rw [symm_image_image_u] at hf_eq hE_eq
      refine ⟨R, hR, ?_, ?_⟩
      · rw [← hf_eq, image_symm_image_u]
      · rw [symm_image_image_u]
        exact hE_eq
  exact h4 (ULift.{u} S') (χ'.mapHomeo uS) href_u (hobad.mapHomeo uS)

/-- `Theorem55Statement` in universe `0` implies `Theorem55Statement` in any universe `u`. -/
theorem theorem_5_5_lift (h0 : Theorem55Statement.{0, w}) : Theorem55Statement.{u, w} := by
  intro S Shat _ _ _ _ β _ cap χ hS1 hS3 P hbad hor rad n
  have := χ.connected
  have := cap.connected
  obtain ⟨a, b, c, ⟨eS⟩⟩ := classification.{u} S χ.isSurface χ.connected
  obtain ⟨a', b', c', ⟨eShat⟩⟩ := classification.{u} Shat cap.isSurface cap.connected
  have : T2Space (SurfaceModel a b c) := (isSurface_model a b c).1.2.1
  have : T2Space (SurfaceModel a' b' c') := (isSurface_model a' b' c').1.2.1
  obtain ⟨h, hh⟩ := h0 (SurfaceModel a b c) (SurfaceModel a' b' c') β
    (cap.mapHomeo eS eShat) (χ.mapHomeo eS)
    (hS1.mapHomeo eShat) (hS3.mapHomeo eS eShat)
    (fun i ↦ (P i).mapHomeo eS) (hbad.mapHomeo eS) (hor.mapHomeo eS)
    (fun i ↦ (rad i).mapHomeo eS eShat) n
  exact ⟨h, fun i hi ↦ (Painting.rep_mapHomeo eS eShat (rad i)) ▸ hh i hi⟩

/-- `Theorem41Statement` in universe `0` implies `Theorem41Statement` in any universe `u`. -/
theorem theorem_4_1_lift (h0 : Theorem41Statement.{0, w}) : Theorem41Statement.{u, w} := by
  intro S Shat _ _ β _ cap χ hS1 hS2 hS3 hS4 hobad
  have := χ.connected
  have := cap.connected
  obtain ⟨a, b, c, ⟨eS⟩⟩ := classification.{u} S χ.isSurface χ.connected
  obtain ⟨a', b', c', ⟨eShat⟩⟩ := classification.{u} Shat cap.isSurface cap.connected
  exact h0 (SurfaceModel a b c) (SurfaceModel a' b' c') β
    (cap.mapHomeo eS eShat) (χ.mapHomeo eS)
    (hS1.mapHomeo eShat) (hS2.mapHomeo eS eShat) (hS3.mapHomeo eS eShat) (hS4.mapHomeo eS)
    (hobad.mapHomeo eS)

end ConditionsAndLifts

end GraphMinor.GM19

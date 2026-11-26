/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Thinning
public import LeanPool.GraphMinor.Surface.Classification
public import LeanPool.GraphMinor.Surface.AddCrosscap
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Universe-polymorphic transport of paintings, frames, thinnings, and inflations

This file transports paintings, frames, thinnings, and inflations along a homeomorphism
`ψ : S ≃ₜ S'` between surfaces in arbitrary universes `Type u₁` and `Type u₂`. Using
`Surface.classification.{u}`, this immediately lifts `Theorem21TopologyStatement.{0}` to
`Theorem21TopologyStatement.{u}`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u u₁ u₂ w

section BasicHomeo

variable {S : Type u₁} {S' : Type u₂} [TopologicalSpace S] [TopologicalSpace S'] (ψ : S ≃ₜ S')

theorem symm_image_image_u (A : Set S) : ψ.symm '' (ψ '' A) = A := by
  rw [← image_comp]
  simp

theorem image_symm_image_u (A : Set S') : ψ '' (ψ.symm '' A) = A := by
  rw [← image_comp]
  simp

theorem image_tilde_u (c : Set S) : tilde (ψ '' c) = ψ '' tilde c :=
  Surface.image_tilde_homeomorph ψ c

theorem ncard_tilde_image_u (c : Set S) : (tilde (ψ '' c)).ncard = (tilde c).ncard := by
  rw [image_tilde_u, ncard_image_of_injective _ ψ.injective]

theorem image_arcComponentsIn_u (F : Set S) :
    arcComponentsIn (ψ '' F) = (fun c ↦ ψ '' c) '' arcComponentsIn F :=
  GM07.arcComponentsIn_image_homeo ψ F

theorem image_componentsIn_u (F : Set S) :
    componentsIn (ψ '' F) = (fun c ↦ ψ '' c) '' componentsIn F :=
  componentsIn_image (f' := ψ.symm) ψ.continuous.continuousOn ψ.symm.continuous.continuousOn
    (fun x _ ↦ by simp)

theorem image_isClosedDisc_u {Δ : Set S} (h : IsClosedDisc Δ) : IsClosedDisc (ψ '' Δ) :=
  Surface.image_isClosedDisc_homeomorph ψ h

theorem image_isOArc_u {F : Set S} (h : IsOArc F) : IsOArc (ψ '' F) :=
  Surface.image_isOArc_homeomorph ψ h

theorem image_isLine_u {F : Set S} (h : IsLine F) : IsLine (ψ '' F) :=
  Surface.image_isLine_homeomorph ψ h

theorem image_discBd_u (Δ : Set S) : discBd (ψ '' Δ) = ψ '' discBd Δ :=
  Surface.image_discBd_homeomorph ψ Δ

theorem image_lineEnds_subset_u (F : Set S) : ψ '' lineEnds F ⊆ lineEnds (ψ '' F) :=
  Surface.image_lineEnds_subset_homeomorph ψ F

theorem image_lineEnds_u {S : Type u₁} {S' : Type u₂} [TopologicalSpace S] [TopologicalSpace S']
    (ψ : S ≃ₜ S') (F : Set S) : lineEnds (ψ '' F) = ψ '' lineEnds F :=
  Surface.image_lineEnds_homeomorph ψ F

theorem cuffs_eq_image_u : cuffs S' = (fun C ↦ ψ '' C) '' cuffs S :=
  Surface.image_cuffs_homeomorph ψ

include ψ in
theorem numCuffs_eq_u : numCuffs S = numCuffs S' := by
  have hinj : Injective fun C : Set S ↦ ψ '' C := image_injective.2 ψ.injective
  unfold numCuffs
  rw [cuffs_eq_image_u ψ, ncard_image_of_injective _ hinj]

theorem isBorder_image_u {e : Set S} : Painting.IsBorder (ψ '' e) ↔ Painting.IsBorder e := by
  have hset : ψ '' e ∩ bd S' = ψ '' (e ∩ bd S) := by
    conv_lhs => rw [← image_bd ψ]
    exact (image_inter ψ.injective).symm
  simp only [Painting.IsBorder, hset, image_nonempty]

theorem isInternal_image_u {e : Set S} : Painting.IsInternal (ψ '' e) ↔ Painting.IsInternal e := by
  rw [isInternal_iff_not_border, isInternal_iff_not_border, isBorder_image_u]

end BasicHomeo

section PaintingAndFrame

variable {S : Type u₁} {S' : Type u₂} [TopologicalSpace S] [TopologicalSpace S'] (ψ : S ≃ₜ S')

/-- The image of a painting `Γ` under a homeomorphism `ψ : S ≃ₜ S'`. -/
noncomputable def Painting.mapHomeo (Γ : Painting S) : Painting S' where
  U := ψ '' Γ.U
  V := ψ '' Γ.V
  γ e := (Γ.γ (ψ.symm '' e)).map ψ
  isClosed_U := ψ.isClosed_image.mpr Γ.isClosed_U
  V_subset := image_mono Γ.V_subset
  finite_V := Γ.finite_V.image _
  bd_subset := by
    rw [← image_bd ψ]
    exact image_mono Γ.bd_subset
  finite_edges := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn_u]
    exact Γ.finite_edges.image _
  edge_shape := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨c, hc, rfl⟩
    simp only
    rw [image_tilde_u, ncard_image_of_injective _ ψ.injective, ← ψ.image_closure]
    rcases Γ.edge_shape c hc with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · refine Or.inl ⟨h₁, h₂.image _, image_isLine_u ψ h₃, ?_⟩
      rw [image_lineEnds_u, h₄]
    · refine Or.inr ⟨h₁, h₂.image _, image_isClosedDisc_u ψ h₃, ?_⟩
      rw [image_discBd_u]
      exact image_mono h₄
  γ_nodup := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨c, hc, rfl⟩
    simp only
    rw [symm_image_image_u ψ]
    exact (Γ.γ_nodup c hc).map ψ.injective
  γ_set := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨c, hc, rfl⟩
    simp only
    rw [symm_image_image_u ψ, image_tilde_u, ← Γ.γ_set c hc]
    ext x
    simp
  border_edge := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨c, hc, rfl⟩ hb
    simp only at hb ⊢
    have hb' : Painting.IsBorder c := (isBorder_image_u ψ).mp hb
    obtain ⟨h₁, h₂⟩ := Γ.border_edge c hc hb'
    refine ⟨by rw [image_tilde_u, ncard_image_of_injective _ ψ.injective, h₁], ?_⟩
    rw [← image_bd ψ]
    exact image_mono h₂

theorem Painting.mapHomeo_E (Γ : Painting S) : (Γ.mapHomeo ψ).E = (fun c ↦ ψ '' c) '' Γ.E := by
  change arcComponentsIn (ψ '' Γ.U \ ψ '' Γ.V) = (fun c ↦ ψ '' c) '' arcComponentsIn (Γ.U \ Γ.V)
  rw [← image_sdiff ψ.injective, image_arcComponentsIn_u]

theorem Painting.mapHomeo_mem (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) :
    ψ '' e ∈ (Γ.mapHomeo ψ).E := by
  rw [Γ.mapHomeo_E ψ]
  exact ⟨e, he, rfl⟩

theorem Painting.mapHomeo_γ (Γ : Painting S) (e : Set S) :
    (Γ.mapHomeo ψ).γ (ψ '' e) = (Γ.γ e).map ψ := by
  change (Γ.γ (ψ.symm '' (ψ '' e))).map ψ = _
  rw [symm_image_image_u ψ]

theorem Painting.mapHomeo_regions (Γ : Painting S) :
    (Γ.mapHomeo ψ).regions = (fun r ↦ ψ '' r) '' Γ.regions := by
  change componentsIn (ψ '' Γ.U)ᶜ = (fun r ↦ ψ '' r) '' componentsIn Γ.Uᶜ
  rw [← image_compl_eq ψ.bijective]
  exact image_componentsIn_u ψ Γ.Uᶜ

@[ext]
theorem Painting.ext {Γ₁ Γ₂ : Painting S} (hU : Γ₁.U = Γ₂.U) (hV : Γ₁.V = Γ₂.V)
    (hγ : Γ₁.γ = Γ₂.γ) : Γ₁ = Γ₂ := by
  cases Γ₁; cases Γ₂; congr

theorem Painting.mapHomeo_symm_mapHomeo (Γ : Painting S) :
    (Γ.mapHomeo ψ).mapHomeo ψ.symm = Γ := by
  apply Painting.ext
  · exact symm_image_image_u ψ _
  · exact symm_image_image_u ψ _
  · funext e
    change List.map ψ.symm (List.map ψ (Γ.γ (ψ.symm '' (ψ '' e)))) = Γ.γ e
    rw [symm_image_image_u ψ, List.map_map,
      show (ψ.symm ∘ ψ : S → S) = id from funext (by simp), List.map_id]

theorem Painting.mapHomeo_internally {Γ : Painting S} (hΓ : Γ.IsInternallyThreeConnected) :
    (Γ.mapHomeo ψ).IsInternallyThreeConnected := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he⟩ := hΓ.1
    exact ⟨_, Γ.mapHomeo_mem ψ he⟩
  · intro F hF hFU hfin hcard
    change F ∩ ψ '' Γ.U ⊆ ψ '' Γ.V at hFU
    change (F ∩ ψ '' Γ.V).ncard + _ ≤ 2 at hcard
    have himg : ∀ A : Set S, ψ.symm '' (F ∩ ψ '' A) = (ψ.symm '' F) ∩ A := fun A ↦ by
      rw [image_inter ψ.symm.injective, symm_image_image_u ψ]
    have hbd : ψ.symm '' (F ∩ bd S') = (ψ.symm '' F) ∩ bd S := by
      rw [image_inter ψ.symm.injective, image_bd ψ.symm]
    obtain ⟨D, h₁, h₂, h₃⟩ := hΓ.2 (ψ.symm '' F) (image_isOArc_u ψ.symm hF)
      (by
        rw [← himg]
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨v, hv, rfl⟩ := hFU hy
        simpa using hv)
      (by rw [← hbd]; exact hfin.image _)
      (by
        rw [← himg, ← hbd, ncard_image_of_injective _ ψ.symm.injective,
          ncard_image_of_injective _ ψ.symm.injective]
        exact hcard)
    refine ⟨ψ '' D, image_isClosedDisc_u ψ h₁, ?_, ?_⟩
    · rw [image_discBd_u, h₂, image_symm_image_u]
    · rintro _ ⟨⟨y, hy, rfl⟩, ⟨v, hv, he⟩⟩
      obtain rfl : y = v := ψ.injective he.symm
      obtain ⟨z, hz, hzy⟩ := h₃ ⟨hy, hv⟩
      have : ψ y = z := by rw [← hzy]; simp
      rw [this]
      exact hz

/-- The image of a frame `Φ` under a homeomorphism `ψ : S ≃ₜ S'`. -/
noncomputable def Frame.mapHomeo (Φ : Frame S) : Frame S' where
  V := ψ '' Φ.V
  γ s := (Φ.γ (ψ.symm '' s)).map ψ
  isLong s := Φ.isLong (ψ.symm '' s)
  V_subset := by
    rw [← image_bd ψ]
    exact image_mono Φ.V_subset
  finite_V := Φ.finite_V.image _
  finite_sides := by
    rw [← image_bd ψ, ← image_sdiff ψ.injective, image_arcComponentsIn_u]
    exact Φ.finite_sides.image _
  side_shape := by
    rw [← image_bd ψ, ← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Φ.side_shape s hs
    rw [image_tilde_u, ncard_image_of_injective _ ψ.injective, ← ψ.image_closure,
      image_lineEnds_u, h₄]
    exact ⟨h₁, h₂.image _, image_isLine_u ψ h₃, rfl⟩
  γ_nodup := by
    rw [← image_bd ψ, ← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨s, hs, rfl⟩
    simp only [symm_image_image_u]
    exact (Φ.γ_nodup s hs).map ψ.injective
  γ_set := by
    rw [← image_bd ψ, ← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨s, hs, rfl⟩
    simp only [symm_image_image_u, image_tilde_u, ← Φ.γ_set s hs]
    ext x
    simp
  long_disjoint := by
    rw [← image_bd ψ, ← image_sdiff ψ.injective, image_arcComponentsIn_u]
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ hne hl₁ hl₂
    simp only [symm_image_image_u] at hl₁ hl₂
    rw [image_tilde_u, image_tilde_u]
    exact (disjoint_image_iff ψ.injective).mpr
      (Φ.long_disjoint s₁ hs₁ s₂ hs₂ (fun h ↦ hne (by rw [h])) hl₁ hl₂)

theorem Frame.mapHomeo_sides (Φ : Frame S) :
    (Φ.mapHomeo ψ).sides = (fun s ↦ ψ '' s) '' Φ.sides := by
  change arcComponentsIn (bd S' \ ψ '' Φ.V) = (fun s ↦ ψ '' s) '' arcComponentsIn (bd S \ Φ.V)
  rw [← image_bd ψ, ← image_sdiff ψ.injective, image_arcComponentsIn_u]

theorem Frame.mapHomeo_longSides (Φ : Frame S) :
    (Φ.mapHomeo ψ).longSides = (fun s ↦ ψ '' s) '' Φ.longSides := by
  ext s'
  simp only [Frame.longSides, mem_ofPred_eq, Φ.mapHomeo_sides ψ, mem_image]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hl⟩
    change Φ.isLong (ψ.symm '' (ψ '' s)) at hl
    rw [symm_image_image_u] at hl
    exact ⟨s, ⟨hs, hl⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hl⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, ?_⟩
    change Φ.isLong (ψ.symm '' (ψ '' s))
    rwa [symm_image_image_u]

theorem Frame.mapHomeo_shortSides (Φ : Frame S) :
    (Φ.mapHomeo ψ).shortSides = (fun s ↦ ψ '' s) '' Φ.shortSides := by
  ext s'
  simp only [Frame.shortSides, mem_ofPred_eq, Φ.mapHomeo_sides ψ, mem_image]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hl⟩
    change ¬ Φ.isLong (ψ.symm '' (ψ '' s)) at hl
    rw [symm_image_image_u] at hl
    exact ⟨s, ⟨hs, hl⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hl⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, ?_⟩
    change ¬ Φ.isLong (ψ.symm '' (ψ '' s))
    rwa [symm_image_image_u]

theorem Frame.mapHomeo_γ (Φ : Frame S) (s : Set S) :
    (Φ.mapHomeo ψ).γ (ψ '' s) = (Φ.γ s).map ψ := by
  change (Φ.γ (ψ.symm '' (ψ '' s))).map ψ = _
  rw [symm_image_image_u ψ]

@[ext]
theorem Frame.ext {Φ₁ Φ₂ : Frame S} (hV : Φ₁.V = Φ₂.V) (hγ : Φ₁.γ = Φ₂.γ)
    (hl : Φ₁.isLong = Φ₂.isLong) : Φ₁ = Φ₂ := by
  cases Φ₁; cases Φ₂; congr

theorem Frame.mapHomeo_symm_mapHomeo (Φ : Frame S) :
    (Φ.mapHomeo ψ).mapHomeo ψ.symm = Φ := by
  apply Frame.ext
  · exact symm_image_image_u ψ _
  · funext s
    change List.map ψ.symm (List.map ψ (Φ.γ (ψ.symm '' (ψ '' s)))) = Φ.γ s
    rw [symm_image_image_u ψ, List.map_map,
      show (ψ.symm ∘ ψ : S → S) = id from funext (by simp), List.map_id]
  · funext s
    change Φ.isLong (ψ.symm '' (ψ '' s)) = Φ.isLong s
    rw [symm_image_image_u ψ]

theorem dirAgrees_image_u {s : Set S} {γs : List S} {e : Set S} {γe : List S}
    (h : DirAgrees s γs e γe) :
    DirAgrees (ψ '' s) (γs.map ψ) (ψ '' e) (γe.map ψ) := by
  obtain ⟨f, t₁, t₂, hlt, hsub, h₁, h₂, h₃, h₄⟩ := h
  have hcl : closure (ψ '' s) = ψ '' closure s := (ψ.image_closure s).symm
  let f' : Icc (0 : ℝ) 1 ≃ₜ closure (ψ '' s) :=
    f.trans ((ψ.image (closure s)).trans (Homeomorph.setCongr hcl.symm))
  refine ⟨f', t₁, t₂, hlt, image_mono hsub, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, h₁]
    rfl
  · rw [List.getLast?_map, h₂]
    rfl
  · rw [List.head?_map, h₃]
    rfl
  · rw [List.getLast?_map, h₄]
    rfl

theorem Painting.Fits.mapHomeo {Γ : Painting S} {Φ : Frame S} (hf : Γ.Fits Φ) :
    (Γ.mapHomeo ψ).Fits (Φ.mapHomeo ψ) := by
  refine
    { V_subset := image_mono hf.V_subset
      short_sides := by
        rw [Φ.mapHomeo_shortSides ψ, Γ.mapHomeo_E ψ]
        exact image_mono hf.short_sides
      border_dir := ?_
      internally_three_connected := Γ.mapHomeo_internally ψ hf.internally_three_connected
      size_three_region := ?_ }
  · rw [Γ.mapHomeo_E ψ, Φ.mapHomeo_sides ψ]
    rintro _ ⟨e, he, rfl⟩ hb _ ⟨s, hs, rfl⟩ hes
    rw [Φ.mapHomeo_γ ψ, Γ.mapHomeo_γ ψ]
    exact dirAgrees_image_u ψ (hf.border_dir e he ((isBorder_image_u ψ).mp hb) s hs
      ((image_subset_image_iff ψ.injective).mp hes))
  · rw [Γ.mapHomeo_E ψ, Γ.mapHomeo_regions ψ]
    rintro _ ⟨e, he, rfl⟩ h3 _ ⟨r, hr, rfl⟩ hcard f' hf'
    rw [ncard_tilde_image_u ψ] at h3
    have hcard₀ : 3 ≤ (closure r ∩ Γ.V).ncard := by
      have : closure (ψ '' r) ∩ (Γ.mapHomeo ψ).V = ψ '' (closure r ∩ Γ.V) := by
        change closure (ψ '' r) ∩ ψ '' Γ.V = _
        rw [← ψ.image_closure, image_inter ψ.injective]
      rw [this, ncard_image_of_injective _ ψ.injective] at hcard
      exact hcard
    have hf₀ : f' ∈ (fun c ↦ ψ '' c) '' componentsIn (e ∩ closure r) := by
      rw [← image_componentsIn_u ψ, image_inter ψ.injective, ψ.image_closure]
      exact hf'
    obtain ⟨f, hf_mem, rfl⟩ := hf₀
    obtain ⟨x, hx⟩ := hf.size_three_region e he h3 r hr hcard₀ f hf_mem
    refine ⟨ψ x, ?_⟩
    rw [← ψ.image_closure, ← image_bd ψ, ← image_inter ψ.injective]
    exact mem_image_of_mem _ hx

end PaintingAndFrame

section Thinning

variable {S : Type u₁} {S₀ : Type u₂} [TopologicalSpace S] [TopologicalSpace S₀] (ψ : S ≃ₜ S₀)

theorem hasNullSignature_conj {h₀ : S₀ ≃ₜ S₀} (hh₀ : HasNullSignature h₀) :
    HasNullSignature (ψ.trans (h₀.trans ψ.symm)) := by
  intro C φ hC
  have hC₀ : ψ '' C ∈ cuffs S₀ := by
    rw [cuffs_eq_image_u ψ]
    exact mem_image_of_mem _ hC
  let φ₀ : Circle ≃ₜ ↥(ψ '' C) := φ.trans (ψ.image C)
  obtain ⟨g, hg₁, hg₂⟩ := hh₀ (ψ '' C) φ₀ hC₀
  refine ⟨g, hg₁, fun x ↦ ?_⟩
  have hx := hg₂ x
  change h₀ (ψ (φ x).1) = ψ (φ (g x)).1 at hx
  change ψ.symm (h₀ (ψ (φ x).1)) = (φ (g x)).1
  rw [hx, ψ.symm_apply_apply]

theorem IsThinning.pull {Φ₀ : Frame S₀} {Γ : Painting S} {h₀ : S₀ ≃ₜ S₀} {Γ₀' : Painting S₀}
    {s₀ : Set S₀ → Set S₀} (T₀ : IsThinning Φ₀ (Γ.mapHomeo ψ) h₀ Γ₀' s₀) :
    IsThinning (Φ₀.mapHomeo ψ.symm) Γ (ψ.trans (h₀.trans ψ.symm)) (Γ₀'.mapHomeo ψ.symm)
      (fun e ↦ ψ.symm '' s₀ (ψ '' e)) := by
  set h : S ≃ₜ S := ψ.trans (h₀.trans ψ.symm)
  have h_img : ∀ A : Set S, h '' A = ψ.symm '' (h₀ '' (ψ '' A)) := fun A ↦ by
    ext x
    simp [h]
  have h_map : ∀ l : List S, l.map h = ((l.map ψ).map h₀).map ψ.symm := fun l ↦ by
    simp [h, List.map_map, Function.comp_def]
  have hsymm_eq : h.symm = ψ.trans (h₀.symm.trans ψ.symm) := by
    ext x
    rfl
  refine
    { null := hasNullSignature_conj ψ T₀.null
      null_symm := hsymm_eq ▸ hasNullSignature_conj ψ T₀.null_symm
      V_eq := by
        change ψ.symm '' Γ₀'.V = h '' Γ.V
        rw [T₀.V_eq, h_img]
        rfl
      fits := T₀.fits.mapHomeo ψ.symm
      three := ?_
      three_inj := ?_
      three_surj := ?_
      two := ?_
      internal_γ := ?_
      border_γ := ?_
      rest := ?_
      short := ?_ }
  · intro e he h3
    obtain ⟨h₁, h₂, h₃⟩ := T₀.three (ψ '' e) (Γ.mapHomeo_mem ψ he)
      (by rw [ncard_tilde_image_u, h3])
    refine ⟨Γ₀'.mapHomeo_mem ψ.symm h₁, ?_, ?_⟩
    · rw [image_tilde_u, h₂, image_tilde_u, ← h_img]
    · rw [Γ₀'.mapHomeo_γ ψ.symm, h₃, Γ.mapHomeo_γ ψ, h_map]
  · intro e₁ he₁ e₂ he₂ heq
    have hs := image_injective.2 ψ.symm.injective heq
    have h₁ : ψ '' e₁ ∈ {e' ∈ (Γ.mapHomeo ψ).E | (tilde e').ncard = 3} :=
      ⟨Γ.mapHomeo_mem ψ he₁.1, by rw [ncard_tilde_image_u, he₁.2]⟩
    have h₂ : ψ '' e₂ ∈ {e' ∈ (Γ.mapHomeo ψ).E | (tilde e').ncard = 3} :=
      ⟨Γ.mapHomeo_mem ψ he₂.1, by rw [ncard_tilde_image_u, he₂.2]⟩
    exact image_injective.2 ψ.injective (T₀.three_inj h₁ h₂ hs)
  · intro e' he' h3
    rw [Γ₀'.mapHomeo_E ψ.symm] at he'
    obtain ⟨c₀, hc₀, rfl⟩ := he'
    rw [ncard_tilde_image_u] at h3
    obtain ⟨e₀, he₀, h3₀, rfl⟩ := T₀.three_surj c₀ hc₀ h3
    rw [Γ.mapHomeo_E ψ] at he₀
    obtain ⟨e, he, rfl⟩ := he₀
    rw [ncard_tilde_image_u] at h3₀
    exact ⟨e, he, h3₀, rfl⟩
  · intro e he h2
    rw [h_img]
    exact Γ₀'.mapHomeo_mem ψ.symm (T₀.two (ψ '' e) (Γ.mapHomeo_mem ψ he)
      (by rw [ncard_tilde_image_u, h2]))
  · intro e he h2 hi
    rw [h_img, Γ₀'.mapHomeo_γ ψ.symm, T₀.internal_γ (ψ '' e) (Γ.mapHomeo_mem ψ he)
      (by rw [ncard_tilde_image_u, h2]) ((isInternal_image_u ψ).mpr hi),
      Γ.mapHomeo_γ ψ, h_map]
  · intro e he hb
    rw [h_img, Γ₀'.mapHomeo_γ ψ.symm]
    rcases T₀.border_γ (ψ '' e) (Γ.mapHomeo_mem ψ he) ((isBorder_image_u ψ).mpr hb) with hγ | hγ
    · left
      rw [hγ, Γ.mapHomeo_γ ψ, h_map]
    · right
      rw [hγ, Γ.mapHomeo_γ ψ, h_map]
      exact List.map_reverse
  · intro e' he' h2
    rw [Γ₀'.mapHomeo_E ψ.symm] at he'
    obtain ⟨c₀, hc₀, rfl⟩ := he'
    rw [ncard_tilde_image_u] at h2
    rcases T₀.rest c₀ hc₀ h2 with ⟨e₀, he₀, h2₀, rfl⟩ | ⟨hi₀, d₀, hd₀, h3₀, hsub₀⟩
    · rw [Γ.mapHomeo_E ψ] at he₀
      obtain ⟨e, he, rfl⟩ := he₀
      rw [ncard_tilde_image_u] at h2₀
      dsimp only
      exact Or.inl ⟨e, he, h2₀, h_img e⟩
    · rw [Γ.mapHomeo_E ψ] at hd₀
      obtain ⟨d, hd, rfl⟩ := hd₀
      rw [ncard_tilde_image_u] at h3₀
      refine Or.inr ⟨(isInternal_image_u ψ.symm).mpr hi₀, d, hd, h3₀, ?_⟩
      rw [image_tilde_u, h_img, ← image_tilde_u ψ]
      exact image_mono hsub₀
  · intro t ht
    rw [Φ₀.mapHomeo_shortSides ψ.symm] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    obtain ⟨e₀, he₀, rfl⟩ := T₀.short t₀ ht₀
    rw [Γ.mapHomeo_E ψ] at he₀
    obtain ⟨e, he, rfl⟩ := he₀
    dsimp only
    exact ⟨e, he, h_img e⟩

/-- `Theorem21TopologyStatement` in universe `0` implies `Theorem21TopologyStatement` in any
universe `u`, via `Surface.classification`. -/
theorem theorem21Topology_of_zero (h0 : Theorem21TopologyStatement.{0}) :
    Theorem21TopologyStatement.{u} := by
  intro S _ hS hc
  obtain ⟨a, b, c, ⟨ψ⟩⟩ := classification.{u} S hS hc
  have hS₀ : IsSurface (SurfaceModel a b c) := isSurface_of_homeo ψ hS
  have hc₀ : ConnectedSpace (SurfaceModel a b c) := ψ.surjective.connectedSpace ψ.continuous
  obtain ⟨Φ₀, hΦ₀⟩ := h0 (SurfaceModel a b c) hS₀ hc₀
  refine ⟨Φ₀.mapHomeo ψ.symm, fun Γ hΓ ↦ ?_⟩
  obtain ⟨h₀, Γ₀', s₀, T₀⟩ := hΦ₀ (Γ.mapHomeo ψ) (Γ.mapHomeo_internally ψ hΓ)
  exact ⟨_, _, _, T₀.pull ψ⟩

/-- **The topology in the proof of Graph Minors XIX, (2.1), in any universe `u`.** -/
theorem theorem21Topology_u : Theorem21TopologyStatement.{u} :=
  theorem21Topology_of_zero theorem21Topology

end Thinning

section Inflation

variable {S : Type u₁} {S' : Type u₂} [TopologicalSpace S] [TopologicalSpace S'] (ψ : S ≃ₜ S')

theorem skAdj_mapHomeo (Γ : Painting S) {x y : S} :
    (Γ.mapHomeo ψ).skAdj.Adj (ψ x) (ψ y) ↔ Γ.skAdj.Adj x y := by
  constructor
  · rintro ⟨hne, hx, hy, e', he', hxe, hye⟩
    change ψ x ∈ ψ '' Γ.V at hx
    change ψ y ∈ ψ '' Γ.V at hy
    rw [Γ.mapHomeo_E ψ] at he'
    obtain ⟨e, he, rfl⟩ := he'
    rw [image_tilde_u] at hxe hye
    exact ⟨fun h ↦ hne (congrArg ψ h), (ψ.injective.mem_set_image).mp hx,
      (ψ.injective.mem_set_image).mp hy, e, he,
      (ψ.injective.mem_set_image).mp hxe, (ψ.injective.mem_set_image).mp hye⟩
  · rintro ⟨hne, hx, hy, e, he, hxe, hye⟩
    refine ⟨fun h ↦ hne (ψ.injective h), mem_image_of_mem _ hx, mem_image_of_mem _ hy,
      ψ '' e, Γ.mapHomeo_mem ψ he, ?_, ?_⟩ <;>
    · rw [image_tilde_u]
      exact mem_image_of_mem _ ‹_›

theorem preconnected_induce_mapHomeo (Γ : Painting S) {A : Set S}
    (h : (Γ.skAdj.induce A).Preconnected) :
    ((Γ.mapHomeo ψ).skAdj.induce (ψ '' A)).Preconnected := by
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
  have hwalk : ∀ {a b : A}, (Γ.skAdj.induce A).Walk a b →
      ((Γ.mapHomeo ψ).skAdj.induce (ψ '' A)).Reachable
        ⟨ψ a.1, mem_image_of_mem _ a.2⟩ ⟨ψ b.1, mem_image_of_mem _ b.2⟩ := by
    intro a b w
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w hadj _ ih =>
      have hadj' : ((Γ.mapHomeo ψ).skAdj.induce (ψ '' A)).Adj
          ⟨ψ u.1, mem_image_of_mem _ u.2⟩ ⟨ψ v.1, mem_image_of_mem _ v.2⟩ :=
        (skAdj_mapHomeo ψ Γ).mpr hadj
      exact hadj'.reachable.trans ih
  obtain ⟨w⟩ := h ⟨x, hx⟩ ⟨y, hy⟩
  exact hwalk w

theorem IsInflation.mapHomeo {Γ₁ Γ₂ : Painting S} {σv : S → Set S} {σe : Set S → Set S}
    (h : IsInflation Γ₁ Γ₂ σv σe) :
    IsInflation (Γ₁.mapHomeo ψ) (Γ₂.mapHomeo ψ)
      (fun v' ↦ ψ '' σv (ψ.symm v')) (fun e' ↦ ψ '' σe (ψ.symm '' e')) where
  edge_mem := by
    rw [Γ₁.mapHomeo_E ψ]
    rintro _ ⟨e, he, rfl⟩
    rw [symm_image_image_u]
    exact Γ₂.mapHomeo_mem ψ (h.edge_mem e he)
  edge_size := by
    rw [Γ₁.mapHomeo_E ψ]
    rintro _ ⟨e, he, rfl⟩
    rw [symm_image_image_u, ncard_tilde_image_u, ncard_tilde_image_u]
    exact h.edge_size e he
  edge_injOn := by
    rw [Γ₁.mapHomeo_E ψ]
    rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ heq
    dsimp only at heq ⊢
    rw [symm_image_image_u, symm_image_image_u] at heq
    rw [h.edge_injOn he₁ he₂ (image_injective.2 ψ.injective heq)]
  vertex_nonempty := by
    rintro _ ⟨v, hv, rfl⟩
    rw [ψ.symm_apply_apply]
    exact (h.vertex_nonempty v hv).image _
  vertex_subset := by
    rintro _ ⟨v, hv, rfl⟩
    rw [ψ.symm_apply_apply]
    exact image_mono (h.vertex_subset v hv)
  vertex_connected := by
    rintro _ ⟨v, hv, rfl⟩
    rw [ψ.symm_apply_apply]
    exact preconnected_induce_mapHomeo ψ Γ₂ (h.vertex_connected v hv)
  vertex_disjoint := by
    rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ hne
    rw [ψ.symm_apply_apply, ψ.symm_apply_apply]
    exact (disjoint_image_iff ψ.injective).mpr
      (h.vertex_disjoint v₁ hv₁ v₂ hv₂ (fun he ↦ hne (congrArg ψ he)))
  ends := by
    rw [Γ₁.mapHomeo_E ψ]
    rintro _ ⟨e, he, rfl⟩ i hi hi'
    simp only [symm_image_image_u, Γ₁.mapHomeo_γ ψ, Γ₂.mapHomeo_γ ψ, List.length_map] at hi hi' ⊢
    simp only [List.getElem_map, ψ.symm_apply_apply]
    exact mem_image_of_mem _ (h.ends e he i hi hi')

theorem RespectsFrame.mapHomeo {Φ : Frame S} {Γ₁ : Painting S} {σe : Set S → Set S}
    (h : RespectsFrame Φ Γ₁ σe) :
    RespectsFrame (Φ.mapHomeo ψ) (Γ₁.mapHomeo ψ) (fun e' ↦ ψ '' σe (ψ.symm '' e')) := by
  intro e' he' hb
  rw [Γ₁.mapHomeo_E ψ] at he'
  obtain ⟨e, he, rfl⟩ := he'
  dsimp only at hb ⊢
  rw [symm_image_image_u]
  obtain ⟨hb', hs'⟩ := h e he ((isBorder_image_u ψ).mp hb)
  refine ⟨(isBorder_image_u ψ).mpr hb', ?_⟩
  rw [Φ.mapHomeo_sides ψ]
  rintro _ ⟨s, hs, rfl⟩
  rw [image_subset_image_iff ψ.injective, image_subset_image_iff ψ.injective]
  exact hs' s hs

theorem immediatelyPrecedes_image_u {Θ : Set S} (f : Circle ≃ₜ Θ) {n : S} {A : Set S} :
    ImmediatelyPrecedes (f.trans (ψ.image Θ)) (ψ n) (ψ '' A) ↔ ImmediatelyPrecedes f n A := by
  have hcp : ∀ t : ℝ, cuffPoint (f.trans (ψ.image Θ)) t = ψ (cuffPoint f t) := fun _ ↦ rfl
  constructor
  · rintro ⟨t₀, t₁, h01, h02, hn, hA⟩
    rw [hcp] at hn
    refine ⟨t₀, t₁, h01, h02, ψ.injective hn, ?_⟩
    apply image_injective.2 ψ.injective
    rw [hA, ← image_comp]
    rfl
  · rintro ⟨t₀, t₁, h01, h02, rfl, rfl⟩
    refine ⟨t₀, t₁, h01, h02, hcp t₀, ?_⟩
    rw [← image_comp]
    rfl

theorem IsLinearInflation.mapHomeo {Γ₁ Γ₂ : Painting S} {σv : S → Set S} {σe : Set S → Set S}
    (h : IsLinearInflation Γ₁ Γ₂ σv σe) :
    IsLinearInflation (Γ₁.mapHomeo ψ) (Γ₂.mapHomeo ψ)
      (fun v' ↦ ψ '' σv (ψ.symm v')) (fun e' ↦ ψ '' σe (ψ.symm '' e')) where
  toIsInflation := h.toIsInflation.mapHomeo ψ
  borders_iff := by
    rw [Γ₁.mapHomeo_E ψ, cuffs_eq_image_u ψ]
    rintro _ ⟨e, he, rfl⟩ _ ⟨Θ, hΘ, rfl⟩
    dsimp only
    rw [symm_image_image_u, ← image_inter ψ.injective, ← image_inter ψ.injective,
      image_nonempty, image_nonempty]
    exact h.borders_iff e he Θ hΘ
  border_edge := by
    rw [Γ₂.mapHomeo_E ψ]
    rintro _ ⟨e', he', rfl⟩ hb hnot
    have hnot₀ : e' ∉ σe '' Γ₁.E := by
      rintro ⟨e, he, rfl⟩
      refine hnot ⟨ψ '' e, Γ₁.mapHomeo_mem ψ he, ?_⟩
      simp [symm_image_image_u]
    obtain ⟨v, hv, hsub⟩ := h.border_edge e' he' ((isBorder_image_u ψ).mp hb) hnot₀
    refine ⟨ψ v, mem_image_of_mem _ hv, ?_⟩
    rw [ψ.symm_apply_apply, image_tilde_u]
    exact image_mono hsub
  orientation := by
    rw [Γ₁.mapHomeo_E ψ, cuffs_eq_image_u ψ]
    rintro _ ⟨e, he, rfl⟩ _ ⟨Θ, hΘ, rfl⟩ hne f' n₁' n₂' hn₁' hn₂' hip
    dsimp only at hne hn₁' hn₂' hip ⊢
    simp only [symm_image_image_u, Γ₁.mapHomeo_γ ψ, Γ₂.mapHomeo_γ ψ,
      List.head?_map] at hn₁' hn₂' ⊢
    obtain ⟨n₁, hn₁, rfl⟩ := Option.map_eq_some_iff.mp hn₁'
    obtain ⟨n₂, hn₂, rfl⟩ := Option.map_eq_some_iff.mp hn₂'
    have hne₀ : (e ∩ Θ).Nonempty := by
      rw [← image_inter ψ.injective, image_nonempty] at hne
      exact hne
    let f : Circle ≃ₜ Θ := f'.trans (ψ.image Θ).symm
    have hf' : f' = f.trans (ψ.image Θ) := by
      ext x
      simp [f]
    rw [hf', immediatelyPrecedes_image_u] at hip ⊢
    exact h.orientation e he Θ hΘ hne₀ f n₁ n₂ hn₁ hn₂ hip

end Inflation

end GraphMinor.GM19

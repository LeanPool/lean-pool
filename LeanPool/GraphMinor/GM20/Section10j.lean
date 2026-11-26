/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10i
public import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.GM07.Defs

/-!
# Graph Minors XX, Section 10: paintings move along homeomorphisms

The set `𝒮` of (10.3) is finite only up to homeomorphism. So the proof needs that a homeomorphism
`ψ : Σ → Σ'` carries a shelled patchwork over `Σ` to one over `Σ'`. This file carries a painting and
its
3-connectivity. Every notion here is topological, and each lemma says that `ψ` respects one of them.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface

variable {S T : Type} [TopologicalSpace S] [TopologicalSpace T] (ψ : S ≃ₜ T)

theorem image_tilde (c : Set S) : tilde (ψ '' c) = ψ '' tilde c :=
  Surface.image_tilde_homeomorph ψ c

theorem image_arcComponentsIn (F : Set S) :
    arcComponentsIn (ψ '' F) = (fun c ↦ ψ '' c) '' arcComponentsIn F :=
  GM07.arcComponentsIn_image_homeo ψ F

theorem image_isClosedDisc {Δ : Set S} (h : IsClosedDisc Δ) : IsClosedDisc (ψ '' Δ) :=
  Surface.image_isClosedDisc_homeomorph ψ h

theorem image_isOArc {F : Set S} (h : IsOArc F) : IsOArc (ψ '' F) :=
  Surface.image_isOArc_homeomorph ψ h

theorem image_isLine {F : Set S} (h : IsLine F) : IsLine (ψ '' F) :=
  Surface.image_isLine_homeomorph ψ h

theorem image_discBd (Δ : Set S) : discBd (ψ '' Δ) = ψ '' discBd Δ :=
  Surface.image_discBd_homeomorph ψ Δ

theorem image_lineEnds_subset (F : Set S) : ψ '' lineEnds F ⊆ lineEnds (ψ '' F) :=
  Surface.image_lineEnds_subset_homeomorph ψ F

theorem image_lineEnds (F : Set S) : lineEnds (ψ '' F) = ψ '' lineEnds F :=
  Surface.image_lineEnds_homeomorph ψ F

theorem image_cuffs : cuffs T = (fun c ↦ ψ '' c) '' cuffs S :=
  Surface.image_cuffs_homeomorph ψ

theorem image_inOrderOn {Θ : Set S} {n₁ n₂ n₃ n₄ : S} (h : GM19.InOrderOn Θ n₁ n₂ n₃ n₄) :
    GM19.InOrderOn (ψ '' Θ) (ψ n₁) (ψ n₂) (ψ n₃) (ψ n₄) := by
  obtain ⟨f, t₁, t₂, t₃, t₄, h₁, h₂, h₃, h₄, rfl, rfl, rfl, rfl⟩ := h
  refine ⟨f.trans (ψ.image Θ), t₁, t₂, t₃, t₄, h₁, h₂, h₃, h₄, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem preimage_image_symm (F : Set T) : ψ '' (ψ.symm '' F) = F := by
  rw [← image_comp]
  simp

/-- The painting `ψ(Γ)` in `T`. -/
noncomputable def Painting.map (Γ : Painting S) : Painting T where
  U := ψ '' Γ.U
  N := ψ '' Γ.N
  γ c := (Γ.γ (ψ.symm '' c)).map ψ
  isClosed_U := ψ.isClosed_image.mpr Γ.isClosed_U
  N_subset := image_mono Γ.N_subset
  finite_N := Γ.finite_N.image _
  bd_subset := by
    rw [← image_bd_homeomorph ψ]
    exact image_mono Γ.bd_subset
  finite_cells := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    exact Γ.finite_cells.image _
  cell_disc := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    change IsClosedDisc (closure (ψ '' c))
    rw [← ψ.image_closure]
    exact image_isClosedDisc ψ (Γ.cell_disc c hc)
  cell_size := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    change (tilde (ψ '' c)).Finite ∧ _
    rw [image_tilde, Set.ncard_image_of_injective _ ψ.injective]
    exact ⟨(Γ.cell_size c hc).1.image _, (Γ.cell_size c hc).2⟩
  closure_inter := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    change closure (ψ '' c) ∩ ψ '' Γ.N = tilde (ψ '' c)
    rw [← ψ.image_closure, image_tilde, ← image_inter ψ.injective, Γ.closure_inter c hc]
  tilde_subset := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    change tilde (ψ '' c) ⊆ discBd (closure (ψ '' c))
    rw [← ψ.image_closure, image_tilde, image_discBd]
    exact image_mono (Γ.tilde_subset c hc)
  border_cell := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩ hb
    change ((ψ '' c) ∩ bd T).Nonempty at hb
    change (tilde (ψ '' c)).ncard = 2 ∧ IsLine (closure (ψ '' c) ∩ bd T) ∧
      lineEnds (closure (ψ '' c) ∩ bd T) = tilde (ψ '' c)
    rw [← image_bd_homeomorph ψ, ← image_inter ψ.injective] at hb
    have hb' := hb.of_image
    obtain ⟨h₁, h₂, h₃⟩ := Γ.border_cell c hc hb'
    rw [← ψ.image_closure, image_tilde, ← image_bd_homeomorph ψ, ← image_inter ψ.injective,
      Set.ncard_image_of_injective _ ψ.injective, image_lineEnds, h₃]
    exact ⟨h₁, image_isLine ψ h₂, rfl⟩
  γ_nodup := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    change ((Γ.γ (ψ.symm '' (ψ '' c))).map ψ).Nodup
    rw [show ψ.symm '' (ψ '' c) = c by simpa using preimage_image_symm ψ.symm c]
    exact (Γ.γ_nodup c hc).map ψ.injective
  γ_set := by
    rw [← image_sdiff ψ.injective, image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    change {n | n ∈ (Γ.γ (ψ.symm '' (ψ '' c))).map ψ} = tilde (ψ '' c)
    rw [show ψ.symm '' (ψ '' c) = c by simpa using preimage_image_symm ψ.symm c, image_tilde,
      ← Γ.γ_set c hc]
    ext x
    simp

theorem symm_image_image (F : Set S) : ψ.symm '' (ψ '' F) = F := by
  simpa using preimage_image_symm ψ.symm F

theorem Painting.map_C (Γ : Painting S) : (Γ.map ψ).C = (fun c ↦ ψ '' c) '' Γ.C := by
  change arcComponentsIn (ψ '' Γ.U \ ψ '' Γ.N) = _
  rw [← image_sdiff ψ.injective, image_arcComponentsIn]
  rfl

theorem image_cells_ncard (Γ : Painting S) (Δ : Set S) :
    {c ∈ (Γ.map ψ).C | c ⊆ ψ '' Δ}.ncard = {c ∈ Γ.C | c ⊆ Δ}.ncard := by
  have h : {c ∈ (Γ.map ψ).C | c ⊆ ψ '' Δ} = (fun c ↦ ψ '' c) '' {c ∈ Γ.C | c ⊆ Δ} := by
    rw [Painting.map_C]
    ext c
    constructor
    · rintro ⟨⟨c₀, hc₀, rfl⟩, h⟩
      exact ⟨c₀, ⟨hc₀, (image_subset_image_iff ψ.injective).mp h⟩, rfl⟩
    · rintro ⟨c₀, ⟨hc₀, h⟩, rfl⟩
      exact ⟨⟨c₀, hc₀, rfl⟩, image_mono h⟩
  rw [h, Set.ncard_image_of_injective _ (image_injective.mpr ψ.injective)]

theorem Painting.IsThreeConnected.map {Γ : Painting S} (h : Γ.IsThreeConnected) :
    (Γ.map ψ).IsThreeConnected := by
  have hU : ∀ F : Set S, ψ '' F ∩ (Γ.map ψ).U ⊆ (Γ.map ψ).N → F ∩ Γ.U ⊆ Γ.N := by
    intro F hF
    change ψ '' F ∩ ψ '' Γ.U ⊆ ψ '' Γ.N at hF
    rw [← image_inter ψ.injective, image_subset_image_iff ψ.injective] at hF
    exact hF
  have hN : ∀ F : Set S, (ψ '' F ∩ (Γ.map ψ).N).ncard = (F ∩ Γ.N).ncard := by
    intro F
    change (ψ '' F ∩ ψ '' Γ.N).ncard = _
    rw [← image_inter ψ.injective, Set.ncard_image_of_injective _ ψ.injective]
  have hΔ : ∀ F Δ : Set S, Δ ∩ Γ.N ⊆ F → ψ '' Δ ∩ (Γ.map ψ).N ⊆ ψ '' F := by
    intro F Δ hsub
    change ψ '' Δ ∩ ψ '' Γ.N ⊆ _
    rw [← image_inter ψ.injective]
    exact image_mono hsub
  refine ⟨fun F hF h₁ h₂ ↦ ?_, fun F hF h₁ h₂ h₃ ↦ ?_⟩
  · obtain ⟨F, rfl⟩ : ∃ G, F = ψ '' G := ⟨ψ.symm '' F, (preimage_image_symm ψ F).symm⟩
    have hG : IsOArc F := by simpa [symm_image_image] using image_isOArc ψ.symm hF
    obtain ⟨Δ, h₄, h₅, h₆, h₇⟩ := h.1 F hG (hU F h₁) (by rwa [hN] at h₂)
    exact ⟨ψ '' Δ, image_isClosedDisc ψ h₄, by rw [image_discBd, h₅],
      by rwa [image_cells_ncard], hΔ F Δ h₇⟩
  · obtain ⟨F, rfl⟩ : ∃ G, F = ψ '' G := ⟨ψ.symm '' F, (preimage_image_symm ψ F).symm⟩
    have hG : IsLine F := by simpa [symm_image_image] using image_isLine ψ.symm hF
    have hbd : F ∩ bd S = lineEnds F := by
      rw [← image_bd_homeomorph ψ, ← image_inter ψ.injective, image_lineEnds] at h₃
      exact image_injective.mpr ψ.injective h₃
    obtain ⟨Δ, h₄, h₅, h₆, h₇, h₈⟩ := h.2 F hG (hU F h₁) (by rwa [hN] at h₂) hbd
    refine ⟨ψ '' Δ, image_isClosedDisc ψ h₄, ?_, ?_, by rwa [image_cells_ncard], hΔ F Δ h₈⟩
    · rw [image_discBd]
      exact image_mono h₅
    · rw [image_discBd, ← image_bd_homeomorph ψ, ← image_union]
      exact image_mono h₆

end GraphMinor.GM20

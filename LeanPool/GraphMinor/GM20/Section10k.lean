/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10j

/-!
# Graph Minors XX, Section 10: hulls and shelled places move along homeomorphisms

Let `ψ : Σ → Σ'` be a homeomorphism that respects the gradings of `X = (Σ, ρ)` and `Y = (Σ', ρ')`.
This
file carries a hull in `X` to a hull in `Y`, and shows that shelled over `X` gives shelled over `Y`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM18

universe u v

variable {α : Type u} {β : Type v} {X Y : GradedSurface} (ψ : X.S ≃ₜ Y.S)

theorem mem_bd_image {x : X.S} : ψ x ∈ bd Y.S ↔ x ∈ bd X.S := by
  rw [← image_bd_homeomorph ψ]
  exact ψ.injective.mem_set_image

theorem isBorder_image {c : Set X.S} :
    Painting.IsBorder (ψ '' c) ↔ Painting.IsBorder c := by
  unfold Painting.IsBorder
  rw [← image_bd_homeomorph ψ, ← image_inter ψ.injective, image_nonempty]

variable {ψ} {G : Hypergraph α β} {Γ : Painting X.S}

/-- The hull in `Y` given by a hull in `X`. -/
def Hull.map (hρ : ∀ Θ ∈ cuffs X.S, Y.ρ (ψ '' Θ) = X.ρ Θ) (h : Hull Γ G) :
    Hull (X := Y) (Γ.map ψ) G where
  node n := h.node (ψ.symm n)
  cell c := h.cell (ψ.symm '' c)
  border n := h.border (ψ.symm n)
  node_injOn := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [Homeomorph.symm_apply_apply] at hab
    rw [h.node_injOn ha hb hab]
  node_mem := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using h.node_mem a ha
  cell_bijOn := by
    rw [Painting.map_C]
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      change h.cell (ψ.symm '' (ψ '' c)) ∈ _
      rw [symm_image_image]
      exact h.cell_bijOn.mapsTo hc
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      change h.cell (ψ.symm '' (ψ '' a)) = h.cell (ψ.symm '' (ψ '' b)) at hab
      rw [symm_image_image, symm_image_image] at hab
      rw [h.cell_bijOn.injOn ha hb hab]
    · intro f hf
      obtain ⟨c, hc, rfl⟩ := h.cell_bijOn.surjOn hf
      exact ⟨ψ '' c, ⟨c, hc, rfl⟩, by
        change h.cell (ψ.symm '' (ψ '' c)) = _
        rw [symm_image_image]⟩
  inc_iff := by
    rintro _ ⟨n, hn, rfl⟩ c' hc'
    rw [Painting.map_C] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    rw [image_tilde, ψ.injective.mem_set_image, symm_image_image, Homeomorph.symm_apply_apply]
    exact h.inc_iff n hn c hc
  border_subset := by
    rintro _ ⟨⟨n, hn, rfl⟩, hb⟩
    simpa using h.border_subset n ⟨hn, (mem_bd_image ψ).mp hb⟩
  border_disjoint := by
    rintro _ ⟨⟨n, hn, rfl⟩, hb⟩
    have : (fun n ↦ h.node (ψ.symm n)) '' (ψ '' Γ.N) = h.node '' Γ.N := by
      rw [← image_comp]
      exact image_congr fun x _ ↦ by simp
    change Disjoint (h.border (ψ.symm (ψ n))) ((fun n ↦ h.node (ψ.symm n)) '' (ψ '' Γ.N))
    rw [this, Homeomorph.symm_apply_apply]
    exact h.border_disjoint n ⟨hn, (mem_bd_image ψ).mp hb⟩
  border_ncard := by
    intro Θ' hΘ' _ hn
    rw [image_cuffs ψ] at hΘ'
    obtain ⟨Θ, hΘ, rfl⟩ := hΘ'
    obtain ⟨⟨n, hn₁, rfl⟩, hn₂⟩ := hn
    have hn₃ : n ∈ Θ := ψ.injective.mem_set_image.mp hn₂
    rw [Homeomorph.symm_apply_apply, hρ Θ hΘ]
    exact h.border_ncard Θ hΘ n ⟨hn₁, hn₃⟩
  border_cuffs := by
    intro Θ₁' h₁' Θ₂' h₂' hne _ hn₁ _ hn₂
    rw [image_cuffs ψ] at h₁' h₂'
    obtain ⟨Θ₁, h₁, rfl⟩ := h₁'
    obtain ⟨Θ₂, h₂, rfl⟩ := h₂'
    obtain ⟨⟨a, ha, rfl⟩, ha'⟩ := hn₁
    obtain ⟨⟨b, hb, rfl⟩, hb'⟩ := hn₂
    simp only [Homeomorph.symm_apply_apply]
    exact h.border_cuffs Θ₁ h₁ Θ₂ h₂ (fun e ↦ hne (by rw [e])) a
      ⟨ha, ψ.injective.mem_set_image.mp ha'⟩ b ⟨hb, ψ.injective.mem_set_image.mp hb'⟩
  vertexSet_eq := by
    rw [h.vertexSet_eq]
    congr 1
    · change h.node '' Γ.N = (fun n ↦ h.node (ψ.symm n)) '' (ψ '' Γ.N)
      rw [← image_comp]
      exact image_congr fun x _ ↦ by simp
    · ext v
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨n, ⟨h₁, h₂⟩, hv⟩
        exact ⟨ψ n, ⟨⟨n, h₁, rfl⟩, (mem_bd_image ψ).mpr h₂⟩, by simpa using hv⟩
      · rintro ⟨_, ⟨⟨n, h₁, rfl⟩, h₂⟩, hv⟩
        exact ⟨n, ⟨h₁, (mem_bd_image ψ).mp h₂⟩, by simpa using hv⟩
  ends_internal := by
    intro c' hc' hb
    rw [Painting.map_C] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    rw [symm_image_image, h.ends_internal c hc fun h' ↦ hb ((isBorder_image ψ).mpr h'),
      image_tilde, ← image_comp]
    exact image_congr fun x _ ↦ by simp
  ends_border := by
    intro c' hc' hb
    rw [Painting.map_C] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    rw [symm_image_image, h.ends_border c hc ((isBorder_image ψ).mp hb), image_tilde,
      ← image_comp]
    congr 1
    · exact image_congr fun x _ ↦ by simp
    · ext v
      simp only [mem_iUnion, exists_prop, mem_image]
      constructor
      · rintro ⟨n, h₁, hv⟩
        exact ⟨ψ n, ⟨n, h₁, rfl⟩, by simpa using hv⟩
      · rintro ⟨_, ⟨n, h₁, rfl⟩, hv⟩
        exact ⟨n, h₁, by simpa using hv⟩
  border_order := by
    intro Θ' hΘ' _ h₁ _ h₂ _ h₃ _ h₄ hord
    rw [image_cuffs ψ] at hΘ'
    obtain ⟨Θ, hΘ, rfl⟩ := hΘ'
    obtain ⟨⟨a, ha, rfl⟩, ha'⟩ := h₁
    obtain ⟨⟨b, hb, rfl⟩, hb'⟩ := h₂
    obtain ⟨⟨c, hc, rfl⟩, hc'⟩ := h₃
    obtain ⟨⟨d, hd, rfl⟩, hd'⟩ := h₄
    have := image_inOrderOn ψ.symm hord
    simp only [symm_image_image, Homeomorph.symm_apply_apply] at this ⊢
    exact h.border_order Θ hΘ a ⟨ha, ψ.injective.mem_set_image.mp ha'⟩ b
      ⟨hb, ψ.injective.mem_set_image.mp hb'⟩ c ⟨hc, ψ.injective.mem_set_image.mp hc'⟩ d
      ⟨hd, ψ.injective.mem_set_image.mp hd'⟩ this

/-- Shelled over `X` gives shelled over `Y`, for a homeomorphism that respects the gradings. -/
theorem IsShelled.map {P : UnlabeledPatchwork α β} {ℒ : Set (RootedHypergraph α β)}
    (hρ : ∀ Θ ∈ cuffs X.S, Y.ρ (ψ '' Θ) = X.ρ Θ) (hS : IsShelled X P ℒ) : IsShelled Y P ℒ := by
  obtain ⟨hfine, e, P', Γ, h, hheart, hE, h₃, hint, hbor⟩ := hS
  refine ⟨hfine, e, P', Γ.map ψ, h.map hρ, hheart, hE, h₃.map ψ, ?_, ?_⟩
  · intro c' hc' A hA hcell hb
    rw [Painting.map_C] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    change h.cell (ψ.symm '' (ψ '' c)) = _ at hcell
    rw [symm_image_image] at hcell
    obtain ⟨h₁, h₂⟩ := hint c hc A hA hcell fun h' ↦ hb ((isBorder_image ψ).mpr h')
    have himg : (fun n ↦ h.node (ψ.symm n)) '' tilde (ψ '' c) = h.node '' tilde c := by
      rw [image_tilde, ← image_comp]
      exact image_congr fun x _ ↦ by simp
    refine ⟨?_, ?_⟩
    · change A.roots = ((Γ.γ (ψ.symm '' (ψ '' c))).map ψ).map fun n ↦ h.node (ψ.symm n)
      rw [symm_image_image, List.map_map, h₁]
      exact (List.map_congr_left fun x _ ↦ by simp).symm
    · intro K hK hverts
      change GM04.IsGrouping ((fun n ↦ h.node (ψ.symm n)) '' tilde (ψ '' c)) K at hK
      change K.verts = (fun n ↦ h.node (ψ.symm n)) '' tilde (ψ '' c) at hverts
      rw [himg] at hK hverts
      exact h₂ K hK hverts
  · intro c' hc' A hA hcell Θ' hΘ' hne n₁' h₁' n₂' h₂' hn
    rw [Painting.map_C] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    rw [image_cuffs ψ] at hΘ'
    obtain ⟨Θ, hΘ, rfl⟩ := hΘ'
    change h.cell (ψ.symm '' (ψ '' c)) = _ at hcell
    rw [symm_image_image] at hcell
    rw [image_tilde] at h₁' h₂'
    obtain ⟨n₁, h₁, rfl⟩ := h₁'
    obtain ⟨n₂, h₂, rfl⟩ := h₂'
    rw [← image_inter ψ.injective, image_nonempty] at hne
    obtain ⟨L, h₃', h₄, h₅⟩ := hbor c hc A hA hcell Θ hΘ hne n₁ h₁ n₂ h₂
      (fun e' ↦ hn (by rw [e']))
    simp only [Hull.map, Homeomorph.symm_apply_apply]
    rw [hρ Θ hΘ]
    rw [ψ.symm_apply_apply n₁, ψ.symm_apply_apply n₂]
    refine ⟨L, h₃', h₄, ?_⟩
    rcases h₅ with h₅ | ⟨c₀, hc₀, hb, h₆, h₇⟩
    · exact Or.inl h₅
    · refine Or.inr ⟨ψ '' c₀, ?_, fun h' ↦ hb ((isBorder_image ψ).mp h'), ?_, ?_⟩
      · rw [Painting.map_C]
        exact ⟨c₀, hc₀, rfl⟩
      · rw [image_tilde]
        exact ⟨n₁, h₆, rfl⟩
      · rw [image_tilde]
        exact ⟨n₂, h₇, rfl⟩

end GraphMinor.GM20

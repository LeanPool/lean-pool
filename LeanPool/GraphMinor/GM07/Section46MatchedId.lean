/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Matched
import LeanPool.GraphMinor.GM07.Section3
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Defs

/-!
# Isolated vertices and homotopy

In VII (4.6), page 227, `H₄` is `H₃` with the set `M₂` added back as
isolated vertices. Isolated vertices are not on any path to another
vertex, so adding the same isolated vertices to two homotopic forests
keeps them homotopic. `IsMatched.forestsHomotopic` gives the opposite
direction. Here is this one, for the identity map.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {X : Type u} [TopologicalSpace X]

theorem end_mem_support {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    b ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.support]
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

theorem isMatched_id {A A' : Drawing X} {B : Set X} (hsub : B ⊆ A.V)
    (hoff : ∀ e ∈ A.E, Disjoint (closure e) B) (hU : A.U \ B = A'.U) (hV : A.V \ B = A'.V)
    (hE : A'.E = A.E) : IsMatched A A' id B where
  cont := continuous_id
  inj := Function.injective_id.injOn
  sub := hsub
  off := hoff
  image_U := by rw [image_id, hU]
  image_V := by rw [image_id, hV]
  image_E := by
    have : image (id : X → X) = id := by
      funext s
      exact image_id s
    rw [this, image_id, hE]

variable [CompactSpace X] [T2Space X] [Nonempty X]

/-- Adding the same isolated vertices to two homotopic forests keeps them homotopic. -/
theorem ForestsHomotopic.of_matched_id {Γ₁ Γ₂ Γ₁' Γ₂' : Drawing X} {B : Set X}
    (m₁ : IsMatched Γ₁ Γ₁' id B) (m₂ : IsMatched Γ₂ Γ₂' id B) (h : ForestsHomotopic Γ₁' Γ₂')
    (hp₁ : Γ₁.IsProper) (hp₂ : Γ₂.IsProper) (hV : Γ₁.V ∩ bd X = Γ₂.V ∩ bd X) :
    ForestsHomotopic Γ₁ Γ₂ := by
  obtain ⟨-, -, f₁, f₂, -, hpaths⟩ := h
  have hforget : ∀ {Γ Γ' : Drawing X}, IsMatched Γ Γ' id B → ∀ {s t : X}, s ≠ t → s ∈ Γ.V →
      GraphWalk Γ.toGraph s t → s ∉ B ∧ t ∉ B := by
    intro Γ Γ' m s t hne hs W
    have hsB : s ∉ B := by
      intro hsB
      cases W with
      | nil _ => exact hne rfl
      | cons hl _ =>
        have hmem : s ∈ closure _ := (hl.2.2.2.symm.subset (by simp)).1
        exact disjoint_left.mp (m.off _ hl.1) hmem hsB
    obtain ⟨-, -, -, h3, -⟩ := m.carry.walk W ⟨hs, hsB⟩ s t rfl rfl
    have ht : t ∈ W.support := end_mem_support W
    exact ⟨hsB, (h3 t ht).2⟩
  have hdown : ∀ {Γ Γ' : Drawing X}, IsMatched Γ Γ' id B → ∀ {s t : X}, s ∈ Γ.V \ B →
      ∀ (W : GraphWalk Γ.toGraph s t), W.IsSimple → ∀ φ : Curve X, CurveTracesWalk Γ φ W →
        ∃ W' : GraphWalk Γ'.toGraph s t, W'.IsSimple ∧ CurveTracesWalk Γ' φ W' := by
    intro Γ Γ' m s t hs W hW φ hφ
    obtain ⟨Q, h1, -, h3, h4⟩ := m.carry.walk W hs s t rfl rfl
    obtain ⟨c, hc, hv⟩ := h4 φ hφ
    have hceq : c = φ := ContinuousMap.ext hv
    subst hceq
    refine ⟨Q, ?_, hc⟩
    rw [GraphWalk.IsSimple, h1, List.map_id]
    exact hW
  have hup : ∀ {Γ Γ' : Drawing X}, IsMatched Γ Γ' id B → ∀ {s t : X}, s ∈ Γ.V \ B →
      ∀ (W : GraphWalk Γ'.toGraph s t), W.IsSimple →
        ∃ W' : GraphWalk Γ.toGraph s t, W'.IsSimple := by
    intro Γ Γ' m s t hs W hW
    obtain ⟨ψ, hl, -, hc⟩ := m.exists_inverse
    have hsV : s ∈ Γ'.V := m.image_V ▸ ⟨s, hs, rfl⟩
    have hUsupp : ∀ z ∈ W.support, z ∈ Γ.U := by
      intro z hz
      have hzV : z ∈ Γ'.V := W.mem_vertexSet_of_mem_support hz
      rw [← m.image_V] at hzV
      obtain ⟨y, hy, rfl⟩ := hzV
      exact Γ.V_subset_U hy.1
    have htU : t ∈ Γ.U := hUsupp t (end_mem_support W)
    obtain ⟨Q, h1, -, h3, -⟩ := hc.walk W hsV s t (hl s (Γ.V_subset_U hs.1)) (hl t htU)
    refine ⟨Q, ?_⟩
    have hmap : W.support.map ψ = W.support.map id :=
      List.map_congr_left fun z hz => hl z (hUsupp z hz)
    rw [GraphWalk.IsSimple, h1, hmap, List.map_id]
    exact hW
  refine ⟨hp₁, hp₂, m₁.isGraphForest_iff.mpr f₁, m₂.isGraphForest_iff.mpr f₂, hV,
    fun s hs t ht hne => ?_⟩
  have hs₂ : s ∈ Γ₂.V := (hV ▸ hs : s ∈ Γ₂.V ∩ bd X).1
  have ht₂ : t ∈ Γ₂.V := (hV ▸ ht : t ∈ Γ₂.V ∩ bd X).1
  by_cases hsB : s ∈ B
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨P, -⟩
      exact ((hforget m₁ hne hs.1 P).1 hsB).elim
    · rintro ⟨P, -⟩
      exact ((hforget m₂ hne hs₂ P).1 hsB).elim
    · intro P₁
      exact ((hforget m₁ hne hs.1 P₁).1 hsB).elim
  by_cases htB : t ∈ B
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨P, -⟩
      exact ((hforget m₁ hne hs.1 P).2 htB).elim
    · rintro ⟨P, -⟩
      exact ((hforget m₂ hne hs₂ P).2 htB).elim
    · intro P₁
      exact ((hforget m₁ hne hs.1 P₁).2 htB).elim
  have hs₁' : s ∈ Γ₁'.V ∩ bd X := ⟨m₁.image_V ▸ ⟨s, ⟨hs.1, hsB⟩, rfl⟩, hs.2⟩
  have ht₁' : t ∈ Γ₁'.V ∩ bd X := ⟨m₁.image_V ▸ ⟨t, ⟨ht.1, htB⟩, rfl⟩, ht.2⟩
  obtain ⟨hiff, hhom⟩ := hpaths s hs₁' t ht₁' hne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, hP⟩
    obtain ⟨Q, hQ⟩ := exists_curveTracesWalk P
    obtain ⟨W, hW, -⟩ := hdown m₁ ⟨hs.1, hsB⟩ P hP Q hQ
    exact hup m₂ ⟨hs₂, hsB⟩ _ (hiff.mp ⟨W, hW⟩).choose_spec
  · rintro ⟨P, hP⟩
    obtain ⟨Q, hQ⟩ := exists_curveTracesWalk P
    obtain ⟨W, hW, -⟩ := hdown m₂ ⟨hs₂, hsB⟩ P hP Q hQ
    exact hup m₁ ⟨hs.1, hsB⟩ _ (hiff.mpr ⟨W, hW⟩).choose_spec
  · intro P₁ P₂ φ₁ φ₂ h₁ h₂ t₁ t₂
    obtain ⟨W₁, hW₁, c₁⟩ := hdown m₁ ⟨hs.1, hsB⟩ P₁ h₁ φ₁ t₁
    obtain ⟨W₂, hW₂, c₂⟩ := hdown m₂ ⟨hs₂, hsB⟩ P₂ h₂ φ₂ t₂
    exact hhom W₁ W₂ φ₁ φ₂ hW₁ hW₂ c₁ c₂

end GraphMinor.GM07

/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card

/-!
# Auxiliary lemmas for stable matching

* `argmin_filter_eq_some_iff`, `argmin_filter_eq_none_iff`: `List.argmin` of an injective map
  `f : α → ℕ` over the elements of a finite type satisfying a predicate picks the unique
  minimiser;
* `exists_eq_some_of_injOn`: if partial maps `f` from `s` into `t` and `g` from `t` into `s`
  are injective, then `f` maps `s` onto `t` (a counting argument used for the lattice of stable
  matchings and for the incentive theorems).
-/

@[expose] public section

namespace LeanPool.StableMatching

section Argmin

variable {α : Type*} [Fintype α] {f : α → ℕ} (p : α → Prop) [DecidablePred p]

theorem argmin_filter_eq_none_iff :
    List.argmin f (Finset.univ.filter p).toList = none ↔ ∀ b, ¬ p b := by
  simp [List.argmin_eq_none, Finset.filter_eq_empty_iff]

theorem argmin_filter_eq_some_iff (hf : Function.Injective f) {a : α} :
    List.argmin f (Finset.univ.filter p).toList = some a ↔ p a ∧ ∀ b, p b → f a ≤ f b := by
  constructor
  · intro h
    have ha := List.argmin_mem h
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨ha, fun b hb ↦ List.le_of_mem_argmin (by simpa using hb) h⟩
  · rintro ⟨ha, hmin⟩
    cases h : List.argmin f (Finset.univ.filter p).toList with
    | none => exact absurd ha ((argmin_filter_eq_none_iff p).1 h a)
    | some a' =>
      have ha' := List.argmin_mem h
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
      have h1 := List.le_of_mem_argmin (by simpa using ha) h
      exact congrArg some (hf (le_antisymm h1 (hmin a' ha')))

end Argmin

section Counting

variable {α β : Type*} {s : Finset α} {t : Finset β} {f : α → Option β}

/-- A partial map sending a finite set injectively into another does not increase the
cardinality. -/
theorem card_le_card_of_injOn (hf : ∀ a ∈ s, ∃ b ∈ t, f a = some b)
    (hfi : ∀ a₁ a₂ b, f a₁ = some b → f a₂ = some b → a₁ = a₂) : s.card ≤ t.card := by
  classical
  have h1 : (s.image f).card = s.card := by
    refine Finset.card_image_of_injOn fun a₁ ha₁ a₂ _ h ↦ ?_
    obtain ⟨b, -, hb⟩ := hf a₁ ha₁
    exact hfi a₁ a₂ b hb (h ▸ hb)
  have h2 : s.image f ⊆ t.image some := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, hab⟩ := hf a ha
    exact Finset.mem_image.2 ⟨b, hb, hab.symm⟩
  rw [← h1, ← Finset.card_image_of_injective t (Option.some_injective β)]
  exact Finset.card_le_card h2

/-- If a partial map `f` sends `s` injectively into `t` and a partial map sends `t` injectively
into `s`, then `f` maps `s` onto `t`. -/
theorem exists_eq_some_of_injOn {g : β → Option α} (hf : ∀ a ∈ s, ∃ b ∈ t, f a = some b)
    (hfi : ∀ a₁ a₂ b, f a₁ = some b → f a₂ = some b → a₁ = a₂)
    (hg : ∀ b ∈ t, ∃ a ∈ s, g b = some a)
    (hgi : ∀ b₁ b₂ a, g b₁ = some a → g b₂ = some a → b₁ = b₂) :
    ∀ b ∈ t, ∃ a ∈ s, f a = some b := by
  classical
  have h1 : (s.image f).card = s.card := by
    refine Finset.card_image_of_injOn fun a₁ ha₁ a₂ _ h ↦ ?_
    obtain ⟨b, -, hb⟩ := hf a₁ ha₁
    exact hfi a₁ a₂ b hb (h ▸ hb)
  have h2 : s.image f ⊆ t.image some := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, hab⟩ := hf a ha
    exact Finset.mem_image.2 ⟨b, hb, hab.symm⟩
  have h3 : s.image f = t.image some := by
    refine Finset.eq_of_subset_of_card_le h2 ?_
    rw [h1, Finset.card_image_of_injective t (Option.some_injective β)]
    exact card_le_card_of_injOn hg hgi
  intro b hb
  have : some b ∈ s.image f := h3 ▸ Finset.mem_image_of_mem some hb
  obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 this
  exact ⟨a, ha, hab⟩

end Counting

end LeanPool.StableMatching

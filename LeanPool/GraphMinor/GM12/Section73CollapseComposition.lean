/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Function

/-!
# Composing consecutive interval contractions

To contract an arc in XII (7.3), page 261, cover its strip axis by
short intervals and collapse them from the last to the first. If a
map collapses `A` to a point of `B` and fixes `B`, a subsequent
collapse of `B` contracts exactly `A ∪ B`. This file proves that
fibre calculation without topological assumptions.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Successive collapses identify exactly the union of their
collapsed sets when the first map fixes the second set. This is the
composition rule for the arc contractions in XII (7.3). -/
theorem collapse_composition_fibres {X : Type*} {f g : X → X} {A B : Set X} {a : X}
    (hf : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hg : ∀ x y, g x = g y ↔ x = y ∨ (x ∈ B ∧ y ∈ B))
    (hA : ∀ x ∈ A, f x = a) (hB : ∀ x ∈ B, f x = x) (haB : a ∈ B) :
    (∀ x ∈ A ∪ B, g (f x) = g a) ∧
      (∀ x y, g (f x) = g (f y) ↔ x = y ∨ (x ∈ A ∪ B ∧ y ∈ A ∪ B)) := by
  have hconstant : ∀ x ∈ A ∪ B, g (f x) = g a := by
    intro x hx
    rcases hx with hxA | hxB
    · rw [hA x hxA]
    · rw [hB x hxB]
      exact (hg x a).mpr (Or.inr ⟨hxB, haB⟩)
  have hpre : ∀ x, f x ∈ B → x ∈ A ∪ B := by
    intro x hx
    have heq : f x = f (f x) := (hB (f x) hx).symm
    rcases (hf x (f x)).mp heq with hxx | hAx
    · exact Or.inr (hxx ▸ hx)
    · exact Or.inl hAx.1
  refine ⟨hconstant, ?_⟩
  intro x y
  constructor
  · intro heq
    rcases (hg (f x) (f y)).mp heq with hxy | hBxy
    · rcases (hf x y).mp hxy with hxy | hAxy
      · exact Or.inl hxy
      · exact Or.inr ⟨Or.inl hAxy.1, Or.inl hAxy.2⟩
    · exact Or.inr ⟨hpre x hBxy.1, hpre y hBxy.2⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · exact (hconstant x hx).trans (hconstant y hy).symm

/-- Collapsing the image of a second set composes with an earlier
collapse to identify exactly their union, provided the earlier
collapsed value belongs to that image. This handles radial-star
contractions in XII (7.3) when the second arc has moved. -/
theorem collapse_image_composition_fibres
    {X : Type*} {f g : X → X} {A B : Set X} {a : X}
    (hf : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hg : ∀ x y, g x = g y ↔ x = y ∨ (x ∈ f '' B ∧ y ∈ f '' B))
    (hA : ∀ x ∈ A, f x = a) (haB : a ∈ f '' B) :
    (∀ x ∈ A ∪ B, g (f x) = g a) ∧
      (∀ x y, g (f x) = g (f y) ↔ x = y ∨ (x ∈ A ∪ B ∧ y ∈ A ∪ B)) := by
  have hconstant : ∀ x ∈ A ∪ B, g (f x) = g a := by
    intro x hx
    rcases hx with hxA | hxB
    · rw [hA x hxA]
    · exact (hg (f x) a).mpr (Or.inr ⟨mem_image_of_mem f hxB, haB⟩)
  have hpre : ∀ x, f x ∈ f '' B → x ∈ A ∪ B := by
    rintro x ⟨z, hz, hzx⟩
    rcases (hf x z).mp hzx.symm with hxz | hxA
    · exact Or.inr (hxz ▸ hz)
    · exact Or.inl hxA.1
  refine ⟨hconstant, ?_⟩
  intro x y
  constructor
  · intro heq
    rcases (hg (f x) (f y)).mp heq with hxy | hBxy
    · rcases (hf x y).mp hxy with hxy | hAxy
      · exact Or.inl hxy
      · exact Or.inr ⟨Or.inl hAxy.1, Or.inl hAxy.2⟩
    · exact Or.inr ⟨hpre x hBxy.1, hpre y hBxy.2⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · exact (hconstant x hx).trans (hconstant y hy).symm

/-- A collapse supported in a region preserves that region and
leaves every image point outside it unchanged. This records the
unchanged part of the radial drawing in XII (7.3), page 261. -/
theorem collapse_image_diff_eq
    {X : Type*} {f : X → X} {A R : Set X}
    (hf : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hfix : ∀ x ∉ R, f x = x) (hAR : A ⊆ R) :
    (∀ x, f x ∈ R ↔ x ∈ R) ∧ (∀ B : Set X, (f '' B) \ R = B \ R) := by
  have hmem : ∀ x, f x ∈ R ↔ x ∈ R := by
    intro x
    constructor
    · intro hfx
      by_contra hxn
      exact hxn (hfix x hxn ▸ hfx)
    · intro hx
      by_contra hfxn
      have heq : f x = f (f x) := (hfix (f x) hfxn).symm
      rcases (hf x (f x)).mp heq with hxx | hxA
      · exact hfxn (hxx ▸ hx)
      · exact hfxn (hAR hxA.2)
  refine ⟨hmem, ?_⟩
  intro B
  apply Subset.antisymm
  · rintro y ⟨⟨x, hxB, hxy⟩, hyn⟩
    have hxn : x ∉ R := fun hx => hyn (hxy ▸ (hmem x).mpr hx)
    have hxy' : x = y := (hfix x hxn).symm.trans hxy
    exact ⟨hxy' ▸ hxB, hyn⟩
  · rintro x ⟨hxB, hxn⟩
    exact ⟨⟨x, hxB, hfix x hxn⟩, hxn⟩

end GraphMinor.GM12

/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Data.Option.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace Option

open _root_.Option

variable {α : Type u}

/-- The lifted subset relation on optional values. -/
inductive IsSubsetOf : Option α → Option α → Prop
  | none : IsSubsetOf none o
  | some (a : α) : IsSubsetOf (some a) (some a)

instance instHasSubsetOptionModel : HasSubset (Option α) :=
  ⟨IsSubsetOf⟩

@[simp]
lemma none_subset (o : Option α) : none ⊆ o :=
  IsSubsetOf.none

@[simp]
lemma some_subset_some_self (a : α) : some a ⊆ some a :=
  IsSubsetOf.some a

@[simp]
lemma subset_none_iff (o : Option α) : o ⊆ none ↔ o = none :=
  by
  cases o
  · simp
  · simp only [reduceCtorEq, iff_false]; rintro ⟨⟩

@[simp]
lemma some_subset_some {a b : α} : some a ⊆ some b ↔ a = b :=
  by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact IsSubsetOf.some a

lemma subset_iff (o₁ o₂ : Option α) : o₁ ⊆ o₂ ↔ ∀ a, a ∈ o₁ → a ∈ o₂ :=
  by
  cases o₁
  · simp
  · cases o₂
    · simp
    · simp; grind

end Option

end

end PointwiseComposition

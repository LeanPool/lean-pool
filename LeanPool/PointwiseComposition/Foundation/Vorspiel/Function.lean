/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Data.Fintype.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace Function

open _root_.Function

variable {α : Type u} {β : Type v}

/-- The fun Eq On construction in `Function`. -/
def funEqOn (φ : α → Prop) (f g : α → β) : Prop :=
  ∀ a, φ a → f a = g a

lemma funEqOn.of_subset {φ ψ : α → Prop} {f g : α → β} (e : funEqOn φ f g)
    (h : ∀ a, ψ a → φ a) : funEqOn ψ f g := by intro a ha; exact e a (h a ha)

end Function

end

end PointwiseComposition

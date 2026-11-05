/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.QuotientObstruction

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Composition on program quotients and its obstruction.
-/

@[expose] public section

namespace FailureOfComposition

universe u

/-- A binary operation descends to a quotient exactly when it preserves the
equivalence relation in both arguments. -/
theorem quotient_composition_exists_iff {A : Type u} (s : Setoid A) (comp : A → A → A) :
    (∃ C : Quotient s → Quotient s → Quotient s,
        ∀ a b, C (Quotient.mk s a) (Quotient.mk s b) = Quotient.mk s (comp a b)) ↔
      (∀ a a' b b', s.r a a' → s.r b b' → s.r (comp a b) (comp a' b')) :=
  by
  constructor
  · rintro ⟨C, hC⟩ a a' b b' ha hb
    apply Quotient.exact
    calc
      Quotient.mk s (comp a b) = C (Quotient.mk s a) (Quotient.mk s b) := (hC a b).symm
      _ = C (Quotient.mk s a') (Quotient.mk s b') := by
        rw [Quotient.sound ha, Quotient.sound hb]
      _ = Quotient.mk s (comp a' b') := hC a' b'
  · intro h
    refine
      ⟨Quotient.lift₂ (fun a b => Quotient.mk s (comp a b))
          (fun a b a' b' ha hb => Quotient.sound (h a a' b b' ha hb)),
        ?_⟩
    intro a b
    rfl

end FailureOfComposition

end

end PointwiseComposition

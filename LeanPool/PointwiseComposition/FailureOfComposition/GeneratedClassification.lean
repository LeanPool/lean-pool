/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedExtensionality
public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedQuotient

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Classification of the generated composition congruence.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace GeneratedCongruence

open ProofSearch PiOneCharacterization

/-- In the Sigma-one sound case the generated congruence is exactly
extensional equality. The containment hypothesis is fully discharged. -/
theorem generated_iff_extensional_of_sound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : SigmaOneSound T) (F G : FunctionalGraph) : Rel T F G ↔ Extensional F.val G.val :=
  rel_iff_extensional_of_sigmaOneSound T (extensional_implies_generated T) hT F G

/-- Failure of Sigma-one soundness makes every two functional graphs
equivalent in the generated congruence. -/
theorem generated_universal_of_not_sound (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (hT : ¬SigmaOneSound T)
    (F G : FunctionalGraph) : Rel T F G :=
  collapse_of_not_sigmaOneSound T (extensional_implies_generated T) hT F G

/-- The generated-congruence dichotomy, with no consistency or effective
presentation assumption on T. -/
theorem classification (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    (SigmaOneSound T → ∀ F G : FunctionalGraph, Rel T F G ↔ Extensional F.val G.val) ∧
      (¬SigmaOneSound T → ∀ F G : FunctionalGraph, Rel T F G) :=
  ⟨generated_iff_extensional_of_sound T, generated_universal_of_not_sound T⟩

theorem generated_iff_extensional_or_unsound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (F G : FunctionalGraph) : Rel T F G ↔ Extensional F.val G.val ∨ ¬SigmaOneSound T := by
  classical
  by_cases hT : SigmaOneSound T
  · simpa only [hT, not_true_eq_false, or_false] using
      generated_iff_extensional_of_sound T hT F G
  · exact ⟨fun _ => Or.inr hT, fun _ => generated_universal_of_not_sound T hT F G⟩

theorem quotient_subsingleton_of_not_sound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : ¬SigmaOneSound T) : Subsingleton (QuotientGraph T) :=
  quotient_subsingleton_of_universal T (generated_universal_of_not_sound T hT)

/-- The quotient monoid has one element exactly in the unsound case. -/
theorem quotient_subsingleton_iff_not_sound (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    Subsingleton (QuotientGraph T) ↔ ¬SigmaOneSound T :=
  by
  constructor
  · intro hsub hT
    have he : quotientMk T identityGraph = quotientMk T emptyGraph := hsub.allEq _ _
    have hr : Rel T identityGraph emptyGraph := Quotient.exact he
    have hx := (generated_iff_extensional_of_sound T hT identityGraph emptyGraph).mp hr
    have hf := (hx 0 0).mp (by simp [identityGraph])
    simp [emptyGraph] at hf
  · exact quotient_subsingleton_of_not_sound T

end GeneratedCongruence
end FailureOfComposition

end

end PointwiseComposition

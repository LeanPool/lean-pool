/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedIndexClassification
public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedIndexQuotient
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteGodel

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Generated-congruence classification for the concrete evaluator indices.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteIndices

noncomputable section

/-- The intersection of all composition congruences containing pointwise
provability for the actual natural-number program indices. -/
def GeneratedRel (T : ArithmeticTheory) : ℕ → ℕ → Prop :=
  CompositionClosure.Generated canonicalPartrecCompIndex (PointwiseIndex T)

/-- The generated Setoid construction in `FailureOfComposition.ConcreteIndices`. -/
def generatedSetoid (T : ArithmeticTheory) : Setoid ℕ :=
  CompositionClosure.setoid canonicalPartrecCompIndex (PointwiseIndex T)

/-- Equal partial functions are always identified by the generated congruence. -/
theorem extensional_implies_generated (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (e d : ℕ)
    (h : Kleene.eval e = Kleene.eval d) : GeneratedRel T e d :=
  ProgramIndices.extensional_implies_generated ConcreteEvaluator.arithmetization T e d h

theorem generated_iff_extensional_of_sound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : GeneratedCongruence.SigmaOneSound T) (e d : ℕ) :
    GeneratedRel T e d ↔ Kleene.eval e = Kleene.eval d :=
  ProgramIndices.generated_iff_extensional_of_sound ConcreteEvaluator.arithmetization T hT e d

theorem generated_universal_of_not_sound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : ¬GeneratedCongruence.SigmaOneSound T) (e d : ℕ) : GeneratedRel T e d :=
  ProgramIndices.generated_universal_of_not_sound ConcreteEvaluator.arithmetization T hT e d

/-- The generated-congruence theorem for every extension of PA. There is no
consistency, enumerability, or supplied realization hypothesis. -/
theorem generated_congruence_classification (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    (GeneratedCongruence.SigmaOneSound T →
        ∀ e d : ℕ, GeneratedRel T e d ↔ Kleene.eval e = Kleene.eval d) ∧
      (¬GeneratedCongruence.SigmaOneSound T → ∀ e d : ℕ, GeneratedRel T e d) :=
  ⟨generated_iff_extensional_of_sound T, generated_universal_of_not_sound T⟩

theorem generated_iff_extensional_or_unsound (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (e d : ℕ) :
    GeneratedRel T e d ↔ Kleene.eval e = Kleene.eval d ∨ ¬GeneratedCongruence.SigmaOneSound T :=
  ProgramIndices.generated_iff_extensional_or_unsound ConcreteEvaluator.arithmetization T e d

/-- In particular, closing PA-pointwise equality under composition gives
exactly extensional equality. -/
theorem pa_generated_iff_extensional (e d : ℕ) :
    GeneratedRel 𝐏𝐀 e d ↔ Kleene.eval e = Kleene.eval d :=
  by
  apply generated_iff_extensional_of_sound 𝐏𝐀
  intro σ _ hp
  exact consequence_iff.mp (Theory.Proof.sound hp) ℕ inferInstance

/-- The Generated Quotient construction in `FailureOfComposition.ConcreteIndices`. -/
abbrev GeneratedQuotient (T : ArithmeticTheory) :=
  ProgramIndices.GeneratedIndexQuotient ConcreteEvaluator.arithmetization T

/-- The generated Quotient Mk construction in `FailureOfComposition.ConcreteIndices`. -/
def generatedQuotientMk (T : ArithmeticTheory) (e : ℕ) : GeneratedQuotient T :=
  Quotient.mk (generatedSetoid T) e

theorem generated_quotient_mul_mk (T : ArithmeticTheory) (e d : ℕ) :
    generatedQuotientMk T e * generatedQuotientMk T d =
      generatedQuotientMk T (canonicalPartrecCompIndex e d) :=
  rfl

/-- The concrete index quotient and functional-graph quotient are isomorphic
as monoids, with their induced composition operations. -/
def generatedQuotientMulEquiv (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    GeneratedQuotient T ≃* GeneratedCongruence.QuotientGraph T :=
  ProgramIndices.generatedQuotientMulEquiv ConcreteEvaluator.arithmetization T

theorem generated_quotient_subsingleton_iff_not_sound (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    Subsingleton (GeneratedQuotient T) ↔ ¬GeneratedCongruence.SigmaOneSound T :=
  ProgramIndices.generated_quotient_subsingleton_iff_not_sound ConcreteEvaluator.arithmetization
    T

end

end ConcreteIndices
end FailureOfComposition

end

end PointwiseComposition

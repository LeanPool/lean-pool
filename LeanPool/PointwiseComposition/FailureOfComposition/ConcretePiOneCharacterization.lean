/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneIndexCharacterization
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteGodel

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The manuscript's four-way characterization for the actual natural-number
program indices and history graphs. The ambient theory may be non-enumerable.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteIndices

/-- The Right Compatible construction in `FailureOfComposition.ConcreteIndices`. -/
def RightCompatible (T : ArithmeticTheory) : Prop :=
  ∀ f h g : ℕ,
    PointwiseIndex T f h →
      PointwiseIndex T (canonicalPartrecCompIndex f g) (canonicalPartrecCompIndex h g)

/-- The Composition Congruence construction in `FailureOfComposition.ConcreteIndices`. -/
def CompositionCongruence (T : ArithmeticTheory) : Prop :=
  ∀ f f' g g' : ℕ,
    PointwiseIndex T f f' →
      PointwiseIndex T g g' →
        PointwiseIndex T (canonicalPartrecCompIndex f g) (canonicalPartrecCompIndex f' g')

/-- The Agrees With Extensional construction in `FailureOfComposition.ConcreteIndices`. -/
def AgreesWithExtensional (T : ArithmeticTheory) : Prop :=
  ∀ e d : ℕ, PointwiseIndex T e d ↔ Kleene.eval e = Kleene.eval d

/-- Left composition preserves pointwise provability for every PA extension. -/
theorem pointwiseIndex_comp_left (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (f g h : ℕ)
    (hgh : PointwiseIndex T g h) :
    PointwiseIndex T (canonicalPartrecCompIndex f g) (canonicalPartrecCompIndex f h) :=
  ProgramIndices.pointwiseIndex_comp_left ConcreteEvaluator.arithmetization T f g h hgh

theorem rightCompatible_implies_piOneComplete (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (h : RightCompatible T) : PiOneCharacterization.PiOneComplete T :=
  PiOneCharacterization.rightCompatible_implies_piOneComplete T
    ((ProgramIndices.rightCompatible_iff_graph ConcreteEvaluator.arithmetization T).mp h)

theorem rightCompatible_iff_piOneComplete (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T] :
    RightCompatible T ↔ PiOneCharacterization.PiOneComplete T :=
  ProgramIndices.rightCompatible_iff_piOneComplete ConcreteEvaluator.arithmetization T

theorem compositionCongruence_iff_piOneComplete (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T] :
    CompositionCongruence T ↔ PiOneCharacterization.PiOneComplete T :=
  ProgramIndices.compositionCongruence_iff_piOneComplete ConcreteEvaluator.arithmetization T

theorem agreesWithExtensional_iff_piOneComplete (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T] :
    AgreesWithExtensional T ↔ PiOneCharacterization.PiOneComplete T :=
  ProgramIndices.agreesWithExtensional_iff_piOneComplete ConcreteEvaluator.arithmetization T

/-- Pointwise provability is exactly equality of the computed partial functions
when T is consistent and proves every true Pi-one sentence. -/
theorem pointwiseIndex_iff_evaluation_eq (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : PiOneCharacterization.PiOneComplete T) (e d : ℕ) :
    PointwiseIndex T e d ↔ Kleene.eval e = Kleene.eval d :=
  ProgramIndices.pointwiseIndex_iff_evaluation_eq ConcreteEvaluator.arithmetization T hT e d

/-- The four statements of the characterization, without a realization or
recursive-enumerability hypothesis. -/
theorem pi_one_characterization (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T] :
    (RightCompatible T ↔ CompositionCongruence T) ∧
      (CompositionCongruence T ↔ PiOneCharacterization.PiOneComplete T) ∧
        (PiOneCharacterization.PiOneComplete T ↔ AgreesWithExtensional T) :=
  ⟨(rightCompatible_iff_piOneComplete T).trans (compositionCongruence_iff_piOneComplete T).symm,
    compositionCongruence_iff_piOneComplete T, (agreesWithExtensional_iff_piOneComplete T).symm⟩

/-- Induced quotient composition fails exactly when Pi-one completeness fails. -/
theorem no_index_quotient_iff_not_piOneComplete (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T] :
    NoIndexQuotientComposition T ↔ ¬PiOneCharacterization.PiOneComplete T :=
  ProgramIndices.no_index_quotient_iff_not_piOneComplete ConcreteEvaluator.arithmetization T

end ConcreteIndices
end FailureOfComposition

end

end PointwiseComposition

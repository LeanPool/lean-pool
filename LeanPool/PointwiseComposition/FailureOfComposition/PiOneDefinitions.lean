/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GraphQuotient

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Definitions for the Pi-one completeness characterization.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace PiOneCharacterization

open ProofSearch

/-- Every true arithmetical Pi-one sentence is provable in `T`. -/
def PiOneComplete (T : ArithmeticTheory) : Prop :=
  ∀ σ : ArithmeticSentence, Hierarchy Π 1 σ → ℕ↓[ℒₒᵣ] ⊧ σ → T ⊢ σ

/-- Equality of the graphs on standard natural-number inputs and outputs. -/
def Extensional (F G : Graph) : Prop :=
  ∀ x y : ℕ, F.val.Evalb ![x, y] ↔ G.val.Evalb ![x, y]

/-- Right composition replaces the outer graph and fixes the inner graph. -/
def RightCompatible (T : ArithmeticTheory) : Prop :=
  ∀ F H G : Graph,
    Functional F →
      Functional H → Functional G → Pointwise T F H → Pointwise T (comp F G) (comp H G)

/-- The pointwise equivalence is preserved by composition in both arguments. -/
def CompositionCongruence (T : ArithmeticTheory) : Prop :=
  ∀ F F' G G' : Graph,
    Functional F →
      Functional F' →
        Functional G →
          Functional G' →
            Pointwise T F F' → Pointwise T G G' → Pointwise T (comp F G) (comp F' G')

/-- Pointwise provability agrees with standard equality on functional graphs. -/
def AgreesWithExtensional (T : ArithmeticTheory) : Prop :=
  ∀ F G : Graph, Functional F → Functional G → (Pointwise T F G ↔ Extensional F G)

end PiOneCharacterization
end FailureOfComposition

end

end PointwiseComposition

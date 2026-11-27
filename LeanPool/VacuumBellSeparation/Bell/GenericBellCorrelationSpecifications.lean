/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationDefs

/-!
Proposition specifications, not theorem declarations or assumptions. The two genericity
specifications are not proved in this library; the other three are proved in
`Bell/GenericBellCorrelationContinuity.lean` (`bellContinuityAndBounds_specification`) and
`Bell/GenericBellCorrelationCompatibility.lean` (`jointBellQuantityCompatibility_specification`,
`observableOrderCompatibility_specification`). HC00 Proposition 1 concerns unit
vectors; the normal-state conclusion additionally uses representation transfer.
Neither conclusion asserts Bell violation in the particular vacuum state.
-/

@[expose] public section

universe u
namespace VacuumBellSeparation.Bipartite.HC00

open scoped ComplexOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- HC00 Proposition 1, p. 4, in the original Hilbert space. -/
def VectorBellGenericitySpecification : Prop :=
  ∀ A B : VonNeumannAlgebra H,
    Commuting A B → HasSchliederProperty A B → IsInfiniteType A → IsInfiniteType B →
      IsOpen (bellCorrelatedVectors A B) ∧ Dense (bellCorrelatedVectors A B)

/-- HC00 p. 4, paragraph immediately after Proposition 1, together with p. 3
openness. Density is in the norm topology on ALL normal states of the joint VNA. -/
def NormalStateBellGenericitySpecification : Prop :=
  ∀ A B : VonNeumannAlgebra H,
    Commuting A B → HasSchliederProperty A B → IsInfiniteType A → IsInfiniteType B →
      IsOpen (bellCorrelatedNormalStates A B) ∧ Dense (bellCorrelatedNormalStates A B)

/-- HC00 p. 3: continuity and bounds on all states, not only normal states.
These are useful prerequisites, not hidden conditions defining a state. -/
def BellContinuityAndBoundsSpecification : Prop :=
  ∀ A B : VonNeumannAlgebra H, Commuting A B →
    (Continuous (fun φ : StateSpace (jointAlgebra A B) =>
      jointBellCorrelation A B φ.1)) ∧
    (∀ φ : StateSpace (jointAlgebra A B),
      1 ≤ jointBellCorrelation A B φ.1 ∧
        jointBellCorrelation A B φ.1 ≤ Real.sqrt 2) ∧
    (Continuous (fun Ω : UnitSphere H =>
      jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) Ω.1)))

/-- Definition bridge to the project's existing joint-algebra Bell quantity.
It does not require or assert a normal extension to all bounded operators. -/
def JointBellQuantityCompatibilitySpecification : Prop :=
  ∀ (A B : VonNeumannAlgebra H)
    (φ : (jointAlgebra A B).toStarSubalgebra →ₚ[ℂ] ℂ)
    (hA : (A : Set (H →L[ℂ] H)) ⊆ (jointAlgebra A B).toStarSubalgebra)
    (hB : (B : Set (H →L[ℂ] H)) ⊆ (jointAlgebra A B).toStarSubalgebra),
      jointBellCorrelation A B φ =
        localBellCorrelation (jointAlgebra A B).toStarSubalgebra φ A B hA hB

/-- HC00's operator-order formulation of the allowed local observables equals
the project's self-adjoint contraction predicate. This bridge is proved in
`Bell/GenericBellCorrelationCompatibility.lean` (`observableOrderCompatibility_specification`). -/
def ObservableOrderCompatibilitySpecification : Prop :=
  ∀ (A : VonNeumannAlgebra H) (X : H →L[ℂ] H),
    X ∈ saContractions A ↔ X ∈ A ∧ IsSelfAdjoint X ∧ -1 ≤ X ∧ X ≤ 1

end VacuumBellSeparation.Bipartite.HC00

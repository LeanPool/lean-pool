/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BipartiteNormalStateDefs
public import LeanPool.VacuumBellSeparation.Bell.LocalStateDefs

/-!
Definition proposal for HC00, arXiv:math-ph/9909013v3, Section II, pp. 2–5.
These definitions assume no Bell-correlation result. In particular a type of
normal states has its inherited operator-NORM topology, not WeakDual topology.
The joint algebra acts on the given full Hilbert space H.
-/

@[expose] public section

universe u
namespace VacuumBellSeparation.Bipartite.HC00

open scoped ComplexOrder InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original unit sphere, with the topology induced by the norm on H. -/
abbrev UnitSphere (H : Type u) [NormedAddCommGroup H] := {Ω : H // ‖Ω‖ = 1}

/-- All states on M itself. Continuous linear functionals carry the operator
norm; the state predicate is positive and unital. No ambient extension is chosen. -/
abbrev StateSpace (M : VonNeumannAlgebra H) :=
  {φ : StrongDual ℂ M.toStarSubalgebra // IsStateFunctional M φ}

/-- Normal states on M, with the inherited operator-norm topology.
Normality still means preservation of EVERY directed positive supremum, through
the existing explicit predicate. No sequential or vector-state restriction is used. -/
abbrev NormalStateSpace (M : VonNeumannAlgebra H) :=
  {φ : StrongDual ℂ M.toStarSubalgebra // IsNormalStateFunctional M φ}

/-- Literal Schlieder property. Commutation is a separate hypothesis. -/
def HasSchliederProperty (A B : VonNeumannAlgebra H) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ B, X * Y = 0 → X = 0 ∨ Y = 0

/-- The identity of A is equivalent IN A to a proper subprojection: the
partial isometry has initial projection 1 and final projection different from 1.
This asks for a proper isometry, not two orthogonal isometries with initial 1;
it does not replace infinite type by nonabelianity or by infinite dimension. -/
def IsInfiniteType (A : VonNeumannAlgebra H) : Prop :=
  ∃ V : H →L[ℂ] H, V ∈ A ∧ star V * V = 1 ∧ V * star V ≠ 1

/-- HC00's normalized CHSH values, evaluated entirely in the joint algebra.
Each observable is a self-adjoint contraction in its original local algebra.
For a linear state, moving the factor 1/2 outside its absolute value is exact. -/
def jointBellValues (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : Set ℝ :=
  {r | ∃ X₀ X₁ Y₀ Y₁ : (jointAlgebra A B).toStarSubalgebra,
    (X₀ : H →L[ℂ] H) ∈ saContractions A ∧
    (X₁ : H →L[ℂ] H) ∈ saContractions A ∧
    (Y₀ : H →L[ℂ] H) ∈ saContractions B ∧
    (Y₁ : H →L[ℂ] H) ∈ saContractions B ∧
    r = (1 / 2 : ℝ) * ‖f (X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁))‖}

/-- The supremum of normalized CHSH values attained by local observables in the joint algebra. -/
noncomputable def jointBellCorrelation (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : ℝ :=
  sSup (jointBellValues A B f)

/-- Bell violation is strict excess over the classical bound; no maximality. -/
noncomputable def bellCorrelatedVectors (A B : VonNeumannAlgebra H) :
    Set (UnitSphere H) :=
  {Ω | 1 < jointBellCorrelation A B (vectorFunctional (jointAlgebra A B) Ω.1)}

/-- This set includes every normal state satisfying strict Bell violation,
not merely the normal states represented by a vector in this representation. -/
noncomputable def bellCorrelatedNormalStates (A B : VonNeumannAlgebra H) :
    Set (NormalStateSpace (jointAlgebra A B)) :=
  {φ | 1 < jointBellCorrelation A B φ.1}

end VacuumBellSeparation.Bipartite.HC00

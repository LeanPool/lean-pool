/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs

/-!
Joint von Neumann algebras and their state functionals, following HC00,
arXiv:math-ph/9909013v3, Section III. A positive functional is normal when
it preserves positive directed suprema.
-/

@[expose] public section

universe u
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual jointly generated von Neumann algebra in the original H. -/
noncomputable def jointAlgebra (A B : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  generatedVNA ((A : Set (H →L[ℂ] H)) ∪ (B : Set (H →L[ℂ] H)))

/-- A complex-linear, positive, unital functional on M itself.
Continuity follows from positivity on the closed C-star algebra; normality does not. -/
def IsStateFunctional (M : VonNeumannAlgebra H)
    (f : M.toStarSubalgebra → ℂ) : Prop :=
  ∃ φ : M.toStarSubalgebra →ₚ[ℂ] ℂ, φ 1 = 1 ∧ ∀ X, φ X = f X

/-- Order-normality of a positive functional. All directed sets are quantified,
not merely sequences. Existence of the displayed upper bound already implies
boundedness of the directed positive set. For positive functionals, equivalence with
continuity in the weak topology of the coefficient predual is proved
(`isNormalFunctional_iff_continuous_coefficientWeak` in `Bell/CoefficientWeakTopology.lean`),
and so is normality of vector functionals (`vectorFunctional_isNormal` in
`Bell/VectorFunctionalNormal.lean`). -/
def IsNormalFunctional (M : VonNeumannAlgebra H)
    (f : M.toStarSubalgebra → ℂ) : Prop :=
  ∀ s : Set M.toStarSubalgebra, s.Nonempty → DirectedOn (· ≤ ·) s →
    (∀ X ∈ s, 0 ≤ X) → ∀ X : M.toStarSubalgebra,
      IsLUB s X → IsLUB ((fun Y => (f Y).re) '' s) (f X).re

/-- A positive unital functional which preserves suprema of bounded directed sets of positive
operators. -/
def IsNormalStateFunctional (M : VonNeumannAlgebra H)
    (f : M.toStarSubalgebra → ℂ) : Prop :=
  IsStateFunctional M f ∧ IsNormalFunctional M f

/-- Product factorization of a joint state across the original A and B.
For a unital state the two factors are exactly its own marginal restrictions;
this avoids arbitrary ambient-state extensions. -/
def HasProductFactorization (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : Prop :=
  ∀ X Y : (jointAlgebra A B).toStarSubalgebra,
    (X : H →L[ℂ] H) ∈ A → (Y : H →L[ℂ] H) ∈ B →
      f (X * Y) = f X * f Y

/-- A normal state on the joint algebra whose expectations of products factor over the two local
algebras. -/
def IsNormalProductState (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : Prop :=
  IsNormalStateFunctional (jointAlgebra A B) f ∧ HasProductFactorization A B f

/-- The actual vector functional restricted to M, with mathlib's inner product
linear in its second argument. The unit-vector premise belongs to its proofs. -/
noncomputable def vectorFunctional (M : VonNeumannAlgebra H) (Ω : H) :
    M.toStarSubalgebra → ℂ :=
  fun X => ⟪Ω, (X : H →L[ℂ] H) Ω⟫_ℂ

/-- Full-H cyclicity, not cyclicity in a preselected cyclic subspace. -/
def IsCyclicForAlgebra (M : VonNeumannAlgebra H) (Ω : H) : Prop :=
  (Submodule.span ℂ {x : H | ∃ X : H →L[ℂ] H, X ∈ M ∧ x = X Ω}).topologicalClosure = ⊤

/-- The algebra contains a pair of operators that do not commute. -/
def IsNonabelian (M : VonNeumannAlgebra H) : Prop :=
  ∃ X ∈ M, ∃ Y ∈ M, X * Y ≠ Y * X

end VacuumBellSeparation.Bipartite

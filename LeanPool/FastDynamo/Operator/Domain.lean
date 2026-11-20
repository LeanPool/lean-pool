/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operators with a bundled Banach domain

The paper uses closed unbounded operators on `L²` with domain `H²`.  Rather than introducing a
generic partially defined operator immediately, we represent such an operator by bounded maps from
its Banach domain into the ambient space.  Resolvents therefore retain the stronger
ambient-to-domain mapping property needed in `prop:local-seed` (Proposition 2.2).
-/

@[expose] public section

namespace FastDynamo

universe u v

/-- An operator on `X` represented as a bounded map out of a Banach domain `D`. -/
structure DomainOperator (X : Type u) (D : Type v)
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup D] [NormedSpace ℂ D] where
  /-- Continuous inclusion of the operator domain into the ambient space. -/
  embedding : D →L[ℂ] X
  embedding_injective : Function.Injective embedding
  /-- The operator regarded as a bounded map from its graph domain. -/
  op : D →L[ℂ] X

namespace DomainOperator

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The domain-to-ambient pencil `z - A`. -/
def pencil (A : DomainOperator X D) (z : ℂ) : D →L[ℂ] X :=
  z • A.embedding - A.op

/-- An eigenpair for a domain operator, with nonvanishing measured in its
ambient state space. -/
def IsEigenpair (A : DomainOperator X D) (eigenvalue : ℂ) (b : D) : Prop :=
  A.embedding b ≠ 0 ∧ A.op b = eigenvalue • A.embedding b

end DomainOperator

/--
A chosen domain-valued resolvent on `S`.  Both inverse equations are retained
explicitly; this is the exact interface needed by the global parametrix proof.
-/
structure HasResolventOn {X : Type u} {D : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    (A : DomainOperator X D) (S : Set ℂ) where
  /-- The chosen ambient-to-domain inverse of the operator pencil. -/
  inv : ℂ → X →L[ℂ] D
  left_inv : ∀ z ∈ S,
    (inv z).comp (A.pencil z) = ContinuousLinearMap.id ℂ D
  right_inv : ∀ z ∈ S,
    (A.pencil z).comp (inv z) = ContinuousLinearMap.id ℂ X
  continuousOn : ContinuousOn inv S

namespace HasResolventOn

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S T : Set ℂ}

/-- The ordinary ambient-space resolvent induced by the domain-valued one. -/
def stateResolvent (h : HasResolventOn A S) (z : ℂ) : X →L[ℂ] X :=
  A.embedding.comp (h.inv z)

end HasResolventOn

end FastDynamo

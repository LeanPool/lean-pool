/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

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

/-- The affine operator pencils at two parameters differ only in their
domain embedding term. -/
theorem pencil_sub_pencil (A : DomainOperator X D) (w z : ℂ) :
    A.pencil w - A.pencil z = (w - z) • A.embedding := by
  apply ContinuousLinearMap.ext
  intro d
  simp only [pencil, sub_apply, smul_apply]
  rw [sub_smul]
  module

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

/-- The resolvent at `z` applied to the pencil at another parameter `w`: the
deviation from the identity of the domain is the domain-valued resolvent
composed with the embedding. -/
theorem inv_comp_pencil (h : HasResolventOn A S) {z w : ℂ} (hz : z ∈ S) :
    (h.inv z).comp (A.pencil w)
      = ContinuousLinearMap.id ℂ D + (w - z) • (h.inv z).comp A.embedding := by
  have hpw : A.pencil w = A.pencil z + (w - z) • A.embedding := by
    ext d
    simp [DomainOperator.pencil, sub_smul]
  rw [hpw, ContinuousLinearMap.comp_add, h.left_inv z hz]
  congr 1
  ext d; simp

/-- The resolvent identity in its domain-valued form,
`R(z) - R(w) = (w - z) R(z) R(w)`, with the right-hand resolvent read as a state
resolvent. -/
theorem inv_sub_inv (h : HasResolventOn A S) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    h.inv z - h.inv w = (w - z) • (h.inv z).comp (h.stateResolvent w) := by
  calc h.inv z - h.inv w
      = ((h.inv z).comp (A.pencil w)).comp (h.inv w) - h.inv w := by
        rw [ContinuousLinearMap.comp_assoc, h.right_inv w hw,
          ContinuousLinearMap.comp_id]
    _ = (ContinuousLinearMap.id ℂ D
          + (w - z) • (h.inv z).comp A.embedding).comp (h.inv w) - h.inv w := by
        rw [inv_comp_pencil h hz]
    _ = (w - z) • (h.inv z).comp (h.stateResolvent w) := by
        ext x; simp [HasResolventOn.stateResolvent]

/-- The resolvent identity on the ambient space:
`R(z) - R(w) = (w - z) R(z) R(w)` for the state resolvents. -/
theorem stateResolvent_sub_stateResolvent (h : HasResolventOn A S) {z w : ℂ}
    (hz : z ∈ S) (hw : w ∈ S) :
    h.stateResolvent z - h.stateResolvent w
      = (w - z) • (h.stateResolvent z).comp (h.stateResolvent w) := by
  have := congrArg (fun T : X →L[ℂ] D ↦ A.embedding.comp T) (h.inv_sub_inv hz hw)
  simpa [HasResolventOn.stateResolvent, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.comp_assoc] using this

end HasResolventOn

end FastDynamo

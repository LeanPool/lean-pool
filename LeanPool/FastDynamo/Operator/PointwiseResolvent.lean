/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.ResolventPropagation

/-!
# Bundling pointwise inverses into a resolvent family

For the affine pencil `z - A`, one explicit two-sided inverse at a base point
determines a continuous propagated inverse wherever its ambient correction is
a unit.  If a two-sided inverse is known separately at every point of a set,
then those corrections are automatically units: the correction is the
composition of the target pencil with the base inverse, hence a composition
of two isomorphisms.

The construction below keeps the base inverse explicit.  Pointwise inverses
are used only to prove invertibility of the corrections, so no choice of a
possibly incoherent inverse-valued function is stored in the resulting
`HasResolventOn` witness.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

omit [CompleteSpace X] in
/-- A pointwise two-sided inverse at `z` makes the ambient correction from a
fixed base inverse at `z₀` a unit. -/
theorem resolventCorrection_isUnit_of_pointwise_twoSidedInverse
    (A : DomainOperator X D) (z₀ z : ℂ)
    (T₀ T : X →L[ℂ] D)
    (hleft₀ : T₀.comp (A.pencil z₀) = ContinuousLinearMap.id ℂ D)
    (hright₀ : (A.pencil z₀).comp T₀ = ContinuousLinearMap.id ℂ X)
    (hleft : T.comp (A.pencil z) = ContinuousLinearMap.id ℂ D)
    (hright : (A.pencil z).comp T = ContinuousLinearMap.id ℂ X) :
    IsUnit (resolventCorrection (A.embedding.comp T₀) z₀ z) := by
  let C : X →L[ℂ] X := resolventCorrection (A.embedding.comp T₀) z₀ z
  let L : X →L[ℂ] X := (A.pencil z₀).comp T
  have hC : C = (A.pencil z).comp T₀ :=
    (pencil_comp_baseInverse A z₀ z T₀ hright₀).symm
  have hCL : C.comp L = ContinuousLinearMap.id ℂ X := by
    apply ContinuousLinearMap.ext
    intro x
    have hleft₀x := congrArg (fun Q : D →L[ℂ] D ↦ Q (T x)) hleft₀
    have hrightx := congrArg (fun Q : X →L[ℂ] X ↦ Q x) hright
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hleft₀x hrightx ⊢
    rw [hC]
    change A.pencil z (T₀ (A.pencil z₀ (T x))) = x
    rw [hleft₀x, hrightx]
  have hLC : L.comp C = ContinuousLinearMap.id ℂ X := by
    apply ContinuousLinearMap.ext
    intro x
    have hleftx := congrArg (fun Q : D →L[ℂ] D ↦ Q (T₀ x)) hleft
    have hright₀x := congrArg (fun Q : X →L[ℂ] X ↦ Q x) hright₀
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hleftx hright₀x ⊢
    rw [hC]
    change A.pencil z₀ (T (A.pencil z (T₀ x))) = x
    rw [hleftx, hright₀x]
  change IsUnit C
  refine ⟨{ val := C, inv := L, val_inv := ?_, inv_val := ?_ }, rfl⟩
  · exact hCL
  · exact hLC

/-- Bundle pointwise invertibility of an affine domain-operator pencil into a
single continuous `HasResolventOn` witness.

Only the base inverse `T₀` is retained by the construction.  The existential
pointwise inverses prove that every correction is a unit; the
rational propagation formula then supplies a coherent continuous family. -/
def hasResolventOnOfPointwiseTwoSidedInverses
    (A : DomainOperator X D) (z₀ : ℂ) (T₀ : X →L[ℂ] D)
    (hleft₀ : T₀.comp (A.pencil z₀) = ContinuousLinearMap.id ℂ D)
    (hright₀ : (A.pencil z₀).comp T₀ = ContinuousLinearMap.id ℂ X)
    (S : Set ℂ)
    (hpoint : ∀ z ∈ S, ∃ T : X →L[ℂ] D,
      T.comp (A.pencil z) = ContinuousLinearMap.id ℂ D ∧
        (A.pencil z).comp T = ContinuousLinearMap.id ℂ X) :
    HasResolventOn A S :=
  hasResolventOnOfIsUnitResolventCorrection A z₀ T₀ hleft₀ hright₀ S
    (fun z hz ↦ by
      obtain ⟨T, hleft, hright⟩ := hpoint z hz
      exact resolventCorrection_isUnit_of_pointwise_twoSidedInverse
        A z₀ z T₀ T hleft₀ hright₀ hleft hright)

end DomainOperator

end

end FastDynamo

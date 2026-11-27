/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.TensorPowerHilbert
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Genuine permutation unitaries on completed Hilbert tensor powers

Algebraic reindexing preserves the product inner form. Its completion is
surjective by the completed inverse, so permutations act by actual
unitaries on the completed n-fold Hilbert tensor product.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open scoped TensorProduct InnerProductSpace

section Completion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem isometry_completion_inverse (e : E ≃ₗᵢ[ℂ] F)
    (x : UniformSpace.Completion E) :
    e.symm.toLinearIsometry.completion (e.toLinearIsometry.completion x) = x := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) continuous_id) ?_
  intro y
  simp only [LinearIsometry.completion_apply_coe]
  change ((e.symm (e y) : E) : UniformSpace.Completion E) = y
  exact congrArg (fun z : E => (z : UniformSpace.Completion E)) (e.symm_apply_apply y)

/-- Isometry equivalence completion of type `UniformSpace.Completion E ≃ₗᵢ[ℂ]
UniformSpace.Completion F`. -/
def isometryEquivCompletion (e : E ≃ₗᵢ[ℂ] F) :
    UniformSpace.Completion E ≃ₗᵢ[ℂ] UniformSpace.Completion F :=
  LinearIsometryEquiv.ofSurjective e.toLinearIsometry.completion (fun y =>
    ⟨e.symm.toLinearIsometry.completion y, isometry_completion_inverse e.symm y⟩)

theorem isometryEquivCompletion_coe (e : E ≃ₗᵢ[ℂ] F) (x : E) :
    isometryEquivCompletion e x = (e x : UniformSpace.Completion F) :=
  LinearIsometry.completion_apply_coe _ _

end Completion

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ)

theorem tensorPower_reindex_inner (e : Equiv.Perm (Fin n))
    (x y : TensorPower ℂ n H) :
    inner ℂ (PiTensorProduct.reindex ℂ (fun _ : Fin n => H) e x)
      (PiTensorProduct.reindex ℂ (fun _ : Fin n => H) e y) = inner ℂ x y := by
  refine x.induction_on ?_ ?_
  · intro c v
    refine y.induction_on ?_ ?_
    · intro d w
      simp only [map_smul, inner_smul_left, inner_smul_right,
        PiTensorProduct.reindex_tprod, tensorPower_inner_tprod]
      rw [Equiv.prod_comp e.symm (fun i => inner ℂ (v i) (w i))]
    · intro y z hy hz
      simp only [map_add, inner_add_right, hy, hz]
  · intro x z hx hz
    simp only [map_add, inner_add_left, hx, hz]

/-- Linear isometry equivalence for the algebraic tensor permutation, of type `TensorPower ℂ n H
≃ₗᵢ[ℂ] TensorPower ℂ n H`. -/
def algebraicTensorPermutation (e : Equiv.Perm (Fin n)) :
    TensorPower ℂ n H ≃ₗᵢ[ℂ] TensorPower ℂ n H :=
  (PiTensorProduct.reindex ℂ (fun _ : Fin n => H) e).isometryOfInner
    (tensorPower_reindex_inner H n e)

/-- Tensor permutation obtained from `isometryEquivCompletion`. -/
def tensorPermutation (e : Equiv.Perm (Fin n)) :
    HilbertTensorPower H n ≃ₗᵢ[ℂ] HilbertTensorPower H n :=
  isometryEquivCompletion (algebraicTensorPermutation H n e)

theorem tensorPermutation_tensorVector (e : Equiv.Perm (Fin n)) (v : Fin n → H) :
    tensorPermutation H n e (tensorVector H n v) =
      tensorVector H n (fun i => v (e.symm i)) := by
  rw [tensorPermutation, tensorVector, isometryEquivCompletion_coe]
  change ((PiTensorProduct.reindex ℂ (fun _ : Fin n => H) e
    (PiTensorProduct.tprod ℂ v) : TensorPower ℂ n H) : HilbertTensorPower H n) = _
  rw [PiTensorProduct.reindex_tprod]
  rfl

theorem tensorPermutation_diagonal (e : Equiv.Perm (Fin n)) (v : H) :
    tensorPermutation H n e (tensorVector H n (fun _ => v)) = tensorVector H n (fun _ => v) :=
  tensorPermutation_tensorVector H n e _

end VacuumBellSeparation.Fock

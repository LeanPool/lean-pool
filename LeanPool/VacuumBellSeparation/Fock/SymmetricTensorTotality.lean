/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.SymmetricFockSpace
public import LeanPool.VacuumBellSeparation.Fock.SymmetricMultilinearDiagonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Totality of diagonal tensors in each actual symmetric sector

The pure-tensor map is bounded multilinear in the genuine Hilbert tensor
norm. An invariant vector determines a symmetric multilinear scalar form.
The proved diagonal determination theorem then gives its vanishing on
all mixed tensors, and algebraic tensor spanning plus completion gives
the vector itself zero.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open scoped TensorProduct InnerProductSpace

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ)

theorem norm_tensorVector (v : Fin n → H) :
    ‖tensorVector H n v‖ = ∏ i, ‖v i‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)).mp
  have h := congrArg norm (inner_tensorVector H n v v)
  simpa only [inner_self_eq_norm_sq_to_K, norm_prod, norm_pow,
    RCLike.norm_ofReal, abs_norm, ← Finset.prod_pow] using h

/-- Multilinear map sending a family of vectors to its simple tensor. -/
def tensorMultilinear : ContinuousMultilinearMap ℂ (fun _ : Fin n => H) (HilbertTensorPower H n) :=
  (((UniformSpace.Completion.toComplL : TensorPower ℂ n H →L[ℂ] HilbertTensorPower H
    n).toLinearMap).compMultilinearMap (PiTensorProduct.tprod ℂ)).mkContinuous 1
      (fun v => by
        change ‖tensorVector H n v‖ ≤ 1 * ∏ i, ‖v i‖
        rw [norm_tensorVector, one_mul])

theorem tensorMultilinear_apply (v : Fin n → H) :
    tensorMultilinear H n v = tensorVector H n v := rfl

theorem tensorVector_smul (c : ℂ) (v : H) :
    tensorVector H n (fun _ => c • v) = c ^ n • tensorVector H n (fun _ => v) := by
  have h := (tensorMultilinear H n).toMultilinearMap.map_smul_univ
    (fun _ : Fin n => c) (fun _ : Fin n => v)
  change tensorVector H n (fun _ => c • v) =
    (∏ _ : Fin n, c) • tensorVector H n (fun _ => v) at h
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem pureSymmetricTensor_smul (c : ℂ) (v : H) :
    pureSymmetricTensor H n (c • v) = c ^ n • pureSymmetricTensor H n v := by
  apply Subtype.ext
  exact tensorVector_smul H n c v

theorem eq_zero_of_inner_mixedTensor_zero (x : HilbertTensorPower H n)
    (hx : ∀ v, inner ℂ x (tensorVector H n v) = 0) : x = 0 := by
  have hall : ∀ y : HilbertTensorPower H n, inner ℂ x y = 0 := by
    intro y
    refine UniformSpace.Completion.induction_on y
      (isClosed_eq (by fun_prop) continuous_const) ?_
    intro z
    refine z.induction_on ?_ ?_
    · intro c v
      rw [UniformSpace.Completion.coe_smul, inner_smul_right]
      change c * inner ℂ x (tensorVector H n v) = 0
      rw [hx v, mul_zero]
    · intro a b ha hb
      simp only [UniformSpace.Completion.coe_add, inner_add_right, ha, hb, add_zero]
  exact inner_self_eq_zero.mp (hall x)

/-- Symmetric tensor scalar form. -/
def symmetricTensorScalarForm (x : SymmetricTensorPower H n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => H) ℂ :=
  (innerSL ℂ (x : HilbertTensorPower H n)).compContinuousMultilinearMap (tensorMultilinear H n)

theorem symmetricTensorScalarForm_invariant (x : SymmetricTensorPower H n) :
    MultilinearPermutationInvariant (symmetricTensorScalarForm H n x) := by
  intro e v
  have hi := (tensorPermutation H n e.symm).inner_map_map
    (x : HilbertTensorPower H n) (tensorVector H n v)
  rw [x.property e.symm, tensorPermutation_tensorVector, Equiv.symm_symm] at hi
  exact hi

theorem eq_zero_of_inner_pureSymmetricTensor_zero (x : SymmetricTensorPower H n)
    (hx : ∀ v, inner ℂ x (pureSymmetricTensor H n v) = 0) : x = 0 := by
  have hm : symmetricTensorScalarForm H n x = 0 :=
    symmetric_multilinear_eq_zero_of_diagonal n (symmetricTensorScalarForm H n x)
      (symmetricTensorScalarForm_invariant H n x) hx
  apply Subtype.ext
  apply eq_zero_of_inner_mixedTensor_zero H n (x : HilbertTensorPower H n)
  intro v
  exact congrArg (fun M : ContinuousMultilinearMap ℂ (fun _ : Fin n => H) ℂ => M v) hm

theorem pureSymmetricTensor_dense_span :
    (Submodule.span ℂ (Set.range (pureSymmetricTensor H n))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℂ (Set.range (pureSymmetricTensor H n))
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply eq_zero_of_inner_pureSymmetricTensor_zero H n x
    intro v
    exact K.inner_left_of_mem_orthogonal (Submodule.subset_span ⟨v, rfl⟩) hx
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, horth]

end VacuumBellSeparation.Fock

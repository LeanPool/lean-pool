/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.Fibre


/-!
# Base change of normalised extension isomorphisms

For an algebra map `B → B'` of commutative `A`-algebras, an `A[X]`-module `M` and its fibre
`N = M(0)`, the transition maps `B[X] ⊗[A] N → B'[X] ⊗[A] N` and
`B[X] ⊗[A[X]] M → B'[X] ⊗[A[X]] M` are compared, and a `B[X]`-linear isomorphism
`u : B[X] ⊗[A] N ≅ B[X] ⊗[A[X]] M` is base changed to `B'`. Normalisation at zero is preserved.

## Main results

* `transP`, `transM`: the transition maps.
* `baseChangeEquiv`: the base change of an isomorphism along `B → B'`.
* `baseChangeEquiv_transP`, `fibreMap_baseChangeEquiv`: compatibility and normalisation.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A[X] M]
variable (B B' : Type*) [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] [Algebra B B']
  [IsScalarTower A B B']

/-- The transition map `B[X] ⊗[A] N → B'[X] ⊗[A] N`, as an `A[X]`-linear map. -/
def transP (N : Type*) [AddCommGroup N] [Module A N] :
    letI := Polynomial.algebra A B
    letI := Polynomial.algebra A B'
    B[X] ⊗[A] N →ₗ[A[X]] B'[X] ⊗[A] N :=
  letI := Polynomial.algebra A B
  letI := Polynomial.algebra A B'
  letI := Polynomial.algebra B B'
  AlgebraTensorModule.map (IsScalarTower.toAlgHom A[X] B[X] B'[X]).toLinearMap LinearMap.id

theorem transP_tmul (N : Type*) [AddCommGroup N] [Module A N] (p : B[X]) (n : N) :
    transP A B B' N (p ⊗ₜ n) = p.map (algebraMap B B') ⊗ₜ n := rfl

/-- The transition map `B[X] ⊗[A[X]] M → B'[X] ⊗[A[X]] M`. -/
def transM :
    letI := Polynomial.algebra A B
    letI := Polynomial.algebra A B'
    B[X] ⊗[A[X]] M →ₗ[A[X]] B'[X] ⊗[A[X]] M :=
  letI := Polynomial.algebra A B
  letI := Polynomial.algebra A B'
  letI := Polynomial.algebra B B'
  (IsScalarTower.toAlgHom A[X] B[X] B'[X]).toLinearMap.rTensor M

theorem transM_tmul (p : B[X]) (m : M) :
    transM A M B B' (letI := Polynomial.algebra A B; p ⊗ₜ[A[X]] m) =
      (letI := Polynomial.algebra A B'; p.map (algebraMap B B') ⊗ₜ[A[X]] m) := rfl

variable {A M B B'} in
/-- The base change along `B → B'` of a `B[X]`-linear isomorphism
`B[X] ⊗[A] N ≅ B[X] ⊗[A[X]] M`. -/
def baseChangeEquiv {N : Type*} [AddCommGroup N] [Module A N]
    (u : (B[X] ⊗[A] N) ≃ₗ[B[X]] (letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M)) :
    (B'[X] ⊗[A] N) ≃ₗ[B'[X]] (letI := Polynomial.algebra A B'; B'[X] ⊗[A[X]] M) :=
  letI := Polynomial.algebra A B
  letI := Polynomial.algebra A B'
  letI := Polynomial.algebra B B'
  (AlgebraTensorModule.cancelBaseChange A B[X] B'[X] B'[X] N).symm ≪≫ₗ
    u.baseChange B[X] B'[X] _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange A[X] B[X] B'[X] B'[X] M

variable {A M B B'} in
theorem baseChangeEquiv_transP {N : Type*} [AddCommGroup N] [Module A N]
    (u : (B[X] ⊗[A] N) ≃ₗ[B[X]] (letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M))
    (x : B[X] ⊗[A] N) :
    baseChangeEquiv (B' := B') u (transP A B B' N x) = transM A M B B' (u x) := by
  let _ := Polynomial.algebra A B
  let _ := Polynomial.algebra A B'
  let _ := Polynomial.algebra B B'
  have h1 : (AlgebraTensorModule.cancelBaseChange A B[X] B'[X] B'[X] N).symm (transP A B B' N x) =
      (1 : B'[X]) ⊗ₜ x := by
    rw [LinearEquiv.symm_apply_eq]
    induction x using TensorProduct.inductionOn with
    | tmul p n =>
      rw [transP_tmul, AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => rw [map_add, hx, hy, tmul_add, map_add]
  simp only [baseChangeEquiv, LinearEquiv.trans_apply, h1, LinearEquiv.baseChange_tmul]
  induction u x using TensorProduct.inductionOn with
  | tmul p m =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, transM_tmul, Algebra.smul_def, mul_one]
    rfl
  | add y z hy hz => rw [tmul_add, map_add, hy, hz, map_add]

theorem transP_eq_polyTensorMap (N : Type*) [AddCommGroup N] [Module A N] (x : B[X] ⊗[A] N) :
    transP A B B' N x = polyTensorMap N B (IsScalarTower.toAlgHom A B B') x := by
  induction x using TensorProduct.inductionOn with
  | tmul p n => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add]

variable {A M B B'} in
theorem cancelBaseChange_eq_smul_transP {N : Type*} [AddCommGroup N] [Module A N] (q : B'[X])
    (x : B[X] ⊗[A] N) :
    letI := Polynomial.algebra B B'
    AlgebraTensorModule.cancelBaseChange A B[X] B'[X] B'[X] N (q ⊗ₜ x) = q • transP A B B' N x := by
  let _ := Polynomial.algebra A B
  let _ := Polynomial.algebra A B'
  let _ := Polynomial.algebra B B'
  induction x using TensorProduct.inductionOn with
  | tmul p n =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, transP_tmul, smul_tmul', Algebra.smul_def,
      smul_eq_mul, mul_comm]
    rfl
  | add x y hx hy => rw [tmul_add, map_add, hx, hy, map_add, smul_add]

variable {A M B B'} in
/-- Base change preserves normalisation at zero. -/
theorem fibreMap_baseChangeEquiv
    (u : (B[X] ⊗[A] fibre A M) ≃ₗ[B[X]] (letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M))
    (hu : ∀ x, fibreMap A M B (u x) = reduce (fibre A M) B x) (x : B'[X] ⊗[A] fibre A M) :
    fibreMap A M B' (baseChangeEquiv (B' := B') u x) = reduce (fibre A M) B' x := by
  let _ := Polynomial.algebra A B
  let _ := Polynomial.algebra A B'
  let _ := Polynomial.algebra B B'
  obtain ⟨z, rfl⟩ := (AlgebraTensorModule.cancelBaseChange A B[X] B'[X] B'[X]
    (fibre A M)).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul q y =>
    rw [cancelBaseChange_eq_smul_transP, LinearEquiv.map_smul, fibreMap_smul,
      baseChangeEquiv_transP, reduce_smul]
    congr 1
    have := fibreMap_natural A M B (IsScalarTower.toAlgHom A B B')
      (transM A M B B').toAddMonoidHom (fun p m => transM_tmul A M B B' p m) (u y)
    rw [LinearMap.toAddMonoidHom_coe] at this
    rw [this, hu, transP_eq_polyTensorMap, reduce_polyTensorMap]
  | add y z hy hz => rw [map_add, map_add, fibreMap_add, hy, hz, map_add]

end LeanPool.QuillenSuslin


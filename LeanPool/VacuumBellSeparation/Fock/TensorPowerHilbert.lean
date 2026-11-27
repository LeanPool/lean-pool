/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Hilbert completion of the actual algebraic tensor powers

The algebraic carrier is Mathlib's n-fold PiTensorProduct. Its positive
inner product is constructed from the genuine binary Hilbert tensor
product by the canonical splitting equivalence. The completed carrier is
the n-fold Hilbert tensor power, before taking its symmetric subspace.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open scoped TensorProduct InnerProductSpace

section Pullback
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [AddCommGroup F] [Module ℂ F]

/-- Linear embedding inner core. -/
@[instance_reducible] def linearEmbeddingInnerCore (e : F →ₗ[ℂ] E) (he : Function.Injective e) :
    InnerProductSpace.Core ℂ F where
  inner x y := inner ℂ (e x) (e y)
  conj_inner_symm _ _ := inner_conj_symm _ _
  re_inner_nonneg _ := inner_self_nonneg
  add_left _ _ _ := by simp only [map_add, inner_add_left]
  smul_left _ _ _ := by simp only [map_smul, inner_smul_left]
  definite x hx := he (by simpa only [map_zero] using (inner_self_eq_zero.mp hx))

end Pullback

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The canonical last-factor splitting of the actual n-fold tensor. -/
def tensorPowerSplit (n : ℕ) :
    TensorPower ℂ (n + 1) H ≃ₗ[ℂ] (TensorPower ℂ n H) ⊗[ℂ] H :=
  ((PiTensorProduct.reindex ℂ (fun _ : Fin (n + 1) => H)
      (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm).trans
    (PiTensorProduct.tmulEquiv ℂ H).symm).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ _)
        (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => H) 0))

theorem tensorPowerSplit_tprod (n : ℕ) (v : Fin (n + 1) → H) :
    tensorPowerSplit H n (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i : Fin n => v i.castSucc) ⊗ₜ[ℂ] v (Fin.last n) := by
  simp only [tensorPowerSplit, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    Equiv.symm_symm, PiTensorProduct.tmulEquiv_symm_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_apply_tprod,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  rfl

/-- Positive definite inner product, derived recursively from actual tensor products. -/
@[instance_reducible] def tensorPowerInnerCore : (n : ℕ)
  → InnerProductSpace.Core ℂ (TensorPower ℂ n H)
  | 0 => linearEmbeddingInnerCore
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun _ : Fin 0 => H) (Fin 0)).toLinearMap
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun _ : Fin 0 => H) (Fin 0)).injective
  | n + 1 =>
      letI : InnerProductSpace.Core ℂ (TensorPower ℂ n H) := tensorPowerInnerCore n
      letI : NormedAddCommGroup (TensorPower ℂ n H) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      letI : InnerProductSpace ℂ (TensorPower ℂ n H) := InnerProductSpace.ofCore _
      linearEmbeddingInnerCore (tensorPowerSplit H n).toLinearMap (tensorPowerSplit H n).injective

instance tensorPowerCore (n : ℕ) : InnerProductSpace.Core ℂ (TensorPower ℂ n H) :=
  tensorPowerInnerCore H n

instance tensorPowerNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (TensorPower ℂ n H) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance tensorPowerInnerProductSpace (n : ℕ) : InnerProductSpace ℂ (TensorPower ℂ n H) :=
  InnerProductSpace.ofCore _

theorem tensorPower_inner_zero (x y : TensorPower ℂ 0 H) :
    inner ℂ x y = inner ℂ
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun _ : Fin 0 => H) (Fin 0) x)
      (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun _ : Fin 0 => H) (Fin 0) y) := rfl

theorem tensorPower_inner_succ (n : ℕ) (x y : TensorPower ℂ (n + 1) H) :
    inner ℂ x y = inner ℂ (tensorPowerSplit H n x) (tensorPowerSplit H n y) := rfl

/-- Exact Hilbert tensor Gram formula, including the empty tensor. -/
theorem tensorPower_inner_tprod (n : ℕ) (v w : Fin n → H) :
    inner ℂ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w) =
      ∏ i, inner ℂ (v i) (w i) := by
  induction n with
  | zero => simp only [tensorPower_inner_zero, PiTensorProduct.isEmptyEquiv_apply_tprod,
      RCLike.inner_apply, map_one, mul_one, Fin.prod_univ_zero]
  | succ n ih =>
      rw [tensorPower_inner_succ, tensorPowerSplit_tprod, tensorPowerSplit_tprod,
        TensorProduct.inner_tmul, ih, Fin.prod_univ_castSucc]

/-- The completed n-fold Hilbert tensor power of H. -/
abbrev HilbertTensorPower (n : ℕ) := UniformSpace.Completion (TensorPower ℂ n H)

/-- Tensor vector. -/
def tensorVector (n : ℕ) (v : Fin n → H) : HilbertTensorPower H n :=
  (PiTensorProduct.tprod ℂ v : TensorPower ℂ n H)

theorem inner_tensorVector (n : ℕ) (v w : Fin n → H) :
    inner ℂ (tensorVector H n v) (tensorVector H n w) = ∏ i, inner ℂ (v i) (w i) := by
  rw [tensorVector, tensorVector, UniformSpace.Completion.inner_coe, tensorPower_inner_tprod]

theorem inner_tensorVector_diagonal (n : ℕ) (v w : H) :
    inner ℂ (tensorVector H n (fun _ => v)) (tensorVector H n (fun _ => w)) =
      inner ℂ v w ^ n := by
  rw [inner_tensorVector]
  simp

end VacuumBellSeparation.Fock

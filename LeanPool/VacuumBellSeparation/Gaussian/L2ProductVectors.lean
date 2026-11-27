/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Actual products of square-summable vectors

An index equivalence turns the pointwise product into a vector in the
full ℓ² space. Its norm is the product of the norms, by nonnegative Fubini.
The resulting map is a genuine bounded bilinear map, not a tensor-product
identification assumed as additional data.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped lp ENNReal

variable {ι κ η : Type*}

theorem hasSum_l2_product_norm_sq (e : κ ≃ ι × η) (x : ℓ²(ι, ℂ)) (y : ℓ²(η, ℂ)) :
    HasSum (fun k => ‖x (e k).1 * y (e k).2‖ ^ 2) (‖x‖ ^ 2 * ‖y‖ ^ 2) := by
  have hx : HasSum (fun i => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
    simpa [Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) x
  have hy : HasSum (fun j => ‖y j‖ ^ 2) (‖y‖ ^ 2) := by
    simpa [Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) y
  have hp := hx.mul hy
    (hx.summable.mul_of_nonneg hy.summable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _))
  simpa only [Function.comp_def, norm_mul, mul_pow] using e.hasSum_iff.mpr hp

theorem l2_product_memℓp (e : κ ≃ ι × η) (x : ℓ²(ι, ℂ)) (y : ℓ²(η, ℂ)) :
    Memℓp (fun k => x (e k).1 * y (e k).2) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  simpa [Real.rpow_two] using (hasSum_l2_product_norm_sq e x y).summable

/-- L² product vector represented by `fun k => x (e k).1 * y (e k).2`. -/
def l2ProductVector (e : κ ≃ ι × η) (x : ℓ²(ι, ℂ)) (y : ℓ²(η, ℂ)) : ℓ²(κ, ℂ) :=
  ⟨fun k => x (e k).1 * y (e k).2, l2_product_memℓp e x y⟩

@[simp] theorem l2ProductVector_apply (e : κ ≃ ι × η) (x : ℓ²(ι, ℂ))
    (y : ℓ²(η, ℂ)) (k : κ) :
    l2ProductVector e x y k = x (e k).1 * y (e k).2 := rfl

theorem norm_l2ProductVector (e : κ ≃ ι × η) (x : ℓ²(ι, ℂ)) (y : ℓ²(η, ℂ)) :
    ‖l2ProductVector e x y‖ = ‖x‖ * ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have h : HasSum (fun k => ‖l2ProductVector e x y k‖ ^ 2)
      (‖l2ProductVector e x y‖ ^ 2) := by
    simpa [Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) (l2ProductVector e x y)
  rw [mul_pow]
  exact h.unique (hasSum_l2_product_norm_sq e x y)

/-- Linear map for the l² product bilinear, of type `ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(η, ℂ) →ₗ[ℂ] ℓ²(κ, ℂ)`. -/
def l2ProductBilinear (e : κ ≃ ι × η) : ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(η, ℂ) →ₗ[ℂ] ℓ²(κ, ℂ) :=
  LinearMap.mk₂ ℂ (l2ProductVector e)
    (by intro x₁ x₂ y; ext k; simp [add_mul])
    (by intro c x y; ext k; simp [mul_assoc])
    (by intro x y₁ y₂; ext k; simp [mul_add])
    (by intro c x y; ext k; simp [mul_left_comm])

/-- Continuous linear map for the l² product continuous, of type `ℓ²(ι, ℂ) →L[ℂ] ℓ²(η, ℂ) →L[ℂ]
ℓ²(κ, ℂ)`. -/
def l2ProductContinuous (e : κ ≃ ι × η) :
    ℓ²(ι, ℂ) →L[ℂ] ℓ²(η, ℂ) →L[ℂ] ℓ²(κ, ℂ) :=
  (l2ProductBilinear e).mkContinuous₂ 1 (by
    intro x y
    simpa only [l2ProductBilinear, LinearMap.mk₂_apply, norm_l2ProductVector, one_mul]
      using le_rfl (a := ‖x‖ * ‖y‖))

@[simp] theorem l2ProductContinuous_apply (e : κ ≃ ι × η) (x : ℓ²(ι, ℂ))
    (y : ℓ²(η, ℂ)) : l2ProductContinuous e x y = l2ProductVector e x y := rfl

/-- Actual coordinate unit vectors are products of coordinate unit vectors. -/
theorem l2ProductVector_single [DecidableEq ι] [DecidableEq κ] [DecidableEq η]
    (e : κ ≃ ι × η) (i : ι) (j : η) :
    l2ProductVector e (lp.single 2 i (1 : ℂ)) (lp.single 2 j (1 : ℂ)) =
      lp.single 2 (e.symm (i, j)) 1 := by
  classical
  ext k
  simp only [l2ProductVector_apply, lp.single_apply]
  have h : k = e.symm (i, j) ↔ (e k).1 = i ∧ (e k).2 = j := by
    rw [e.eq_symm_apply, Prod.ext_iff]
  by_cases hi : (e k).1 = i <;> by_cases hj : (e k).2 = j <;>
    simp [Pi.single_apply, hi, hj, h]

end VacuumBellSeparation.Gaussian

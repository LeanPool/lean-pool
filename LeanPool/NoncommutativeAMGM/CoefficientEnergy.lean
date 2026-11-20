/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.CoefficientOperator

/-!
# Coefficient inner products and the weighted Euler operator

The adjoint and energy identities needed to turn equation (38) into Lemma 3.10.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial

/-- The real coefficient inner product on polynomials. -/
noncomputable def realCoefficientInner (p q : Polynomial ℝ) : ℝ :=
  p.sum (fun i c ↦ c * q.coeff i)

theorem realCoefficientInner_eq_sum (p q : Polynomial ℝ) {N : ℕ} (hp : p.natDegree < N) :
    realCoefficientInner p q = ∑ i ∈ Finset.range N, p.coeff i * q.coeff i :=
  Polynomial.sum_over_range' p (fun _ ↦ by simp) N hp

theorem realCoefficientInner_comm (p q : Polynomial ℝ) :
    realCoefficientInner p q = realCoefficientInner q p := by
  rw [realCoefficientInner_eq_sum p q (N := max p.natDegree q.natDegree + 1) (by omega),
    realCoefficientInner_eq_sum q p (N := max p.natDegree q.natDegree + 1) (by omega)]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem realCoefficientInner_monomial (n : ℕ) (c : ℝ) (q : Polynomial ℝ) :
    realCoefficientInner (monomial n c) q = c * q.coeff n := by
  simp [realCoefficientInner]

theorem realCoefficientInner_add_left (p q r : Polynomial ℝ) :
    realCoefficientInner (p + q) r = realCoefficientInner p r + realCoefficientInner q r := by
  exact Polynomial.sum_add_index p q _ (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)

theorem realCoefficientInner_add_right (p q r : Polynomial ℝ) :
    realCoefficientInner p (q + r) = realCoefficientInner p q + realCoefficientInner p r := by
  simp [realCoefficientInner, coeff_add, mul_add]

theorem realCoefficientInner_smul_left (a : ℝ) (p q : Polynomial ℝ) :
    realCoefficientInner (a • p) q = a * realCoefficientInner p q := by
  rw [realCoefficientInner, Polynomial.sum_smul_index p a _ (fun _ ↦ by simp)]
  simp only [realCoefficientInner, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem realCoefficientInner_smul_right (a : ℝ) (p q : Polynomial ℝ) :
    realCoefficientInner p (a • q) = a * realCoefficientInner p q := by
  rw [realCoefficientInner_comm p, realCoefficientInner_smul_left,
    realCoefficientInner_comm q p]

theorem realCoefficientInner_sub_left (p q r : Polynomial ℝ) :
    realCoefficientInner (p - q) r = realCoefficientInner p r - realCoefficientInner q r := by
  have hneg := realCoefficientInner_smul_left (-1) q r
  simpa [sub_eq_add_neg, realCoefficientInner_add_left] using congrArg
    (fun x ↦ realCoefficientInner p r + x) hneg

theorem realCoefficientInner_sub_right (p q r : Polynomial ℝ) :
    realCoefficientInner p (q - r) = realCoefficientInner p q - realCoefficientInner p r := by
  rw [realCoefficientInner_comm p, realCoefficientInner_sub_left,
    realCoefficientInner_comm q p, realCoefficientInner_comm r p]

/-- Multiplication by `X` and division by `X` are coefficient adjoints. -/
theorem realCoefficientInner_X_mul (p q : Polynomial ℝ) :
    realCoefficientInner (X * p) q = realCoefficientInner p q.divX := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [mul_add, realCoefficientInner_add_left, hp, hr]
  | monomial n c => simp [X_mul_monomial]

/-- The unshifted Euler operator `X d/dX`. -/
noncomputable def coefficientEuler : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := X * p.derivative
  map_add' p q := by simp [mul_add]
  map_smul' a p := by simp

theorem coefficientEuler_coeff (p : Polynomial ℝ) (i : ℕ) :
    (coefficientEuler p).coeff i = (i : ℝ) * p.coeff i := by
  cases i with
  | zero => simp [coefficientEuler]
  | succ i =>
    simp only [coefficientEuler, LinearMap.coe_mk, AddHom.coe_mk, coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The diagonal operator `D(L-D)` on coefficient vectors. -/
noncomputable def weightedEuler (L : ℕ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
  (L : ℝ) • coefficientEuler - coefficientEuler * coefficientEuler

theorem weightedEuler_coeff (L : ℕ) (p : Polynomial ℝ) (i : ℕ) :
    (weightedEuler L p).coeff i = (i : ℝ) * ((L : ℝ) - i) * p.coeff i := by
  simp only [weightedEuler, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    coeff_sub, coeff_smul, smul_eq_mul, coefficientEuler_coeff]
  ring

theorem weightedEuler_divX (L : ℕ) (p : Polynomial ℝ) :
    (weightedEuler L p).divX = (L : ℝ) • p.derivative - (X * p.derivative).derivative := by
  have heq : weightedEuler L p =
      X * ((L : ℝ) • p.derivative - (X * p.derivative).derivative) := by
    simp only [weightedEuler, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      coefficientEuler, LinearMap.coe_mk, AddHom.coe_mk]
    simp [mul_sub]
  rw [heq]
  ext i
  simp

/-- The differential definition equals the adjoint-weighted-difference construction. -/
theorem coefficientOperator_eq_weighted (L : ℕ) (p : Polynomial ℝ) :
    coefficientOperator L p =
      (weightedEuler L ((X - 1) * p)).divX - weightedEuler L ((X - 1) * p) := by
  rw [weightedEuler_divX]
  simp only [coefficientOperator, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.mul_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    multiplyShift, shiftedEuler, coefficientEuler, weightedEuler, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_one, sub_zero,
    derivative_add, one_mul]
  norm_num [Algebra.smul_def]
  simp only [Polynomial.C_ofNat]
  ring

theorem weightedEuler_monomial (L i : ℕ) (c : ℝ) :
    weightedEuler L (monomial i c) = monomial i ((i : ℝ) * ((L : ℝ) - i) * c) := by
  ext k
  rw [weightedEuler_coeff]
  by_cases hk : i = k <;> simp [coeff_monomial, hk]

theorem weightedEuler_symmetric (L : ℕ) (p q : Polynomial ℝ) :
    realCoefficientInner p (weightedEuler L q) = realCoefficientInner (weightedEuler L p) q := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [map_add, realCoefficientInner_add_left, hp, hr]
  | monomial i c =>
    rw [weightedEuler_monomial, realCoefficientInner_monomial,
      realCoefficientInner_monomial, weightedEuler_coeff]
    ring

/-- The weighted quadratic form is an explicit sum of coefficient squares. -/
theorem weightedEuler_inner (L : ℕ) (p : Polynomial ℝ) :
    realCoefficientInner p (weightedEuler L p) =
      p.sum (fun i c ↦ (i : ℝ) * ((L : ℝ) - i) * c ^ 2) := by
  simp only [realCoefficientInner, Polynomial.sum_def, weightedEuler_coeff]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The coefficient adjoint identity from the proof of Lemma 3.10. -/
theorem coefficientOperator_inner (L : ℕ) (p q : Polynomial ℝ) :
    realCoefficientInner p (coefficientOperator L q) =
      realCoefficientInner ((X - 1) * p) (weightedEuler L ((X - 1) * q)) := by
  rw [coefficientOperator_eq_weighted, realCoefficientInner_sub_right,
    ← realCoefficientInner_X_mul, ← realCoefficientInner_sub_left]
  congr 1
  ring

/-- Self-adjointness of the actual operator in equation (38), for the coefficient inner product. -/
theorem coefficientOperator_symmetric (L : ℕ) (p q : Polynomial ℝ) :
    realCoefficientInner (coefficientOperator L p) q =
      realCoefficientInner p (coefficientOperator L q) := by
  rw [realCoefficientInner_comm (coefficientOperator L p) q,
    coefficientOperator_inner, weightedEuler_symmetric,
    realCoefficientInner_comm, ← coefficientOperator_inner]

/-- Squared coefficient seminorm with the first and last terms removed. -/
noncomputable def interiorCoefficientNormSq (L : ℕ) (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (L + 1), if i = 0 ∨ i = L then 0 else p.coeff i ^ 2

/-- The upper energy estimate in Lemma 3.10, including the omitted endpoint coefficients. -/
theorem coefficientOperator_energy_le (L : ℕ) (p : Polynomial ℝ) (hp : p.natDegree < L) :
    realCoefficientInner p (coefficientOperator L p) ≤
      ((L : ℝ) ^ 2 / 4) * interiorCoefficientNormSq L ((X - 1) * p) := by
  have hdeg : ((X - 1 : Polynomial ℝ) * p).natDegree < L + 1 := by
    have h : ((X - 1 : Polynomial ℝ) * p).natDegree ≤
        (X - 1 : Polynomial ℝ).natDegree + p.natDegree := Polynomial.natDegree_mul_le
    have hX : (X - 1 : Polynomial ℝ).natDegree = 1 := by
      compute_degree
      norm_num
    rw [hX] at h
    omega
  rw [coefficientOperator_inner, weightedEuler_inner,
    Polynomial.sum_over_range' _ (fun _ ↦ by simp) (L + 1) hdeg,
    interiorCoefficientNormSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hend : i = 0 ∨ i = L
  · rcases hend with rfl | rfl <;> simp
  · rw [ite_eq_right hend]
    have hw : (i : ℝ) * ((L : ℝ) - i) ≤ (L : ℝ) ^ 2 / 4 := by
      nlinarith [sq_nonneg ((i : ℝ) - (L : ℝ) / 2)]
    exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

end NoncommutativeAMGM

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.LinearCase
public import LeanPool.NairTenenbaum.Polynomials.PolynomialHeight
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentMainTerm

/-! # The shifted linear polynomial and its prime main term -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The polynomial system encoding the shifted linear factors. -/
noncomputable def shiftedLinearSystem (a : ℤ) : PolynomialSystem 1 1 where
  Q := fun _ => X + C a
  R := fun _ => X + C a
  exponent := identityExponents 1
  sign := fun _ => 1
  sign_abs := by simp
  factorization := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [identityExponents]
  irreducible := by
    intro h
    apply Polynomial.irreducible_of_degree_eq_one
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Polynomial.degree_X_add_C]
  nonassociated := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  exponent_pos := by intro h; simp
  noFixedPrime := by simpa using noFixedPrimeDivisor_X_add_C a

@[simp] theorem shiftedLinearSystem_total (a : ℤ) :
    (shiftedLinearSystem a).total = (X + C a : ℤ[X]) := by
  simp [PolynomialSystem.total, shiftedLinearSystem]

@[simp] theorem shiftedLinearSystem_radical (a : ℤ) :
    (shiftedLinearSystem a).radical = (X + C a : ℤ[X]) := by
  simp [PolynomialSystem.radical, shiftedLinearSystem]

@[simp] theorem shiftedLinearSystem_discriminant (a : ℤ) :
    (shiftedLinearSystem a).discriminant = 1 := by
  rw [PolynomialSystem.discriminant, shiftedLinearSystem_radical,
    Polynomial.discr_of_degree_eq_one (Polynomial.degree_X_add_C a)]
  rfl

@[simp] theorem shiftedLinearSystem_badDiscriminant (a : ℤ) :
    (shiftedLinearSystem a).badDiscriminant = 1 := by
  simp [PolynomialSystem.badDiscriminant]

@[simp] theorem shiftedLinearSystem_weight (a : ℤ) (F : ArithmeticMap 1) (N : ℕ+) :
    (shiftedLinearSystem a).weight F N = F (fun _ => N) / (N : ℝ) := by
  unfold PolynomialSystem.weight
  rw [shiftedLinearSystem_discriminant]
  change weight (identityExponents 1) 1 F
    (fun _ n => (rootCount (X + C a : ℤ[X]) n : ℝ)) N = _
  rw [weight_one_variable, ite_eq_left (Nat.coprime_one_right _)]
  simp only [rootCount_X_add_C, Nat.cast_one, mul_one]

theorem polynomialHeight_X_add_C (a : ℤ) :
    polynomialHeight (X + C a) = max 1 a.natAbs := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    by_cases hi₀ : i = 0
    · subst i; simpa only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add] using le_max_right 1
        a.natAbs
    by_cases hi₁ : i = 1
    · subst i
      simpa only [coeff_add, coeff_X_one, coeff_C_succ, add_zero, Int.natAbs_one] using
          le_max_left 1 a.natAbs
    simp only [coeff_add, coeff_X, coeff_C]
    simp [hi₀, Ne.symm hi₁]
  · apply max_le
    · have H := coeff_natAbs_le_height (X + C a : ℤ[X]) 1
      rw [coeff_add, coeff_X_one, coeff_C_succ] at H
      simpa only [add_zero, Int.natAbs_one] using H
    · have H := coeff_natAbs_le_height (X + C a : ℤ[X]) 0
      rw [coeff_add, coeff_X_zero, coeff_C_zero] at H
      simpa only [zero_add] using H

theorem polynomialHeight_X_add_C_of_ne_zero {a : ℤ} (ha : a ≠ 0) :
    polynomialHeight (X + C a) = a.natAbs := by
  rw [polynomialHeight_X_add_C, max_eq_right (Int.natAbs_pos.mpr ha)]

theorem sieveProduct_X_add_C (a : ℤ) (x : ℝ) :
    sieveProduct (X + C a) x = sieveProduct (X : ℤ[X]) x := by
  simp only [sieveProduct, rootCount_X_add_C, rootCount_X]

/-- The explicit right side of Corollary 7, before its uniform constant. -/
noncomputable def shiftedPrimeMainTerm (a : ℤ) (F : ArithmeticMap 1) (x y : ℝ) : ℝ :=
  ((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
    ∑ n ∈ positiveUpTo x, F (fun _ => n) / (n : ℝ)

theorem shiftedLinearSystem_primeMainTerm_le (a : ℤ) {F : ArithmeticMap 1}
    (hF : ∀ n, 0 ≤ F n) {x y : ℝ} (hx : 1 < x) (hy : 0 ≤ y) :
    primeMainTerm (shiftedLinearSystem a) F x y ≤ shiftedPrimeMainTerm a F x y := by
  rw [primeMainTerm_eq]
  simp only [shiftedLinearSystem_total, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, zero_add, sieveProduct_X_add_C, shiftedLinearSystem_weight]
  have hsum : 0 ≤ ∑ n ∈ positiveUpTo x, F (fun _ => n) / (n : ℝ) :=
    sum_nonneg (fun n _ => div_nonneg (hF _) (by positivity))
  have H := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sieveProduct_X_le_inv_log hx)
      (show 0 ≤ (a.natAbs : ℝ) / a.natAbs.totient * (y / Real.log x) by
        exact mul_nonneg (by positivity) (div_nonneg hy (Real.log_pos hx).le))) hsum
  exact H.trans_eq (by unfold shiftedPrimeMainTerm; ring)

end NairTenenbaum

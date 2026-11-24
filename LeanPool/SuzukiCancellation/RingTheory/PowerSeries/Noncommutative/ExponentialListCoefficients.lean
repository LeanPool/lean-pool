/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.Coefficients

/-!
# Homogeneous coefficients of ordered exponential lists

Finite Cauchy convolution defines the coefficients of any ordered product of
exponentials. Taking powers of its positive-degree part then gives the homogeneous
coefficients of the logarithm. These constructions require no topology.

## Main definitions

* `expListTerm`: a homogeneous coefficient of an ordered exponential product.
* `expListLogCoeff`: a homogeneous coefficient of its formal logarithm.

## Main results

* `map_expListTerm`, `map_expListLogCoeff`: compatibility with algebra homomorphisms.
* `expListTerm_smul`, `expListLogCoeff_smul`: homogeneous scaling.
* `sum_expListLogCoeff`: the finite logarithm as a sum of homogeneous coefficients.
-/

@[expose] public noncomputable section

open Finset Finset.Nat

namespace FQFP

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The degree-`n` coefficient of an ordered list of exponentials. -/
def expListTerm : List A → ℕ → A
  | [], n => if n = 0 then 1 else 0
  | a :: l, n => ∑ ij ∈ antidiagonal n,
      ((Nat.factorial ij.1 : ℚ)⁻¹ • a ^ ij.1) * expListTerm l ij.2

/-- The constant coefficient of every exponential product is one. -/
@[simp]
lemma expListTerm_zero (l : List A) : expListTerm l 0 = 1 := by
  induction l with
  | nil => simp [expListTerm]
  | cons a l ih => simp [expListTerm, ih]

/-- The linear coefficient is the sum of the exponent arguments in order. -/
@[simp]
lemma expListTerm_one (l : List A) : expListTerm l 1 = l.sum := by
  induction l with
  | nil => simp [expListTerm]
  | cons a l ih =>
      rw [expListTerm, sum_antidiagonal_eq_sum_range_succ_mk]
      simp [sum_range_succ, ih, Nat.factorial, add_comm]

/-- Algebra homomorphisms preserve homogeneous exponential-product coefficients. -/
lemma map_expListTerm {B : Type*} [Semiring B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (l : List A) (n : ℕ) :
    f (expListTerm l n) = expListTerm (l.map f) n := by
  induction l generalizing n with
  | nil => simp [expListTerm]
  | cons a l ih => simp [expListTerm, map_sum, ih]

/-- Scaling every input by `c` scales the degree-`n` exponential coefficient by `c ^ n`. -/
lemma expListTerm_smul {R : Type*} [CommSemiring R] [Algebra R A]
    (l : List A) (c : R) (n : ℕ) :
    expListTerm (l.map fun a ↦ c • a) n = c ^ n • expListTerm l n := by
  induction l generalizing n with
  | nil => by_cases hn : n = 0 <;> simp [expListTerm, hn]
  | cons a l ih =>
      simp only [List.map_cons, expListTerm, smul_sum]
      apply sum_congr rfl
      intro ij hij
      rw [smul_pow, ih, smul_comm ((Nat.factorial ij.1 : ℚ)⁻¹), smul_mul_smul_comm,
        ← pow_add, (mem_antidiagonal.mp hij)]

/-- The homogeneous degree-`n` coefficient of the formal logarithm of the product. -/
def expListLogCoeff (l : List A) (n : ℕ) : A :=
  ∑ k ∈ range (n + 1), logCoeff k • positivePowerCoeff (expListTerm l) k n

/-- The formal logarithm has zero constant coefficient. -/
@[simp]
lemma expListLogCoeff_zero (l : List A) : expListLogCoeff l 0 = 0 := by
  simp [expListLogCoeff, positivePowerCoeff]

/-- The empty exponential product has zero logarithm in every degree. -/
@[simp]
lemma expListLogCoeff_nil (n : ℕ) : expListLogCoeff ([] : List A) n = 0 := by
  apply sum_eq_zero
  intro k hk
  cases k with
  | zero => simp [logCoeff]
  | succ k => simp [positivePowerCoeff, expListTerm]

/-- The linear logarithm coefficient is the sum of the exponent arguments. -/
@[simp]
lemma expListLogCoeff_one (l : List A) : expListLogCoeff l 1 = l.sum := by
  simp [expListLogCoeff, sum_range_succ, positivePowerCoeff_one]

/-- Algebra homomorphisms preserve homogeneous logarithm coefficients. -/
lemma map_expListLogCoeff {B : Type*} [Semiring B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (l : List A) (n : ℕ) :
    f (expListLogCoeff l n) = expListLogCoeff (l.map f) n := by
  simp only [expListLogCoeff, map_sum, map_smul, map_positivePowerCoeff]
  simp only [map_expListTerm]

/-- Scaling every input by `c` scales the degree-`n` logarithm coefficient by `c ^ n`. -/
lemma expListLogCoeff_smul {R : Type*} [CommSemiring R] [Algebra R A]
    (l : List A) (c : R) (n : ℕ) :
    expListLogCoeff (l.map fun a ↦ c • a) n = c ^ n • expListLogCoeff l n := by
  have hterms : expListTerm (l.map fun a ↦ c • a) = fun i ↦ c ^ i • expListTerm l i :=
    funext (expListTerm_smul l c)
  simp only [expListLogCoeff, hterms, positivePowerCoeff_smul, smul_sum]
  apply sum_congr rfl
  intro k hk
  exact smul_comm (logCoeff k) (c ^ n) _

/-- The finite formal logarithm is the sum of its homogeneous coefficients. -/
lemma sum_expListLogCoeff (l : List A) (n : ℕ) :
    (∑ d ∈ range n, expListLogCoeff l d) =
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expListTerm l) k n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_smul_positivePowerTrunc_succ, expListLogCoeff]

end FQFP

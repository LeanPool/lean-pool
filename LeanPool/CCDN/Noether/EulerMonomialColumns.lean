/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateTotalDegree
import LeanPool.CCDN.Noether.ShearNormalization

/-! Exact sparse monomial columns of the Euler differential matrix. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The nested polynomial associated with a monomial in two variables is the nested monomial with
outer exponent `m 0` and inner exponent `m 1`. -/
lemma bivariatePolynomialEquiv_monomial {R : Type*} [CommRing R]
    (m : Fin 2 →₀ ℕ) (a : R) :
    bivariatePolynomialEquiv R (MvPolynomial.monomial m a) =
      monomial (m 0) (monomial (m 1) a) := by
  classical
  ext i j
  rw [bivariatePolynomialEquiv_coeff]
  have he : m = Finsupp.cons i (Finsupp.single 0 j) ↔ m 0 = i ∧ m 1 = j := by
    rw [eq_comm, bivariate_exponent_eq_iff]
  by_cases h₀ : m 0 = i <;> by_cases h₁ : m 1 = j <;>
    simp [MvPolynomial.coeff_monomial, coeff_monomial, he, h₀, h₁]

/-- For the monomial equation with outer and inner exponents `s` and `t`, the closed-form operator
sends the pair `(monomial, 0)` with exponents `m`, `n` to a single monomial with coefficient
`n - t`. -/
lemma closedFormOperator_monomial_left {R : Type*} [CommRing R]
    (m n s t : ℕ) :
    closedFormOperator (monomial s (monomial t (1 : R)))
      (monomial m (monomial n 1), 0) =
      monomial (m + s) (monomial (n + t - 1) ((n : R) - t)) := by
  change _ - _ - _ + _ = (monomial (m + s) (monomial (n + t - 1) ((n : R) - t)) : R[X][X])
  simp only [derivative_zero, zero_mul, sub_zero, add_zero,
    bivariateCoefficientDerivative_monomial, one_mul, monomial_mul_monomial, mul_one]
  cases n with
  | zero =>
    simp
  | succ n =>
    cases t with
    | zero =>
      simp
    | succ t =>
      rw [show n + 1 - 1 + (t + 1) = n + 1 + (t + 1) - 1 by omega,
        show n + 1 + (t + 1 - 1) = n + 1 + (t + 1) - 1 by omega,
        ← monomial_sub, ← monomial_sub]

/-- For the monomial equation with outer and inner exponents `s` and `t`, the closed-form operator
sends the pair `(0, monomial)` with exponents `m`, `n` to a single monomial with coefficient
`s - m`. -/
lemma closedFormOperator_monomial_right {R : Type*} [CommRing R]
    (m n s t : ℕ) :
    closedFormOperator (monomial s (monomial t (1 : R)))
      (0, monomial m (monomial n 1)) =
      monomial (m + s - 1) (monomial (n + t) ((s : R) - m)) := by
  change _ - _ - _ + _ = (monomial (m + s - 1) (monomial (n + t) ((s : R) - m)) : R[X][X])
  simp only [map_zero, zero_mul, zero_sub, bivariate_derivative_monomial,
    one_mul, monomial_mul_monomial, mul_one, neg_zero]
  rw [neg_add_eq_sub]
  cases m with
  | zero =>
    simp
  | succ m =>
    cases s with
    | zero =>
      simp
    | succ s =>
      rw [show m + 1 + (s + 1 - 1) = m + 1 + (s + 1) - 1 by omega,
        show m + 1 - 1 + (s + 1) = m + 1 + (s + 1) - 1 by omega,
        ← monomial_sub, ← monomial_sub]

/-- The closed-form operator of a monomial equation applied to a radial monomial pair is a single
monomial, whose coefficient is the degree of the radial pair's homogeneous factor plus two minus
the total degree of the equation. -/
lemma closedFormOperator_monomial_radial {R : Type*} [CommRing R]
    (m n s t : ℕ) :
    closedFormOperator (monomial s (monomial t (1 : R)))
      (monomial m (monomial (n + 1) (1 : R)), -(monomial (m + 1) (monomial n (1 : R)))) =
      monomial (m + s) (monomial (n + t) (((m + n + 2 : ℕ) : R) - (s : R) - t)) := by
  have hp := closedFormOperator_monomial_left (R := R) m (n + 1) s t
  have hq := closedFormOperator_monomial_right (R := R) (m + 1) n s t
  have he : (monomial m (monomial (n + 1) (1 : R)), -(monomial (m + 1) (monomial n (1 : R)))) =
      (monomial m (monomial (n + 1) (1 : R)), (0 : R[X][X])) -
      ((0 : R[X][X]), monomial (m + 1) (monomial n (1 : R))) := by simp
  rw [he, map_sub, hp, hq,
    show n + 1 + t - 1 = n + t by omega,
    show m + 1 + s - 1 = m + s by omega,
    ← monomial_sub, ← monomial_sub]
  congr 2
  push_cast
  ring

end
end CCDN

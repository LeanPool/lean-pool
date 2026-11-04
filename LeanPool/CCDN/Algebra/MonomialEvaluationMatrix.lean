/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Evaluation matrices and auxiliary polynomials

A coefficient vector in the kernel of the monomial evaluation matrix produces a polynomial
vanishing at every specified point. Injectivity of the list of monomials ensures that a
nonzero vector produces a nonzero polynomial.
-/

@[expose] public section

namespace CCDN

open Matrix

/-- The integer polynomial `∑ j, v j * X ^ mon j` with coefficient vector `v` on the list of
monomials `mon`. -/
noncomputable def polynomialOfCoefficients {n N : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (v : Fin N → ℤ) : MvPolynomial (Fin n) ℤ :=
  ∑ j, MvPolynomial.monomial (mon j) (v j)

/-- For an injective list of monomials `mon`, the coefficient of `mon j` in
`polynomialOfCoefficients mon v` is `v j`. -/
theorem coefficient_polynomialOfCoefficients {n N : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (hmon : Function.Injective mon) (v : Fin N → ℤ) (j : Fin N) :
    (polynomialOfCoefficients mon v).coeff (mon j) = v j := by
  classical
  simp [polynomialOfCoefficients, MvPolynomial.coeff_monomial,
    hmon.eq_iff]

/-- For an injective list of monomials, a nonzero coefficient vector gives a nonzero
polynomial. -/
theorem polynomialOfCoefficients_ne_zero {n N : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (hmon : Function.Injective mon) {v : Fin N → ℤ} (hv : v ≠ 0) :
    polynomialOfCoefficients mon v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hc := coefficient_polynomialOfCoefficients mon hmon v j
  rw [h] at hc
  simpa using hc.symm

/-- If every monomial in the list `mon` has degree at most `M`, then
`polynomialOfCoefficients mon v` has total degree at most `M`. -/
theorem totalDegree_polynomialOfCoefficients_le {n N M : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (v : Fin N → ℤ)
    (hdeg : ∀ j, (mon j).degree ≤ M) :
    (polynomialOfCoefficients mon v).totalDegree ≤ M := by
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (hdeg j)

/-- The monomial evaluation matrix, whose entry in row `i` and column `j` is the value of the
monomial `mon j` at the integer point `points i`. -/
noncomputable def evaluationMatrix {n N s : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (points : Fin s → (Fin n → ℤ)) : Matrix (Fin s) (Fin N) ℤ :=
  fun i j => (mon j).prod fun k e => points i k ^ e

/-- The value of `polynomialOfCoefficients mon v` at `points i` is the `i`-th entry of the
product of the monomial evaluation matrix with `v`. -/
theorem eval_polynomialOfCoefficients {n N s : ℕ} (mon : Fin N → (Fin n →₀ ℕ))
    (points : Fin s → (Fin n → ℤ)) (v : Fin N → ℤ) (i : Fin s) :
    MvPolynomial.eval (points i) (polynomialOfCoefficients mon v) =
      (evaluationMatrix mon points *ᵥ v) i := by
  simp [polynomialOfCoefficients, evaluationMatrix, Matrix.mulVec, dotProduct,
    MvPolynomial.eval_monomial, mul_comm]

/-- If the integer point `x` lies in the box of radius `B ≥ 1` and the exponent `e` has degree
at most `M`, then the monomial `x ^ e` has absolute value at most `B ^ M`. -/
theorem abs_monomial_value_le {n M : ℕ} (e : Fin n →₀ ℕ) (x : Fin n → ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hx : InBox x B)
    (he : e.degree ≤ M) :
    |((e.prod (fun i k => x i ^ k) : ℤ) : ℝ)| ≤ B ^ M := by
  have hsum : ∑ i, e i ≤ M := by rwa [Finsupp.degree_eq_sum] at he
  rw [Finsupp.prod_fintype e (fun i k => x i ^ k) (fun _ => pow_zero _)]
  push_cast
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i : Fin n, B ^ e i := by
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
    _ = B ^ (∑ i, e i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ B ^ M := pow_le_pow_right₀ hB hsum

end CCDN

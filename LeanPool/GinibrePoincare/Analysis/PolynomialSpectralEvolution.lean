/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialSpectralEvolution.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorClosure
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

/-! # Spectral evolution in the sum/radius polynomial algebra

These linear maps act on the actual polynomial observables and have the exact
concrete generator eigenvalues. They form an algebraic semigroup. Extension to
a strongly continuous contraction semigroup on the closed L² sector and its
identification with the full Ginibre diffusion are separate analytic goals.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section

/-- Spectral time evolution on the concrete sum/radius polynomial algebra. -/
def polynomialSpectralEvolution (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    sumRadiusPolynomialSpace n →ₗ[ℂ] sumRadiusPolynomialSpace n :=
  (polynomialEigenfunctionBasis n hn).constr ℂ fun i =>
    (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) •
      polynomialEigenfunctionBasis n hn i

@[simp] theorem polynomialSpectralEvolution_basis (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ) (i : PolynomialEigenfunctionData n) :
    polynomialSpectralEvolution n hn t (polynomialEigenfunctionBasis n hn i) =
      (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) •
        polynomialEigenfunctionBasis n hn i := by
  exact Module.Basis.constr_basis _ _ _ _

/-- The algebraic evolution starts at the identity. -/
@[simp] theorem polynomialSpectralEvolution_zero (n : ℕ) (hn : 2 ≤ n) :
    polynomialSpectralEvolution n hn 0 = LinearMap.id := by
  apply (polynomialEigenfunctionBasis n hn).ext
  intro i
  simp

/-- Exact semigroup law on actual polynomial observables. -/
theorem polynomialSpectralEvolution_add (n : ℕ) (hn : 2 ≤ n) (s t : ℝ) :
    polynomialSpectralEvolution n hn (s + t) =
      (polynomialSpectralEvolution n hn s).comp (polynomialSpectralEvolution n hn t) := by
  apply (polynomialEigenfunctionBasis n hn).ext
  intro i
  simp only [LinearMap.comp_apply, polynomialSpectralEvolution_basis, map_smul,
    smul_smul]
  rw [mul_add, Real.exp_add, Complex.ofReal_mul]
  congr 1
  ring

/-- Pointwise evolution of each genuine Hermite–Laguerre observable. -/
theorem polynomialSpectralEvolution_eigenfunction (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ) (i : PolynomialEigenfunctionData n) (z : Configuration n) :
    (polynomialSpectralEvolution n hn t (polynomialEigenfunctionBasis n hn i) :
      Configuration n → ℂ) z =
        (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) *
          polynomialEigenfunction n i z := by
  rw [polynomialSpectralEvolution_basis]
  change (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) *
    (polynomialEigenfunctionBasis n hn i : Configuration n → ℂ) z = _
  rw [polynomialEigenfunctionBasis_apply]

/-- Spectral multipliers are contractions for nonnegative times. -/
theorem polynomialSpectralEvolution_multiplier_le_one (n : ℕ)
    (i : PolynomialEigenfunctionData n) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-eigenvalue n i.a i.b i.m * t) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h : 0 ≤ eigenvalue n i.a i.b i.m := by
    unfold eigenvalue
    positivity
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) ht

/-- Every actual polynomial eigenfunction follows the exact scalar evolution
ODE, pointwise on the concrete configuration space. -/
theorem polynomialSpectralEvolution_eigenfunction_hasDerivAt (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) (z : Configuration n) (t : ℝ) :
    HasDerivAt
      (fun s => (polynomialSpectralEvolution n hn s
        (polynomialEigenfunctionBasis n hn i) : Configuration n → ℂ) z)
      (-(eigenvalue n i.a i.b i.m : ℂ) *
        (polynomialSpectralEvolution n hn t
          (polynomialEigenfunctionBasis n hn i) : Configuration n → ℂ) z) t := by
  simp only [polynomialSpectralEvolution_eigenfunction]
  have h := (((hasDerivAt_id t).const_mul (-eigenvalue n i.a i.b i.m)).exp).ofReal_comp
  convert h.mul_const (polynomialEigenfunction n i z) using 1 <;> simp only [id_eq, mul_one]
  push_cast
  ring

end
end GinibrePoincare

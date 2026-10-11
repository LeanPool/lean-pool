/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

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

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite monomial moment matrices

A complete finite monomial basis spans bounded-degree polynomials over any
commutative semiring. For real coefficients, positivity of its moment matrix
implies positivity on every quadratic square, for any polynomial variable type.
-/

@[expose] public section
namespace PersistentSOS
open MvPolynomial
open scoped BigOperators

/-- A complete finite list of monomials of degree at most two spans every
quadratic polynomial. Repeated entries in the list are allowed. -/
theorem quadratic_eq_sum_monomials {σ R ι : Type*} [CommSemiring R] [Fintype ι]
    (basis : ι → (σ →₀ ℕ))
    (hcover : ∀ d : σ →₀ ℕ, d.sum (fun _ n => n) ≤ 2 → ∃ i, basis i = d)
    (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 2) :
    ∃ x : ι → R, p = ∑ i, x i • (monomial (basis i) (1 : R) : MvPolynomial σ R) := by
  classical
  suffices hmem : p ∈ Submodule.span R
      (Set.range fun i => (monomial (basis i) (1 : R) : MvPolynomial σ R)) by
    obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hmem
    exact ⟨x, hx.symm⟩
  rw [p.as_sum]
  apply Submodule.sum_mem
  intro d hd
  obtain ⟨i, hi⟩ := hcover d ((le_totalDegree hd).trans hp)
  rw [← hi]
  have hmem : (monomial (basis i) (1 : R) : MvPolynomial σ R) ∈
      Submodule.span R (Set.range fun j => (monomial (basis j) (1 : R) : MvPolynomial σ R)) :=
    Submodule.subset_span (Set.mem_range_self i)
  simpa only [smul_monomial, smul_eq_mul, mul_one] using
    Submodule.smul_mem _ (p.coeff (basis i)) hmem

/-- Positivity of the genuine monomial moment matrix implies positivity
on the square of every quadratic polynomial. -/
theorem nonneg_quadratic_square_of_momentMatrix {σ ι : Type*} [Fintype ι]
    (basis : ι → (σ →₀ ℕ))
    (hcover : ∀ d : σ →₀ ℕ, d.sum (fun _ n => n) ≤ 2 → ∃ i, basis i = d)
    (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ)
    (hpsd : ∀ x : ι → ℝ,
      0 ≤ ∑ i, ∑ j, x i * L (monomial (basis i + basis j) 1) * x j)
    (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ 2) : 0 ≤ L (p ^ 2) := by
  classical
  obtain ⟨x, rfl⟩ := quadratic_eq_sum_monomials basis hcover p hp
  convert hpsd x using 1
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_sum, smul_mul_smul_comm, map_smul,
    monomial_mul_monomial, one_mul, smul_eq_mul]
  congr 1
  ext i
  congr 1
  ext j
  ring

end PersistentSOS

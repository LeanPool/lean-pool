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

public import LeanPool.PersistentSOS.PSD
public import LeanPool.PersistentSOS.Definitions

/-!
# Linear moment functionals and finite Gram forms

A single exponent-indexed function supplies every occurrence of a monomial.
-/


@[expose] public section

namespace PersistentSOS

open scoped BigOperators

/-- Exponent vectors of ordinary polynomials in fourteen variables. -/
abbrev Exponent := Fin 14 →₀ ℕ

/-- A base - five key used only to index the explicit finite moment table. -/
def exponentKey (d : Exponent) : ℕ := ∑ i : Fin 14, d i * 5 ^ i.val

@[simp] theorem exponentKey_zero : exponentKey 0 = 0 := by
  simp [exponentKey]

@[simp] theorem exponentKey_add (d e : Exponent) :
    exponentKey (d + e) = exponentKey d + exponentKey e := by
  simp [exponentKey, add_mul, Finset.sum_add_distrib]

@[simp] theorem exponentKey_single (i : Fin 14) (n : ℕ) :
    exponentKey (Finsupp.single i n) = n * 5 ^ i.val := by
  classical
  simp [exponentKey, Finsupp.single_apply, ite_mul]

/-- Extend any moment table linearly to ordinary real multivariate polynomials. -/
noncomputable def momentLinearMap (m : ℕ → ℤ) : Poly →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ (fun d : Exponent => (m (exponentKey d) : ℝ) / 1000000000)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem momentLinearMap_monomial (m : ℕ → ℤ) (d : Exponent) (c : ℝ) :
    momentLinearMap m (MvPolynomial.monomial d c) =
      c * (m (exponentKey d) : ℝ) / 1000000000 := by
  simp [momentLinearMap, LinearMap.comp_apply, MvPolynomial.monomial,
    Finsupp.linearCombination_single, smul_eq_mul,
    mul_div_assoc]

/-- A block - diagonal collection of nonnegative quadratic forms is nonnegative. -/
theorem block_nonneg {κ : Type*} [Fintype κ] (size : κ → ℕ)
    (A : (k : κ) → Fin (size k) → Fin (size k) → ℝ)
    (hA : ∀ k, IsPSD (A k)) (x : (k : κ) × Fin (size k) → ℝ) :
    0 ≤ ∑ k, quadraticForm (A k) (fun i => x ⟨k, i⟩) := by
  exact Finset.sum_nonneg (fun k _ => hA k _)

end PersistentSOS

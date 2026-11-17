/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MultivariateComplexHermite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NormalizedComplexHermite
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Multivariate normalized complex Hermite functions

This file evaluates the normalized two-variable polynomial on the complex
diagonal and forms the finite tensor product over coordinates.  No analytic
completion is used at this stage.
-/


@[expose] public section


namespace GinibrePoincare

open scoped BigOperators ComplexConjugate

namespace ComplexHermite

@[simp] theorem oneDimNormalization_zero (n : ℕ) :
    oneDimNormalization n 0 = 1 := by
  simp [oneDimNormalization]

/-- Diagonal evaluation of the normalized univariate complex Hermite
polynomial. -/
noncomputable def normalizedEval (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![z, conj z] (normalized n hn p q)

@[simp] theorem normalizedEval_zero_right (n : ℕ) (hn : 0 < n)
    (p : ℕ) (z : ℂ) :
    normalizedEval n hn p 0 z = (oneDimNormalization n p : ℂ) * z ^ p := by
  simp [normalizedEval, normalized, oneDimNormalization_zero, raw_zero_right, Z]

@[simp] theorem normalizedEval_zero_left (n : ℕ) (hn : 0 < n)
    (q : ℕ) (z : ℂ) :
    normalizedEval n hn 0 q z =
      (oneDimNormalization n q : ℂ) * (conj z) ^ q := by
  simp [normalizedEval, normalized, oneDimNormalization_zero, raw_zero_left, W]

theorem normalizedEval_zero_zero (n : ℕ) (hn : 0 < n) (z : ℂ) :
    normalizedEval n hn 0 0 z = 1 := by
  simp

/-- A multivariate normalized complex Hermite function, indexed by two
multi-indices and defined as the coordinatewise tensor product. -/
noncomputable def multivariateNormalized (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (z : Fin n → ℂ) : ℂ :=
  ∏ i, normalizedEval n hn (p i) (q i) (z i)

@[simp] theorem multivariateNormalized_zero_right (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) (z : Fin n → ℂ) :
    multivariateNormalized n hn p 0 z =
      ∏ i, (oneDimNormalization n (p i) : ℂ) * (z i) ^ p i := by
  simp [multivariateNormalized]

@[simp] theorem multivariateNormalized_zero_left (n : ℕ) (hn : 0 < n)
    (q : Fin n → ℕ) (z : Fin n → ℂ) :
    multivariateNormalized n hn 0 q z =
      ∏ i, (oneDimNormalization n (q i) : ℂ) * (conj (z i)) ^ q i := by
  simp [multivariateNormalized]

theorem multivariateNormalized_zero_zero (n : ℕ) (hn : 0 < n)
    (z : Fin n → ℂ) :
    multivariateNormalized n hn 0 0 z = 1 := by
  simp [multivariateNormalized]

/-- Every normalized diagonal Hermite function is continuous. -/
theorem continuous_normalizedEval (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    Continuous (normalizedEval n hn p q) := by
  unfold normalizedEval
  apply (MvPolynomial.continuous_eval (normalized n hn p q)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_id
  · exact Complex.continuous_conj

/-- A finite coordinate product of normalized Hermite functions is
continuous on `ℂⁿ`. -/
theorem continuous_multivariateNormalized (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    Continuous (multivariateNormalized n hn p q) := by
  unfold multivariateNormalized
  apply continuous_finsetProd Finset.univ
  intro i hi
  exact (continuous_normalizedEval n hn (p i) (q i)).comp (continuous_apply i)

end ComplexHermite
end GinibrePoincare

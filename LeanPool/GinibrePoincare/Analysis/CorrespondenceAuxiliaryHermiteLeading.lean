/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryHermiteLeading.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteMonomialSpan
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-!
# Correspondence auxiliary Hermite leading

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `normalized_leading_coefficient`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare.ComplexHermite
noncomputable section

/-- The coefficient of the leading mixed monomial in the raw polynomial is
exactly one, not just a nonzero triangularity certificate. -/
theorem raw_leading_coefficient (ρ : ℝ) (p q : ℕ) :
    (raw ρ p q).coeff
      (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) = 1 := by
  classical
  unfold raw
  rw [MvPolynomial.coeff_sum]
  simp only [Z, W, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkbound : k ≤ p ∧ k ≤ q := by
      have h := Finset.mem_range.mp hk
      omega
    have hne : Finsupp.single (0 : Fin 2) (p-k) + Finsupp.single 1 (q-k) ≠
        Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q := by
      intro he
      have h := congrArg (fun a : Fin 2 →₀ ℕ => a 0) he
      simp at h
      omega
    exact ite_eq_right hne
  · simp

/-- Exact leading coefficient of the paper's normalized complex Hermite
polynomial (Appendix B's triangular normalization). -/
theorem normalized_leading_coefficient (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    (normalized n hn p q).coeff
      (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) =
      ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) := by
  unfold normalized
  rw [MvPolynomial.coeff_C_mul, raw_leading_coefficient, mul_one]

end
end GinibrePoincare.ComplexHermite

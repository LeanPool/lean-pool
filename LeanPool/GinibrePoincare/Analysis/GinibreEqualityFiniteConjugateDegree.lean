/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityFiniteConjugateDegree.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityConjugatePolynomialDegree
public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry

/-!
# Ginibre Equality Finite Conjugate Degree
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite

/-- Every genuine finite homogeneous quotient has a nonzero conjugate mode
at its own degree: any finite conjugate support bound is at least that degree. -/
theorem ginibreEquality_finite_quotient_conjugate_degree_bound {n : ℕ} (hn : 0 < n)
    (r : ℕ) (h : Lp ℂ 2 (ginibreMeasure n)) (hh : IsFiniteHomogeneousQuotientVector hn r h)
    (b : HermiteMultiIndex n →₀ ℂ) (K : ℕ)
    (hb : ∀ pq ∈ b.support, totalAntiDegree pq ≤ K)
    (hfinite : normalizedVandermondeL2 n hn (star h) = finiteHermiteCombination n hn b) :
    r ≤ K := by
  rcases hh with ⟨S, c, hAlt, Q, hdegree, hpolyAlt, hne, hfactor, hsum, hphase, rfl⟩
  have hhom : MvPolynomial.IsHomogeneous
      (finiteZeroAntiholomorphicHermitePolynomial n S c) (vandermondeDegree n+r) :=
    by
      apply isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree
      exact hdegree
  have hQne : Q≠0 := by
    intro hz
    rw [hz, mul_zero] at hfactor
    exact hne hfactor
  have hdegP := hhom.totalDegree hne
  have hdegV := (isHomogeneous_polynomialVandermonde n).totalDegree (polynomialVandermonde_ne_zero
    n)
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain (polynomialVandermonde_ne_zero n) hQne
  rw [←hfactor, hdegP, hdegV] at hdeg
  have hbQ := ginibreEquality_conjugate_polynomial_degree_bound hn _ Q
    (finiteHomogeneousQuotientL2_coeFn hn S c hAlt Q hsum) b K hb hfinite
  omega

end GinibrePoincare

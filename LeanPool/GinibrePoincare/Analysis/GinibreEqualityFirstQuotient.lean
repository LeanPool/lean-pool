/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityFirstQuotient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityPolynomial
public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry
public import LeanPool.GinibrePoincare.Analysis.GinibreCoordinateSumL2

/-!
# Ginibre Equality First Quotient
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped BigOperators

/-- Every genuine finite homogeneous holomorphic quotient in the first positive
sector is a scalar multiple of the coordinate sum, with no polynomial-shape
assumption imposed on its quotient. -/
theorem ginibreEquality_finite_first_quotient_ae_coordinateSum {n : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n)) (hh : IsFiniteHomogeneousQuotientVector hn 1 h) :
    ∃ c : ℂ, (h : Configuration n → ℂ) =ᵐ[ginibreMeasure n] fun z => c * coordinateSum z := by
  rcases hh with ⟨S, c, hAlt, Q, hdegree, hpolyAlt, hne, hfactor, hsum, hphase, rfl⟩
  have hhom : MvPolynomial.IsHomogeneous
      (finiteZeroAntiholomorphicHermitePolynomial n S c) (vandermondeDegree n + 1) := by
    apply isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree
    exact hdegree
  have hQne : Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfactor
    exact hne hfactor
  have hdegP := hhom.totalDegree hne
  have hdegV := (isHomogeneous_polynomialVandermonde n).totalDegree (polynomialVandermonde_ne_zero
    n)
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain (polynomialVandermonde_ne_zero n) hQne
  rw [← hfactor, hdegP, hdegV] at hdeg
  have hQdeg : Q.totalDegree ≤ 1 := by omega
  have hQsym := isSymmetric_quotient_of_vandermonde_mul_alternating
    (by rwa [← hfactor])
  obtain ⟨a, b, hQ⟩ := ginibreEquality_symmetric_affine_eval hn Q hQsym hQdeg
  let z : Configuration n := fun i => ((i : ℕ) : ℂ)
  have hz : vandermonde z ≠ 0 := (vandermonde_ne_zero_iff _).2 (fun i j hij => by
    exact Fin.ext (by exact_mod_cast Complex.ofReal_injective hij))
  have hp := hphase (-1) (by norm_num) z hz
  rw [hQ, hQ] at hp
  have hS : coordinateSum (globalPhase (-1) z) = -coordinateSum z := by
    simp [coordinateSum, globalPhase]
  rw [hS] at hp
  simp only [pow_one, neg_one_mul, mul_neg] at hp
  have ha : a = 0 := by
    have h2 : (2 : ℂ) * a = 0 := by linear_combination hp
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  refine ⟨(groundStateNormalization n : ℂ) * b, ?_⟩
  filter_upwards [finiteHomogeneousQuotientL2_coeFn hn S c hAlt Q hsum] with x hx
  rw [hx, hQ, ha, zero_add]
  ring

/-- The entire closed first holomorphic quotient sector is one dimensional,
including all its L² limits. -/
theorem ginibreEquality_first_quotient_closedSpan_le_coordinateSum {n : ℕ} (hn : 0 < n)
    (s : ginibreSymmetricL2 n)
    (hs : (s.val : Configuration n → ℂ) =ᵐ[ginibreMeasure n] coordinateSum) :
    (ginibreFiniteQuotientDegreeClosedSpan n 1 hn).toSubmodule ≤
      Submodule.span ℂ ({s.val} : Set (Lp ℂ 2 (ginibreMeasure n))) := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    intro h hh
    obtain ⟨c, hc⟩ := ginibreEquality_finite_first_quotient_ae_coordinateSum hn h hh
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply Lp.ext
    filter_upwards [hc, hs, Lp.coeFn_smul c s.val] with z hz hsz hsmul
    rw [hsmul]
    change c * s.val z = h z
    rw [hsz, hz]
  · exact Submodule.isClosed_of_finiteDimensional
      (Submodule.span ℂ ({s.val} : Set (Lp ℂ 2 (ginibreMeasure n))))

/-- Exhaustive actual L² classification of the closed first positive
holomorphic quotient sector. -/
theorem ginibreEquality_first_quotient_closedSpan_ae_coordinateSum {n : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n)) (hh : h ∈ ginibreFiniteQuotientDegreeClosedSpan n 1 hn) :
    ∃ c : ℂ, (h : Configuration n → ℂ) =ᵐ[ginibreMeasure n] fun z => c * coordinateSum z := by
  obtain ⟨s, hs⟩ := ginibreSymmetricL2_coordinateSum n hn
  have hm := ginibreEquality_first_quotient_closedSpan_le_coordinateSum hn s hs hh
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  refine ⟨c, ?_⟩
  rw [← hc]
  filter_upwards [hs, Lp.coeFn_smul c s.val] with z hz hsmul
  rw [hsmul]
  change c * s.val z = _
  rw [hz]

end GinibrePoincare

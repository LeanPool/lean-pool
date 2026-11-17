/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityConjugateModeDetection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityFiniteConjugateDegree
public import LeanPool.GinibrePoincare.Analysis.GaussianHermitePhaseSpectrum
public import LeanPool.GinibrePoincare.Analysis.GaussianVandermondePhase

/-!
# Ginibre Equality Conjugate Mode Detection
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite
open scoped ComplexConjugate

/-- Vanishing actual high anti-degree projections implies vanishing every
corresponding Hilbert-basis coefficient. -/
theorem gaussianHermiteCoefficient_eq_zero_of_high_projections {n : ℕ} (hn : 0 < n)
    (x : Lp ℂ 2 (complexGaussianMeasure n)) (K : ℕ)
    (hx : ∀ d : ℕ, K<d → hermiteAntiDegreeProjection n hn d x=0)
    (pq : HermiteMultiIndex n) (hpq : K<totalAntiDegree pq) :
    gaussianHermiteCoefficient hn x pq=0 := by
  have hi := inner_basis_gaussianHermiteMode hn x (totalAntiDegree pq) pq
  rw [ite_eq_left rfl, gaussianHermiteMode_eq_antiDegreeProjection,
    hx _ hpq, inner_zero_right] at hi
  exact hi.symm

/-- Bounded conjugate anti modes of a genuine homogeneous phase vector
are an actual finite Gaussian polynomial, with no polynomial assumption. -/
theorem ginibreEquality_phase_conjugate_low_modes_finite {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hphase : ∀ (u : ℂ) (hu : ‖u‖ = 1), ginibreGlobalPhaseL2 hn u hu h = u ^ r • h)
    (K : ℕ)
    (hanti : ∀ d : ℕ, K<d → hermiteAntiDegreeProjection n hn d
      (normalizedVandermondeL2 n hn (star h))=0) :
    ∃ b : HermiteMultiIndex n →₀ ℂ,
      normalizedVandermondeL2 n hn (star h)=finiteHermiteCombination n hn b ∧
      ∀ pq ∈ b.support, totalAntiDegree pq≤K := by
  have hc : ∀ (u : ℂ) (hu : ‖u‖=1), ginibreGlobalPhaseL2 hn u hu (star h)=
      (u^0*(conj u)^r)•star h := by
    intro u hu
    simpa using ginibreGlobalPhaseL2_star_eigen hn h hphase u hu
  have hG := gaussianGlobalPhaseL2_normalizedVandermonde_character hn (star h) hc
  obtain ⟨b, hb, hs⟩ := gaussian_mixed_phase_finite_reconstruction hn
    (normalizedVandermondeL2 n hn (star h)) (by simpa using hG)
    (gaussianHermiteCoefficient_eq_zero_of_high_projections hn _ K hanti)
  exact ⟨b, hb.symm, fun pq hpq => (hs pq hpq).1⟩

/-- Actual finite homogeneous quotient degree is detected by its conjugate
Gaussian projections. Thus degrees above K cannot have only anti modes ≤K. -/
theorem ginibreEquality_finite_quotient_degree_le_of_conjugate_modes {n : ℕ} (hn : 0 < n)
    (r : ℕ) (h : Lp ℂ 2 (ginibreMeasure n)) (hh : IsFiniteHomogeneousQuotientVector hn r h)
    (K : ℕ)
    (hanti : ∀ d : ℕ, K<d → hermiteAntiDegreeProjection n hn d
      (normalizedVandermondeL2 n hn (star h))=0) : r≤K := by
  have hp : ∀ (u : ℂ) (hu : ‖u‖=1), ginibreGlobalPhaseL2 hn u hu h=u^r•h := by
    rcases hh with ⟨S, c, hAlt, Q, hdegree, hpolyAlt, hne, hfactor, hsum, hphase, rfl⟩
    exact finiteHomogeneousQuotientL2_mem_phaseDegree hn S c hAlt Q hsum hphase
  obtain ⟨b, hb, hbs⟩ := ginibreEquality_phase_conjugate_low_modes_finite hn h hp K hanti
  exact ginibreEquality_finite_quotient_conjugate_degree_bound hn r h hh b K hbs hb

end GinibrePoincare

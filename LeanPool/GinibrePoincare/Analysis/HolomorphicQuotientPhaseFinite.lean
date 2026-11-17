/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HolomorphicQuotientPhaseFinite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianHolomorphicPhasePolynomial
public import LeanPool.GinibrePoincare.Analysis.GaussianVandermondePhase
public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry

/-! # Finite reconstruction of actual closed homogeneous quotient vectors -/


@[expose] public section


open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
open ComplexHermite
noncomputable section

/-- Every nonzero vector of the actual closed homogeneous quotient space is
itself a finite homogeneous quotient, without a polynomial assumption. -/
theorem ginibre_holomorphic_phase_nonzero_isFinite {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hhol : h ∈ ginibreHolomorphicAmbientClosedSpan n hn)
    (hchar : h ∈ ginibreHolomorphicPhaseDegree n r hn) (hne : h ≠ 0) :
    IsFiniteHomogeneousQuotientVector hn r h := by
  obtain ⟨s, hs, hsv⟩ := hhol
  change s.val = h at hsv
  have hg0 : normalizedVandermondeL2 n hn h ∈ hermiteAntiDegreeClosedSpan n hn 0 := by
    have hmap : vandermondeSymmetricAlternatingEquiv n hn s ∈
        gaussianAlternatingZeroModeClosedSpan n hn := by
      change vandermondeSymmetricAlternatingEquiv n hn s ∈
        (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
      rw [← map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
      exact ⟨s, hs, rfl⟩
    have hz := gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode n hn hmap
    change normalizedVandermondeL2 n hn s.val ∈ hermiteAntiDegreeClosedSpan n hn 0 at hz
    rwa [hsv] at hz
  have hphase : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn h) =
        u ^ (vandermondeDegree n + r) • normalizedVandermondeL2 n hn h := by
    have hx := hchar
    simpa using gaussianGlobalPhaseL2_normalizedVandermonde_character (r := r) (s := 0) hn h
      (by intro u hu; simpa using hx u hu)
  obtain ⟨S, c, hf, hd⟩ := gaussian_holomorphic_phase_finiteZero_reconstruction hn _ hg0 hphase
  have hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n := by
    rw [hf, ← hsv]
    exact normalizedVandermondeL2_mem_gaussianAlternating hn s
  have hPalt := finiteZeroHermiteL2_alternating_polynomial hn S c hAlt
  have hPne : finiteZeroAntiholomorphicHermitePolynomial n S c ≠ 0 := by
    intro hP
    have hf0 : finiteZeroHermiteL2 n hn S c = 0 := by
      apply Lp.ext
      filter_upwards [finiteZeroHermiteL2_coeFn n hn S c,
        Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hz hzero
      rw [hz, hzero]
      rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z, hP]
      simp
    apply hne
    apply (normalizedVandermondeL2 n hn).injective
    rw [← hf, hf0, map_zero]
  obtain ⟨Q, hQsym, hfactor, hle, hQphase⟩ :=
    homogeneous_alternating_polynomial_division
      (isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree S c hd) hPalt hPne
  have hsEq : finiteHomogeneousQuotientL2 hn S c hAlt = s := by
    apply (vandermondeSymmetricAlternatingEquiv n hn).injective
    rw [finiteHomogeneousQuotientL2, LinearIsometryEquiv.apply_symm_apply]
    apply Subtype.ext
    change finiteZeroHermiteL2 n hn S c = normalizedVandermondeL2 n hn s.val
    rw [hsv]
    exact hf
  refine ⟨S, c, hAlt, Q, hd, hPalt, hPne, hfactor, ?_, ?_, ?_⟩
  · intro z
    rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z,
      hfactor, map_mul, eval_polynomialVandermonde]
  · simpa using hQphase
  · rw [hsEq]
    exact hsv.symm

/-- Nonzero vectors of the entire closed homogeneous quotient degree space
are genuine finite homogeneous quotients. -/
theorem ginibre_quotientDegreeClosedSpan_nonzero_isFinite {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hh : h ∈ ginibreFiniteQuotientDegreeClosedSpan n r hn) (hne : h ≠ 0) :
    IsFiniteHomogeneousQuotientVector hn r h :=
  ginibre_holomorphic_phase_nonzero_isFinite hn h
    (ginibreFiniteQuotientDegreeClosedSpan_le_holomorphicAmbient n r hn hh)
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n r hn hh) hne

/-- Within the actual holomorphic space, the phase character completely
identifies a closed homogeneous quotient degree. -/
theorem ginibre_holomorphic_phase_mem_quotientDegree {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hhol : h ∈ ginibreHolomorphicAmbientClosedSpan n hn)
    (hchar : h ∈ ginibreHolomorphicPhaseDegree n r hn) :
    h ∈ ginibreFiniteQuotientDegreeClosedSpan n r hn := by
  by_cases hz : h = 0
  · rw [hz]; exact Submodule.zero_mem _
  · apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ginibre_holomorphic_phase_nonzero_isFinite hn h hhol hchar hz

end
end GinibrePoincare

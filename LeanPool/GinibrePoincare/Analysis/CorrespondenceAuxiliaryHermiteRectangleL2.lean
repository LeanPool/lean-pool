/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryHermiteRectangleL2.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianHermiteMoments
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-!
# Correspondence auxiliary Hermite rectangle L 2

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `multivariateMixedMonomialL2_mem_hermite_rectangle`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Rectangular triangular inversion survives passage to the actual Gaussian
L² quotient, with each coordinate bound preserved. -/
theorem multivariateMixedMonomialL2_mem_hermite_rectangle (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    multivariateMixedMonomialL2 n hn p q ∈ Submodule.span ℂ
      {v | ∃ a b : Fin n → ℕ, (∀ i, a i ≤ p i) ∧ (∀ i, b i ≤ q i) ∧
        v = multivariateNormalizedL2 n hn a b} := by
  let S := Submodule.span ℂ
    {v | ∃ a b : Fin n → ℕ, (∀ i, a i ≤ p i) ∧ (∀ i, b i ≤ q i) ∧
      v = multivariateNormalizedL2 n hn a b}
  have lift : ∀ {F : Configuration n → ℂ},
      F ∈ multivariateNormalizedRectangleSpan n hn p q →
      ∃ hmem : MemLp F 2 (complexGaussianMeasure n), hmem.toLp F ∈ S := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hg
      refine ⟨memLp_two_multivariateNormalized n hn a b,?_⟩
      have he : (memLp_two_multivariateNormalized n hn a b).toLp
          (multivariateNormalized n hn a b) = multivariateNormalizedL2 n hn a b := by
        apply Lp.ext
        filter_upwards [(memLp_two_multivariateNormalized n hn a b).coeFn_toLp,
          multivariateNormalizedL2_coeFn n hn a b] with z h1 h2
        exact h1.trans h2.symm
      rw [he]
      exact Submodule.subset_span ⟨a, b, ha, hb, rfl⟩
    | zero => exact ⟨MemLp.zero, by simp⟩
    | add f g hf hg ihf ihg =>
      obtain ⟨hfm, hfs⟩ := ihf
      obtain ⟨hgm, hgs⟩ := ihg
      refine ⟨hfm.add hgm,?_⟩
      rw [MemLp.toLp_add hfm hgm]
      exact S.add_mem hfs hgs
    | smul c f hf ih =>
      obtain ⟨hfm, hfs⟩ := ih
      refine ⟨hfm.const_smul c,?_⟩
      rw [MemLp.toLp_const_smul c hfm]
      exact S.smul_mem c hfs
  have hpoint : (fun z : Configuration n => ∏ i, z i ^ p i * conj (z i) ^ q i) ∈
      multivariateNormalizedRectangleSpan n hn p q := by
    rw [multivariateNormalizedRectangleSpan_eq_mixedMonomialRectangleSpan]
    exact Submodule.subset_span ⟨p, q, fun _ => le_rfl, fun _ => le_rfl, rfl⟩
  obtain ⟨hm, hs⟩ := lift hpoint
  have he : hm.toLp _ = multivariateMixedMonomialL2 n hn p q := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp,
      (memLp_two_multivariateMixedMonomial n hn p q).coeFn_toLp] with z h1 h2
    exact h1.trans h2.symm
  simpa only [he] using hs

end
end GinibrePoincare

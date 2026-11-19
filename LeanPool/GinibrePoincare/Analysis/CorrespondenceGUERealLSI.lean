/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUERealLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEProjection
/-!
# Correspondence GUE real LSI

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueOrderedMeasure_square_lsi`, `gueOrderedMeasure_boundedC1_square_lsi`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

theorem gueOrderedMeasure_boundedC1_square_lsi {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (K : ℝ≥0) (hK : LipschitzWith K f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    squareEntropy (gueOrderedMeasure n) f ≤
      (2/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n := by
  have hL := gueDoubledOrderedMeasure_boundedC1_square_lsi hn
    (f ∘ gueRealProjection n) (hf.comp ((gueRealProjection_contDiff n).of_le (by norm_num)))
    (K*‖gueRealProjectionLinear n‖₊)
    (hK.comp (gueRealProjectionLinear n).lipschitzWith) C (fun x => hb _)
  have he : squareEntropy (gueDoubledOrderedMeasure n) (f ∘ gueRealProjection n)=
      squareEntropy (gueOrderedMeasure n) f := by
    unfold squareEntropy
    simp only [Function.comp_apply]
    rw [gueOrderedMeasure_real_marginal_integral hn (fun x => f x^2*Real.log (f x^2)),
      gueOrderedMeasure_real_marginal_integral hn (fun x => f x^2)]
  rw [he] at hL
  simp_rw [gueRealProjection_gradient_norm_sq n f hf] at hL
  rw [gueOrderedMeasure_real_marginal_integral hn (fun x => ‖gradient f x‖^2)] at hL
  exact hL

theorem gueOrderedMeasure_square_lsi {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) :
    squareEntropy (gueOrderedMeasure n) f ≤
      (2/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n := by
  obtain ⟨M, hM⟩ := hf.continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support (hs.fderiv ℝ)
  let K : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hLip : LipschitzWith K f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by norm_num)) (fun x => by
      change ‖fderiv ℝ f x‖≤max M 0
      exact (hM x).trans (le_max_left _ _))
  obtain ⟨C, hC⟩ := hf.continuous.norm.bddAbove_range_of_hasCompactSupport hs.norm
  exact gueOrderedMeasure_boundedC1_square_lsi hn f hf K hLip C (fun x => hC (mem_range_self x))

end
end GinibrePoincare

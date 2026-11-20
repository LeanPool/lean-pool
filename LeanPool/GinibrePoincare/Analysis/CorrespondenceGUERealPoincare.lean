/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUERealPoincare.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUERealLSI
public import LeanPool.GinibrePoincare.Analysis.SquareEntropyLinearization
/-!
# Correspondence GUE real Poincare

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueOrderedMeasure_poincare_compactC1`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

theorem gueOrderedMeasure_poincare_compactC1 {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) :
    (∫x, f x^2 ∂gueOrderedMeasure n)-(∫x, f x ∂gueOrderedMeasure n)^2 ≤
      (1/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n := by
  let := gueOrderedMeasure_probability hn
  obtain ⟨M, hM⟩ := hf.continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support (hs.fderiv ℝ)
  let K : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hLip : LipschitzWith K f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by norm_num)) (fun x => by
      change ‖fderiv ℝ f x‖≤max M 0
      exact (hM x).trans (le_max_left _ _))
  obtain ⟨C, hC⟩ := hf.continuous.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hb (x) : ‖f x‖≤C := hC (mem_range_self x)
  have hlin := squareEntropy_affine_bound_variance (gueOrderedMeasure n) f hf.continuous.measurable
    C ((norm_nonneg (f 0)).trans (hb 0)) (by simpa only [Real.norm_eq_abs] using hb)
    ((2/(n : ℝ))*∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n) (by
      intro t
      have hft : ContDiff ℝ 1 (fun x => 1+t*f x) := contDiff_const.add (contDiff_const.mul hf)
      have hdt (x) : fderiv ℝ (fun x => 1+t*f x) x = t • fderiv ℝ f x := by
        rw [fderiv_const_add, fderiv_const_mul (hf.differentiable (by norm_num) x)]
      have hLipT : LipschitzWith (‖t‖₊*K) (fun x => 1+t*f x) :=
        lipschitzWith_of_nnnorm_fderiv_le (hft.differentiable (by norm_num)) (fun x => by
          rw [hdt, nnnorm_smul]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          change ‖fderiv ℝ f x‖≤max M 0
          exact (hM x).trans (le_max_left _ _))
      have hbT (x) : ‖1+t*f x‖≤1+|t| *C := by
        calc
          _ ≤ ‖(1 : ℝ)‖+‖t*f x‖ := norm_add_le _ _
          _ = 1+|t| *‖f x‖ := by rw [norm_mul, Real.norm_eq_abs t]; norm_num
          _ ≤ 1+|t| *C := add_le_add_right (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t)) _
      have hL := gueOrderedMeasure_boundedC1_square_lsi hn _ hft _ hLipT _ hbT
      have hg (x) : gradient (fun x => 1+t*f x) x=t • gradient f x := by
        unfold gradient
        rw [fderiv_const_add, fderiv_const_mul (hf.differentiable (by norm_num) x)]
        simp only [map_smul]
      simp_rw [hg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hL
      rw [integral_const_mul] at hL
      convert hL using 1; ring)
  convert hlin using 1; ring

end
end GinibrePoincare

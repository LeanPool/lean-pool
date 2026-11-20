/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEOptimality.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEEndpoints
/-!
# Correspondence GUE optimality

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueFull_poincare_constant_optimal`, `gueFull_lsi_constant_optimal`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem gueFull_poincare_constant_optimal {n : ℕ} (hn : 0 < n) (c : ℝ)
    (hc : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
      (∀σ x, f (guePermute n σ x)=f x) → MemLp f 2 (gueFullMeasure n) →
      MemLp (gradient f) 2 (gueFullMeasure n) →
      (∫x, f x^2 ∂gueFullMeasure n)-(∫x, f x ∂gueFullMeasure n)^2≤
        c*(∫x, ‖gradient f x‖^2 ∂gueFullMeasure n)) : 1/(n : ℝ)≤c := by
  let := gueFullMeasure_probability hn
  have h := hc (gueCenterCoordinate n) ((gueCenterCoordinate_contDiff n).of_le (by simp))
    (gueCenterCoordinate_symmetric n) (gueCenterCoordinate_memLp hn)
        (gueCenterCoordinate_gradient_memLp hn)
  rw [gueCenterCoordinate_poincare_equality hn] at h
  simpa only [gueCenterCoordinate_gradient, gueCenterUnit_norm hn, one_pow, integral_const,
    probReal_univ, smul_eq_mul, mul_one] using h

theorem gueFull_lsi_constant_optimal {n : ℕ} (hn : 0 < n) (c : ℝ)
    (hc : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
      (∀σ x, f (guePermute n σ x)=f x) → MemLp f 2 (gueFullMeasure n) →
      MemLp (gradient f) 2 (gueFullMeasure n) →
      squareEntropy (gueFullMeasure n) f≤c*(∫x, ‖gradient f x‖^2 ∂gueFullMeasure n)) :
    2/(n : ℝ)≤c := by
  have h := hc (gueLSIWitness n) ((gueLSIWitness_contDiff n).of_le (by simp))
    (gueLSIWitness_symmetric n) (gueLSIWitness_memLp hn) (gueLSIWitness_gradient_memLp hn)
  rw [gueLSIWitness_lsi_equality hn, gueLSIWitness_gradient_energy hn] at h
  exact (mul_le_mul_iff_left₀ (by positivity : 0<(1/4 : ℝ)*Real.exp ((gueCenterVariance n :
                                    ℝ)/2))).mp h

end
end GinibrePoincare

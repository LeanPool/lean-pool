/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticGaussianSquareMoments.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGaussianFourthMoment

/-! # Exact second-moment and variance estimates for Gaussian squared increments -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreGaussian_square_memLp_two (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := integrable_pow_of_mem_interior_integrableExpSet (X := id) (μ := gaussianReal 0 v) (by
      simp) 4
  simpa only [id_eq, ← pow_mul] using h

theorem ginibreGaussian_square_variance (v : ℝ≥0) :
    variance (fun x : ℝ => x^2) (gaussianReal 0 v) = 2*(v : ℝ)^2 := by
  rw [variance_eq_sub (ginibreGaussian_square_memLp_two v)]
  simp only [Pi.pow_apply, ← pow_mul]
  rw [ginibreGaussian_centered_fourthMoment, ginibreGaussian_secondMoment]
  norm_num
  ring

theorem ginibreGaussian_hasLaw_square_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0) (hLaw : HasLaw X (gaussianReal 0 v) P) :
    MemLp (fun ω => (X ω)^2) 2 P := by
  have h := ginibreGaussian_square_memLp_two v
  rw [← hLaw.map_eq] at h
  exact (memLp_map_measure_iff (by fun_prop) hLaw.aemeasurable).mp h

theorem ginibreGaussian_hasLaw_square_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0) (hLaw : HasLaw X (gaussianReal 0 v) P) :
    (∫ ω, (X ω)^2 ∂P) = (v : ℝ) := by
  have h := hLaw.integral_comp (f := fun x : ℝ => x^2) (by fun_prop)
  simpa only [Function.comp_apply, ginibreGaussian_secondMoment, zero_pow (by
      norm_num : (2 : ℕ) ≠ 0), add_zero] using h

theorem ginibreGaussian_hasLaw_square_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0) (hLaw : HasLaw X (gaussianReal 0 v) P) :
    variance (fun ω => (X ω)^2) P = 2*(v : ℝ)^2 := by
  have h := ginibreGaussian_square_variance v
  rw [← hLaw.map_eq, variance_map (by fun_prop) hLaw.aemeasurable] at h
  exact h

end
end GinibrePoincare

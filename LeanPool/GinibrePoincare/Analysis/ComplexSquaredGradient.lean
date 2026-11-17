/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/ComplexSquaredGradient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient

/-! # Actual gradient bound for squared complex observables -/


@[expose] public section


open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

/-- Total squared norm of the complex directional derivatives over the real coordinate basis. -/
def complexDirectionalEnergy {n : ℕ} (F : Configuration n → ℂ) (z : Configuration n) : ℝ :=
  ∑ k : Fin n × Fin 2, Complex.normSq (fderiv ℝ F z (ginibreCoordinateDirection k))

theorem complexDirectionalEnergy_nonneg {n : ℕ} (F : Configuration n → ℂ) (z : Configuration n) :
    0 ≤ complexDirectionalEnergy F z := Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem continuous_complexDirectionalEnergy {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ ∞ F) : Continuous (complexDirectionalEnergy F) := by
  apply continuous_finsetSum
  intro k _
  exact Complex.continuous_normSq.comp ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- Actual coordinate derivative of a squared complex observable. -/
theorem fderiv_complex_normSq {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ ∞ F) (z v : Configuration n) :
    fderiv ℝ (fun w => Complex.normSq (F w)) z v =
      2 * (F z).re * (fderiv ℝ F z v).re + 2 * (F z).im * (fderiv ℝ F z v).im := by
  have hr := Complex.reCLM.hasFDerivAt.comp z ((hF.differentiable (by simp) z).hasFDerivAt)
  have hi := Complex.imCLM.hasFDerivAt.comp z ((hF.differentiable (by simp) z).hasFDerivAt)
  have hd := (hr.mul hr).add (hi.mul hi)
  have he : (fun w => Complex.normSq (F w)) =
      (fun w => (F w).re * (F w).re + (F w).im * (F w).im) := by
    funext w; simp [Complex.normSq_apply]
  change HasFDerivAt (fun w => (F w).re * (F w).re + (F w).im * (F w).im) _ z at hd
  rw [he, hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, Function.comp_apply,
      smul_eq_mul]
  ring

/-- Cauchy–Schwarz controls the actual squared-real gradient by the complex
directional energy times the squared complex value. -/
theorem ginibreEuclideanGradient_complex_normSq_bound {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ ∞ F) (z : Configuration n) :
    ‖ginibreEuclideanGradient (fun w => Complex.normSq (F w)) z‖ ^ 2 ≤
      4 * Complex.normSq (F z) * complexDirectionalEnergy F z := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]
  unfold complexDirectionalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [ginibreEuclideanGradient_coordinate, fderiv_complex_normSq F hF]
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg ((F z).re * (fderiv ℝ F z (ginibreCoordinateDirection k)).im -
    (F z).im * (fderiv ℝ F z (ginibreCoordinateDirection k)).re)]
end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticConfigurationBrownianBracket.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyBracket
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticConfigurationBrownianMartingale

/-! Exact square-minus-variance martingales for the paper's configuration noise. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConfigurationBrownianNoise_real_square_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).re^2-
      (2*(α : ℝ)/(n : ℝ)^2)*(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_square_martingale B P hB hind (j, 0)).smul
    (2*(α : ℝ)/(n : ℝ)^2)
  have hσ : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  convert! h using 1
  funext t ω
  have he : (ginibreConfigurationBrownianNoise n B α ω t j).re =
      Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*B (j, 0) t ω := by
    simp [ginibreConfigurationBrownianNoise, Complex.mul_re]
  rw [he, mul_pow, hσ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ginibreConfigurationBrownianNoise_imag_square_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).im^2-
      (2*(α : ℝ)/(n : ℝ)^2)*(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_square_martingale B P hB hind (j, 1)).smul
    (2*(α : ℝ)/(n : ℝ)^2)
  have hσ : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  convert! h using 1
  funext t ω
  have he : (ginibreConfigurationBrownianNoise n B α ω t j).im =
      Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*B (j, 1) t ω := by
    simp [ginibreConfigurationBrownianNoise, Complex.mul_im]
  rw [he, mul_pow, hσ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianQuadraticOrthogonality.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianWeightedQuadratic

/-! # Actual orthogonality of predictable centered quadratic innovations -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_predictable_quadratic_cross_zero {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (si ti sj tj : ℝ≥0) (hij : si + ti ≤ sj)
    (Fi : (Set.Iic si → ℝ) → ℝ) (Fj : (Set.Iic sj → ℝ) → ℝ)
    (hFi : Measurable Fi) (hFj : Measurable Fj) :
    (∫ ω, (Fi (fun v => B v ω)*((B (si+ti) ω-B si ω)^2-(ti : ℝ)))*
      (Fj (fun v => B v ω)*((B (sj+tj) ω-B sj ω)^2-(tj : ℝ))) ∂P) = 0 := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hsi : si ≤ sj := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ ti from bot_le)).trans hij
  let Past := fun ω (v : Set.Iic sj) => B v ω
  let Z := fun ω => B (sj+tj) ω-B sj ω
  let G : (Set.Iic sj → ℝ) → ℝ := fun p =>
    Fi (fun v => p ⟨v, v.2.trans hsi⟩)*
      ((p ⟨si+ti, hij⟩-p ⟨si, hsi⟩)^2-(ti : ℝ))*Fj p
  have hPast : Measurable Past := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hZ : HasLaw Z (gaussianReal 0 tj) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P
        hB.toIsPreBrownianReal sj (sj+tj)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ tj from bot_le))
  have hInd : IndepFun (fun ω => G (Past ω)) (fun ω => (Z ω)^2-(tj : ℝ)) P :=
    (ginibreBrownian_increment_whole_past_independent B P hB.toIsPreBrownianReal sj tj).symm.comp hG
      (show Measurable (fun x : ℝ => x^2-(tj : ℝ)) by fun_prop)
  have hSq : Integrable (fun ω => (Z ω)^2) P :=
    (ginibreGaussian_hasLaw_square_memLp_two P Z tj hZ).integrable (by norm_num)
  have hMean : (∫ ω, (Z ω)^2-(tj : ℝ) ∂P) = 0 := by
    rw [integral_sub hSq (integrable_const (tj : ℝ)), ginibreGaussian_hasLaw_square_mean P Z tj hZ]
    simp
  have hProd := hInd.integral_mul_eq_mul_integral
    (hG.comp hPast).aestronglyMeasurable ((hSq.sub (integrable_const (tj :
        ℝ))).aestronglyMeasurable)
  simp only [Pi.mul_apply, hMean, mul_zero] at hProd
  convert! hProd using 1
  congr 1
  funext ω
  dsimp [G, Past, Z]
  ring

end
end GinibrePoincare

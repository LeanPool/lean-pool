/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianWeightedQuadratic.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticInnovation

/-! # Genuine predictable quadratic-increment second-moment bounds -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_predictable_quadratic_memLp_two {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) → ℝ) (hF : Measurable F) (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C) :
    MemLp (fun ω => F (fun v => B v ω)*((B (s+t) ω-B s ω)^2-(t : ℝ))) 2 P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hPast : Measurable (fun ω (v : Set.Iic s) => B v ω) := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hZ : HasLaw (fun ω => B (s+t) ω-B s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P
        hB.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hCenter := (ginibreGaussian_hasLaw_square_memLp_two P _ t hZ).sub
    (memLp_const (t : ℝ))
  have hWeight : AEStronglyMeasurable (fun ω => F (fun v => B v ω)) P := (hF.comp
      hPast).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq (hWeight.mul hCenter.aestronglyMeasurable)).mpr
  change Integrable (fun ω => (F (fun v => B v ω) * ((B (s+t) ω-B s ω)^2-(t : ℝ)))^2) P
  simp_rw [mul_pow]
  apply hCenter.integrable_sq.bdd_mul (c := C^2) (hWeight.pow 2)
  apply Filter.Eventually.of_forall
  intro ω
  change ‖(F (fun v => B v ω))^2‖ ≤ C^2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound _) 2

theorem ginibreBrownian_predictable_quadratic_secondMoment_le {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) → ℝ) (hF : Measurable F) (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ ω, (F (fun v => B v ω)*((B (s+t) ω-B s ω)^2-(t : ℝ)))^2 ∂P) ≤
      2*C^2*(t : ℝ)^2 := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (v : Set.Iic s) => B v ω
  let Z := fun ω => B (s+t) ω-B s ω
  have hPast : Measurable Past := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hZ : HasLaw Z (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P
        hB.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hInd : IndepFun Z Past P := ginibreBrownian_increment_whole_past_independent B P
      hB.toIsPreBrownianReal s t
  have hSq : MemLp (fun ω => (Z ω)^2) 2 P := ginibreGaussian_hasLaw_square_memLp_two P Z t hZ
  have hMean := ginibreGaussian_hasLaw_square_mean P Z t hZ
  have hVar := ginibreGaussian_hasLaw_square_variance P Z t hZ
  have hCenter : (∫ ω, ((Z ω)^2-(t : ℝ))^2 ∂P) = 2*(t : ℝ)^2 := by
    have h := variance_eq_integral hSq.aemeasurable
    rw [hMean] at h
    exact h.symm.trans hVar
  have hC : 0 ≤ C := (norm_nonneg (F 0)).trans (hbound 0)
  have hSqBound (p : Set.Iic s → ℝ) : (F p)^2 ≤ C^2 := by
    have h := hbound p
    rw [Real.norm_eq_abs] at h
    nlinarith [sq_abs (F p), abs_nonneg (F p)]
  have hH : Integrable (fun ω => (F (Past ω))^2) P := by
    apply (integrable_const (C^2)).mono'
    · exact ((hF.comp hPast).pow_const 2).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hSqBound _
  have hHbound : (∫ ω, (F (Past ω))^2 ∂P) ≤ C^2 := by
    have h := integral_mono_ae hH (integrable_const (C^2))
      (Filter.Eventually.of_forall fun ω => hSqBound (Past ω))
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hIndSq := hInd.symm.comp
    (show Measurable (fun p => (F p)^2) from hF.pow_const 2)
    (show Measurable (fun x : ℝ => (x^2-(t : ℝ))^2) by fun_prop)
  have hProd := hIndSq.integral_mul_eq_mul_integral
    hH.aestronglyMeasurable (((hZ.aemeasurable.aestronglyMeasurable.pow 2).sub
        aestronglyMeasurable_const).pow 2)
  simp only [Function.comp_apply, Pi.mul_apply] at hProd
  simp only [mul_pow]
  change (∫ ω, (F (Past ω))^2*((Z ω)^2-(t : ℝ))^2 ∂P) ≤ _
  rw [hProd, hCenter]
  nlinarith [mul_le_mul_of_nonneg_right hHbound (sq_nonneg (t : ℝ))]

end
end GinibrePoincare

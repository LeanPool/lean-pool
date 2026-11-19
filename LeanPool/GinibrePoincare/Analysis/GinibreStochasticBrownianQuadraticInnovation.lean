/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianQuadraticInnovation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGaussianSquareMoments
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUWholePastMarkov
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianSums
public import Mathlib.Probability.Independence.Integration

/-! # Genuine predictable centered quadratic Brownian innovations -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_increment_whole_past_independent {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    IndepFun (fun ω => B (s+t) ω-B s ω) (fun ω (v : Set.Iic s) => B v ω) P :=
  (hB.indepFun_shift s).comp (measurable_pi_apply t) measurable_id

theorem ginibreBrownian_increment_quadratic_predictable_conditional {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) → ℝ) (hF : Measurable F) (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C) :
    P[(fun ω => F (fun v => B v ω)*((B (s+t) ω-B s ω)^2-(t : ℝ))) |
      ginibreBrownianPastMeasurableSpace B s] =ᵐ[P] (fun _ => 0) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (v : Set.Iic s) => B v ω
  let Z := fun ω => B (s+t) ω-B s ω
  let ν := gaussianReal 0 t
  have hPast : Measurable Past := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hZ : HasLaw Z ν P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P
        hB.toIsPreBrownianReal s (s+t) (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hInd : IndepFun Z Past P := ginibreBrownian_increment_whole_past_independent B P
      hB.toIsPreBrownianReal s t
  have hCond := ginibreIndependent_condDistrib P Past Z hPast ν hZ hInd
  have hCondω := ae_of_ae_map hPast.aemeasurable hCond
  let G : (Set.Iic s → ℝ) × ℝ → ℝ := fun p => F p.1*(p.2^2-(t : ℝ))
  have hG : Measurable G := by
    exact ((hF.comp measurable_fst).mul ((measurable_snd.pow_const 2).sub measurable_const))
  have hSq : Integrable (fun ω => (Z ω)^2) P :=
    (ginibreGaussian_hasLaw_square_memLp_two P Z t hZ).integrable (by norm_num)
  have hGint : Integrable (fun ω => G (Past ω, Z ω)) P :=
    (hSq.sub (integrable_const (t : ℝ))).bdd_mul
      (hF.comp hPast).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => hbound (Past ω))
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hZ.aemeasurable hG.stronglyMeasurable
      hGint
  apply hCE.trans
  filter_upwards [hCondω] with ω hκ
  change (∫ u, F (Past ω)*(u^2-(t : ℝ)) ∂condDistrib Z Past P (Past ω)) = 0
  rw [hκ]
  change (∫ u, F (Past ω)*(u^2-(t : ℝ)) ∂gaussianReal 0 t) = 0
  rw [integral_const_mul, integral_sub ((ginibreGaussian_square_memLp_two t).integrable (by
      norm_num)) (integrable_const (t : ℝ)),
    ginibreGaussian_secondMoment]
  simp
theorem ginibreBrownian_increment_quadratic_predictable_integrable_conditional {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) → ℝ) (hF : Measurable F)
    (hWeight : Integrable (fun ω => F (fun v => B v ω)) P) :
    P[(fun ω => F (fun v => B v ω)*((B (s+t) ω-B s ω)^2-(t : ℝ))) |
      ginibreBrownianPastMeasurableSpace B s] =ᵐ[P] (fun _ => 0) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (v : Set.Iic s) => B v ω
  let Z := fun ω => B (s+t) ω-B s ω
  let ν := gaussianReal 0 t
  have hPast : Measurable Past := by
    apply Measurable.of_eval
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hZ : HasLaw Z ν P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P
        hB.toIsPreBrownianReal s (s+t) (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hInd : IndepFun Z Past P := ginibreBrownian_increment_whole_past_independent B P
      hB.toIsPreBrownianReal s t
  have hCond := ginibreIndependent_condDistrib P Past Z hPast ν hZ hInd
  have hCondω := ae_of_ae_map hPast.aemeasurable hCond
  let G : (Set.Iic s → ℝ) × ℝ → ℝ := fun p => F p.1*(p.2^2-(t : ℝ))
  have hG : Measurable G := by
    exact ((hF.comp measurable_fst).mul ((measurable_snd.pow_const 2).sub measurable_const))
  have hSq : Integrable (fun ω => (Z ω)^2) P :=
    (ginibreGaussian_hasLaw_square_memLp_two P Z t hZ).integrable (by norm_num)
  have hIndWeight : IndepFun (fun ω => F (Past ω)) (fun ω => (Z ω)^2-(t : ℝ)) P :=
    hInd.symm.comp hF (show Measurable (fun x : ℝ => x^2-(t : ℝ)) by fun_prop)
  have hGint : Integrable (fun ω => G (Past ω, Z ω)) P :=
    hIndWeight.integrable_mul hWeight (hSq.sub (integrable_const (t : ℝ)))
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hZ.aemeasurable hG.stronglyMeasurable
      hGint
  apply hCE.trans
  filter_upwards [hCondω] with ω hκ
  change (∫ u, F (Past ω)*(u^2-(t : ℝ)) ∂condDistrib Z Past P (Past ω)) = 0
  rw [hκ]
  change (∫ u, F (Past ω)*(u^2-(t : ℝ)) ∂gaussianReal 0 t) = 0
  rw [integral_const_mul, integral_sub ((ginibreGaussian_square_memLp_two t).integrable (by
      norm_num)) (integrable_const (t : ℝ)),
    ginibreGaussian_secondMoment]
  simp

end
end GinibrePoincare

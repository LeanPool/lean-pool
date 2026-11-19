/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticAugmentedPredictableQuadratic.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianAugmentedFreshIncrement
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticPredictableInnovation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianWeightedQuadratic

/-! Exact predictable quadratic moments in the actual augmented joint Brownian filtration. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_augmented_coordinate_increment_independent {Ω ι A : Type*}
    [MeasurableSpace Ω] [Finite ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y) :
    IndepFun (fun ω => B i (s+t) ω-B i s ω) Y P := by
  have := Fintype.ofFinite ι
  have h := brownianFamily_fresh_increment_independent_augmented_variable B P hB hind s t Y hY
  exact h.comp (measurable_pi_apply i) measurable_id

theorem ginibreBrownian_augmented_quadratic_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F) :
    (∫ ω, (F ω*((B i (s+t) ω-B i s ω)^2-(t : ℝ)))^2 ∂P) =
      2*(t : ℝ)^2*(∫ ω, (F ω)^2 ∂P) := by
  have := Fintype.ofFinite ι
  let Z := fun ω => B i (s+t) ω-B i s ω
  have hZ : HasLaw Z (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono (ginibreBrownianAugmentedFiltration B P hB |>.le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  have hSq := ginibreGaussian_hasLaw_square_memLp_two P Z t hZ
  have hCenter : (∫ ω, ((Z ω)^2-(t : ℝ))^2 ∂P) = 2*(t : ℝ)^2 := by
    have h := variance_eq_integral hSq.aemeasurable
    rw [ginibreGaussian_hasLaw_square_mean P Z t hZ] at h
    exact h.symm.trans (ginibreGaussian_hasLaw_square_variance P Z t hZ)
  have hφ : Measurable (fun z : ℝ => (z^2-(t : ℝ))^2) := by fun_prop
  have hp := (hInd.symm.comp (measurable_id.pow_const 2) hφ).integral_mul_eq_mul_integral
    (hFM.pow_const 2).aestronglyMeasurable ((hφ.comp_aemeasurable
        hZ.aemeasurable).aestronglyMeasurable)
  simp only [Pi.mul_apply, Function.comp_apply, id_eq] at hp
  dsimp only [Z] at hCenter
  simp_rw [mul_pow]
  rw [hp, hCenter]
  ring

theorem ginibreBrownian_augmented_quadratic_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hFi : MemLp F 2 P) :
    MemLp (fun ω => F ω*((B i (s+t) ω-B i s ω)^2-(t : ℝ))) 2 P := by
  have := Fintype.ofFinite ι
  have hZ : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono (ginibreBrownianAugmentedFiltration B P hB |>.le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  have hφLp : MemLp (fun z : ℝ => z^2-(t : ℝ)) 2 (gaussianReal 0 t) :=
    (ginibreGaussian_hasLaw_square_memLp_two (gaussianReal 0 t) id t ⟨by fun_prop, by simp⟩).sub
        (memLp_const _)
  exact ginibreIndependent_predictable_memLp_two P F _ hFM _ hZ hInd id measurable_id hFi
    (fun z => z^2-(t : ℝ)) (by fun_prop) hφLp

end
end GinibrePoincare

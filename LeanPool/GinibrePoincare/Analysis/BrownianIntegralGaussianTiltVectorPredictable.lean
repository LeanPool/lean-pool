/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltVectorPredictable.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVector
public import LeanPool.GinibrePoincare.Analysis.BrownianAugmentedFreshIncrement

/-!
# Brownian integral Gaussian tilt vector predictable

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianVectorPredictableTilt_lintegral`,
`gaussianVectorPredictableTilt_lintegral_sq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem gaussianVectorExponentialTilt_product_lintegral {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (H : α → ι → ℝ) (Z : α → ℝ≥0∞) (hH : Measurable H) (hZ : Measurable Z) (v : ℝ≥0) :
    (∫⁻ z, Z z.1*ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)
      ∂μ.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))) = ∫⁻ a, Z a ∂μ := by
  classical
  rw [lintegral_prod]
  · congr 1
    funext a
    simp only []
    rw [lintegral_const_mul _ (by unfold gaussianVectorExponentialTilt gaussianExponentialTilt;
                                    fun_prop),
      gaussianVectorExponentialTilt_lintegral, mul_one]
  · unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop

theorem gaussianVectorExponentialTilt_product_lintegral_sq {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (H : α → ι → ℝ) (Z : α → ℝ≥0∞) (hH : Measurable H) (hZ : Measurable Z) (v : ℝ≥0) :
    (∫⁻ z, Z z.1*ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)^2
      ∂μ.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))) =
      ∫⁻ a, Z a*ENNReal.ofReal (Real.exp ((∑ i, (H a i)^2)*(v : ℝ))) ∂μ := by
  classical
  rw [lintegral_prod]
  · congr 1
    funext a
    simp only []
    rw [lintegral_const_mul _ (by unfold gaussianVectorExponentialTilt gaussianExponentialTilt;
                                    fun_prop),
      gaussianVectorExponentialTilt_lintegral_sq]
  · unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop

theorem gaussianVectorPredictableTilt_lintegral {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω)) ∂P) =
      ∫⁻ ω, Z (Y ω) ∂P := by
  classical
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY, rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×(ι→ℝ) => Z z.1*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)) := by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [] at hh
  rw [gaussianVectorExponentialTilt_product_lintegral μ H Z hH hZ v] at hh
  exact hh.trans (hYL.lintegral_comp hZ.aemeasurable).symm

theorem gaussianVectorPredictableTilt_lintegral_sq {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω))^2 ∂P) =
      ∫⁻ ω, Z (Y ω)*ENNReal.ofReal (Real.exp ((∑ i, (H (Y ω) i)^2)*(v : ℝ))) ∂P := by
  classical
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY, rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×(ι→ℝ) => Z z.1*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)^2) := by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [] at hh
  rw [gaussianVectorExponentialTilt_product_lintegral_sq μ H Z hH hZ v] at hh
  exact hh.trans (hYL.lintegral_comp (by fun_prop)).symm

end
end GinibrePoincare

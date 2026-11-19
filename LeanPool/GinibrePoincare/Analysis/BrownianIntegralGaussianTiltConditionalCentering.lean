/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltConditionalCentering.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVectorCentering
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVectorPredictable

/-!
# Brownian integral Gaussian tilt conditional centering

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianVectorPredictableTilt_centered_lintegral`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Every nonnegative joint past/centered-innovation test under the genuine
predictable RN tilt has the unchanged fresh Gaussian kernel. -/
theorem gaussianVectorPredictableTilt_centered_lintegral {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z)
    (F : α×(ι→ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω))*
      F (Y ω, fun i => X ω i-H (Y ω) i*(v : ℝ)) ∂P) =
      ∫⁻ a, Z a*(∫⁻ x, F (a, x) ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) ∂P.map Y := by
  classical
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY, rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×(ι→ℝ) => Z z.1*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)*
        F (z.1, fun i => z.2 i-H z.1 i*(v : ℝ))) := by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [] at hh
  rw [lintegral_prod _ hm.aemeasurable] at hh
  refine hh.trans ?_
  congr 1
  funext a
  simp only [mul_assoc]
  rw [lintegral_const_mul _ (by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt; fun_prop)]
  rw [gaussianVectorExponentialTilt_centered_lintegral (H a) v
    (fun x => F (a, x)) (hF.comp (measurable_const.prodMk measurable_id))]

end
end GinibrePoincare

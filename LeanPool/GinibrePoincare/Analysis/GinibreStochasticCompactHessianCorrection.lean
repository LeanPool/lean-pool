/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCompactHessianCorrection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedWeightedHessian
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTestCoefficients

/-! Actual local C² Hessian correction along compact adapted configuration paths. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCompactProcess_hessian_correction {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0) :
    TendstoInMeasure P
      (ginibreBrownianAugmentedWeightedHessian B T
        (fun i j t ω => itoConfigurationHessianEntry f (X t ω) i j)) atTop
      (fun ω => ∫ s in (0 : ℝ)..T, configurationLaplacian f (X s.toNNReal ω)) := by
  classical
  obtain ⟨C, hC, _, hH⟩ := ginibreCompactProcess_test_coefficients n
    (ginibreBrownianAugmentedFiltration B P hB) X hX hCont f U K hU hf hK hKU hRange
  have hlimit := ginibreBrownianAugmentedWeightedHessian_tendstoInProbability B P hB hind T
    (fun i j t ω => itoConfigurationHessianEntry f (X t ω) i j)
    (fun i j => (hH i j).1) (fun i j => Filter.Eventually.of_forall (hH i j).2.1)
    C (fun i j t ω => (hH i j).2.2 t ω)
  convert hlimit using 1
  funext ω
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro s hs
    exact itoConfigurationHessian_trace f (X s.toNNReal ω)
      (hf.contDiffAt (hU.mem_nhds (hKU (hRange _ _)))) |>.symm
  · intro i hi
    exact ((hH i i).2.1 ω).comp continuous_real_toNNReal |>.intervalIntegrable _ _
end
end GinibrePoincare

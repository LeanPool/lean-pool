/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitNoisePath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalEvaluation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousNoisePath

/-! The actual Brownian configuration noise as a full continuous zero-based path. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Turns a continuous path `N` into a continuous noise by subtracting its initial value `N 0`. -/
def ginibreContinuousNoiseNormalize (n : ℕ) (N : C(ℝ, Configuration n)) : GinibreContinuousNoise n
     :=
  ⟨N - ContinuousMap.const ℝ (N 0), by simp⟩

theorem ginibreContinuousNoiseNormalize_continuous (n : ℕ) :
    Continuous (ginibreContinuousNoiseNormalize n) := by
  apply Continuous.subtype_mk
  exact continuous_id.sub (ContinuousMap.continuous_const'.comp (continuous_eval_const 0))

/-- The continuous noise of the sample `ω`: the scaled configuration Brownian noise
`ginibreConfigurationBrownianNoise n B α ω` (replaced by `0` if it is not continuous),
normalized to vanish at time `0`. -/
def ginibreBrownianFullContinuousNoise {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) : GinibreContinuousNoise n :=
  ginibreContinuousNoiseNormalize n
    (ContinuousMap.mkD (ginibreConfigurationBrownianNoise n B α ω) 0)

theorem ginibreBrownianFullContinuousNoise_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, (ginibreBrownianFullContinuousNoise n B α ω).val t =
      ginibreConfigurationBrownianNoise n B α ω t := by
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  intro t
  simp [ginibreBrownianFullContinuousNoise, ginibreContinuousNoiseNormalize,
    ContinuousMap.mkD, hω.1, hω.2]

theorem ginibreBrownianFullContinuousNoise_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    Measurable (ginibreBrownianFullContinuousNoise n B α) := by
  let : MeasurableSpace C(ℝ, Configuration n) := borel _
  let : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  apply (ginibreContinuousNoiseNormalize_continuous n).measurable.comp
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply (aemeasurable_iff_measurable (μ := P)).mp
  have hNoise : Measurable (fun ω => ginibreConfigurationBrownianNoise n B α ω t) := by
    apply Measurable.of_eval
    intro j
    exact (((aemeasurable_iff_measurable.mp ((hB (j, 0)).aemeasurable
        t.toNNReal)).complex_ofReal).add
      (measurable_const.mul ((aemeasurable_iff_measurable.mp
        ((hB (j, 1)).aemeasurable t.toNNReal)).complex_ofReal))).const_smul (Real.sqrt (2*α/(n :
            ℝ)^2))
  apply hNoise.aemeasurable.congr
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  simp [ContinuousMap.mkD, hω.1]

end
end GinibrePoincare

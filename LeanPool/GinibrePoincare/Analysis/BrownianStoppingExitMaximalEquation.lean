/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitMaximalEquation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitMaximalAdaptation
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalBlowup

/-! The canonical maximal process solves the original Brownian Volterra equation before its
actual lifetime. No solution or local-equation certificate is assumed. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalLifetime_pos {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    0 < ginibreBrownianMaximalLifetime n α z B ω := by
  exact ginibreDrivenMaximalLifetime_pos n α _
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz

theorem ginibreBrownianMaximalProcess_equation_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω →
      CollisionFree (ginibreBrownianMaximalProcess n α z B t ω) ∧
      IntervalIntegrable (fun u : ℝ => ginibreLangevinDrift n α
        (ginibreBrownianMaximalProcess n α z B (Real.toNNReal u) ω)) volume 0 (t : ℝ) ∧
      ginibreBrownianMaximalProcess n α z B t ω =
        z + ginibreConfigurationBrownianNoise n B α ω t +
        ∫ u in (0 : ℝ)..(t : ℝ), ginibreLangevinDrift n α
          (ginibreBrownianMaximalProcess n α z B (Real.toNNReal u) ω) := by
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hω
  intro t ht
  have he := ginibreDrivenMaximalPath_equation (n := n) (α := α)
    (N := (ginibreBrownianFullContinuousNoise n B α ω).val) (z := z)
    (t := (t : ℝ)) ⟨t.coe_nonneg, by simpa only [ginibreBrownianMaximalLifetime,
                                       ENNReal.ofReal_coe_nnreal] using ht⟩
  change CollisionFree (ginibreDrivenMaximalValue n α _ z t) ∧ _ ∧ _
  simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe,
    ginibreBrownianMaximalProcess, hω] using he

end
end GinibrePoincare

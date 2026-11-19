/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianStoppedAdaptation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianStoppedEquation
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitCountableEvaluation
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalTimeContinuity

/-! Genuine strong adaptation of the compact localized maximal path, proved by countable
upper stopping approximations and continuity strictly before its lifetime. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted {Ω : Type*}
    [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T) := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T
  have hσ := ginibreBrownianHamiltonianBoundedStop_isStoppingTime hn α z hz B P hB R hR T
  have hu := ginibreBrownianMaximalProcess_stronglyAdapted hn α z B P hB
  intro s
  have hMeas (m : ℕ) : @StronglyMeasurable Ω (Configuration n) _ (F s)
      (fun ω => ginibreBrownianMaximalProcess n α z B (min s (stoppingUpperGrid m (σ ω))) ω) :=
    (adapted_capped_upper_grid_evaluation_measurable F _ hu.adapted σ hσ m s).stronglyMeasurable
  apply stronglyMeasurable_of_tendsto atTop hMeas
  rw [tendsto_pi_nhds]
  intro ω
  have hsσ := ginibreDrivenHamiltonianBoundedStop_lt_lifetime hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T
  have hs : ((min s (σ ω) : ℝ≥0) : ℝ≥0∞) <
      ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α ω).val z :=
    (ENNReal.coe_le_coe.mpr (min_le_right s (σ ω))).trans_lt hsσ
  have hc := ginibreDrivenMaximalValue_continuousAt_time (min s (σ ω)) hs
  exact hc.tendsto.comp (tendsto_const_nhds.min (stoppingUpperGrid_tendsto (σ ω)))

end
end GinibrePoincare

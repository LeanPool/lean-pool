/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticGlobalUniqueness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticNoncollision
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianPathUniqueness

/-! # Pathwise uniqueness for the original singular equation

The competing path `Y` is assumed continuous, collision-free, and to solve
the same driven equation with the same initial state and Brownian noise.
On the intersection of its full-measure solution event and that of the
canonical global process, fix any finite nonnegative time `t`. Both paths
satisfy the same Volterra equation on `[0, t]`; deterministic finite-interval
uniqueness in `GinibreHamiltonianPathUniqueness` identifies their endpoints.
Thus the conclusion uses one full-measure event for all nonnegative times. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_global_pathwise_unique
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (Y : ℝ → Ω → Configuration n)
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω) ∧ Y 0 ω = z ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (Y t ω)) ∧
      IsGinibreDrivenPath n α (ginibreConfigurationBrownianNoise n B α ω) (fun t => Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω=ginibreBrownianMaximalProcess n α z B t.toNNReal ω := by
  have hGlobal := (ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2
  filter_upwards [hGlobal, hY] with ω hX hY
  intro t ht
  let X := fun s : ℝ => ginibreBrownianMaximalProcess n α z B s.toNNReal ω
  have hinit : X 0=z := by simpa [X] using hX.2.1
  have hEqX (s : ℝ) (hs : s ∈ Icc 0 t) : X s=z+ginibreConfigurationBrownianNoise n B α ω s+
      ∫ u in (0 : ℝ)..s, ginibreLangevinDrift n α (X u) := by
    have h := hX.2.2.2.2 s hs.1
    change X s=X 0+ginibreConfigurationBrownianNoise n B α ω s+
      ∫ u in (0 : ℝ)..s, ginibreLangevinDrift n α (X u) at h
    rw [hinit] at h
    exact h
  have hEqY (s : ℝ) (hs : s ∈ Icc 0 t) : Y s ω=z+ginibreConfigurationBrownianNoise n B α ω s+
      ∫ u in (0 : ℝ)..s, ginibreLangevinDrift n α (Y u ω) := by
    have h := hY.2.2.2.2 s hs.1
    dsimp only at h
    rw [hY.2.1] at h
    exact h
  exact ginibreDrivenPath_finite_interval_unique n α z (ginibreConfigurationBrownianNoise n B α ω)
    (fun s => Y s ω) X t ht hY.1.continuousOn hX.1.continuousOn
    (fun s hs => hY.2.2.1 s hs.1) (fun s hs => hX.2.2.1 s hs.1) hEqY hEqX ⟨ht, le_rfl⟩
end
end GinibrePoincare

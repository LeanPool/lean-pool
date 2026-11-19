/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationExistence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationPaths

/-!
# Brownian integral continuous modification existence

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `realMartingale_terminal_cauchy_exists_continuous_limit`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Actual continuous martingales which are mean-square Cauchy at the terminal
time admit a deterministic subsequence converging almost surely uniformly to
an actual continuous path. All probability and convergence conclusions are
derived; the hypotheses contain only the original martingales and moments. -/
theorem realMartingale_terminal_cauchy_exists_continuous_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (F : ℕ → ℝ≥0 → Ω → ℝ)
    (hF : ∀ n, Martingale (F n) ℱ P) (T : ℝ≥0)
    (hT : ∀ n, MemLp (F n T) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t => F n t ω) (Set.Icc 0 T))
    (hterm : Tendsto (fun q : ℕ × ℕ =>
      ∫ ω, (F q.2 T ω-F q.1 T ω)^2 ∂P) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ L : Ω → C(Set.Icc 0 T, ℝ),
      ∀ᵐ ω ∂P, TendstoUniformly (fun n (t : Set.Icc 0 T) => F (s n) t ω) (L ω) atTop := by
  let G := fun n => continuousIntervalPathVersion (F n) T
  have hG := continuousIntervalPathVersion_probability_cauchy P ℱ F hF T hT hc hterm
  let d : ℕ → ℝ := fun n => ((1 : ℝ)/2)^n
  have hd : ∀ n, 0 < d n := fun n => pow_pos (by norm_num) n
  let p : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (d n)
  have hp : ∀ n, 0 < p n := fun n => ENNReal.ofReal_pos.mpr (hd n)
  have hpsum : (∑' n, p n) ≠ ⊤ := by
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => (hd n).le) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  obtain ⟨s, hs, hlimit⟩ := continuousProbabilityCauchy_exists_uniform_limit P G hG
    d hd summable_geometric_two p hp hpsum
  refine ⟨s, hs, (fun ω => continuousMartingalePathLimit (fun n => G (s n)) ω),?_⟩
  filter_upwards [hlimit, continuousIntervalPathVersion_sequence_eq_ae P F T hc] with ω hl he
  convert hl using 1
  funext n t
  exact (he (s n) t).symm

end
end GinibrePoincare

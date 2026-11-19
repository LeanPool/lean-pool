/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralSubstitutionDiagonal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionRefinement

/-!
# Ginibre Brownian integral substitution diagonal

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualMeanSquare_diagonal_selection`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Choose actual inner approximations so the outer mean-square error vanishes. -/
theorem actualMeanSquare_diagonal_selection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → ℕ → Ω → ℝ) (I : ℕ → Ω → ℝ)
    (hlim : ∀ n, Tendsto (fun m => ∫ ω, (S n m ω - I n ω) ^ 2 ∂P) atTop (𝓝 0)) :
    ∃ m : ℕ → ℕ, Tendsto (fun n => ∫ ω, (S n (m n) ω-I n ω)^2 ∂P) atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ m, (∫ ω, (S n m ω-I n ω)^2 ∂P) ≤ 1/((n : ℝ)+1) := by
    have hp : (0 : ℝ)<1/((n : ℝ)+1) := by positivity
    have h := (hlim n).eventually (gt_mem_nhds hp)
    obtain ⟨m, hm⟩ := h.exists
    exact ⟨m, hm.le⟩
  choose m hm using hex
  refine ⟨m,?_⟩
  exact squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hm
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end
end GinibrePoincare

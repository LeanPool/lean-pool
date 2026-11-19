/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralUniformLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralL2Completion
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationExistence

/-! Almost surely uniform continuous limits of the actual Brownian integral approximations. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianUniformPartialSum_exists_continuous_uniform_limit {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal) t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Set.Icc 0 T, ∀ ω, ‖F s ω‖ ≤ C) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ L : Ω → C(Set.Icc 0 T, ℝ),
      ∀ᵐ ω ∂P, TendstoUniformly (fun n (t : Set.Icc 0 T) => brownianUniformPartialSum (B j) F T (s
          n+1) t ω)
        (L ω) atTop := by
  have := Fintype.ofFinite ι
  let hb := fun i => (hB i).toIsPreBrownianReal
  let S := fun n => brownianUniformPartialSum (B j) F T (n+1)
  have hSM (n : ℕ) : Martingale (S n) (ginibreBrownianAugmentedFiltration B P hb) P :=
    brownianUniformPartialSum_martingale B P hb hind j F hF hFi T (n+1)
  have hST (n : ℕ) : MemLp (S n T) 2 P :=
    brownianUniformPartialSum_memLp_two B P hb hind j F hF hFi T (n+1) T
  have hSC (n : ℕ) : ∀ᵐ ω ∂P, ContinuousOn (fun t => S n t ω) (Set.Icc 0 T) :=
    (hB j).cont.mono fun ω hω => (brownianUniformPartialSum_continuous (B j) F T (n+1) ω
        hω).continuousOn
  have hterm : Tendsto (fun q : ℕ×ℕ => ∫ ω, (S q.2 T ω-S q.1 T ω)^2 ∂P) atTop (𝓝 0) := by
    have hh := brownianUniformPartialSum_tendsto_difference_meanSquare B P hb hind j F hF hFi T T
        le_rfl hc C hC hbound
    convert hh using 1
    funext q
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by dsimp [S]; ring)
  exact realMartingale_terminal_cauchy_exists_continuous_limit P _ S hSM T hST hSC hterm

end
end GinibrePoincare

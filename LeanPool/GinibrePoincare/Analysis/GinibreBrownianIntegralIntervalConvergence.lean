/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralIntervalConvergence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralIntervalIsometry
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralCoefficientMesh

/-!
# Ginibre Brownian integral interval convergence

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianDisjointSampleDifferences_tendsto_meanSquare`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Actual finite disjoint Brownian increments with vanishing sampled coefficient
oscillation tend to zero in mean square. -/
theorem brownianDisjointSampleDifferences_tendsto_meanSquare {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (κ : ℕ → Type*) [∀ n, Fintype (κ n)] [∀ n, Nonempty (κ n)]
    (s d a b : (n : ℕ) → κ n → ℝ≥0)
    (hdisj : ∀ n i k, i ≠ k → d n i ≠ 0 → d n k ≠ 0 →
      s n i + d n i ≤ s n k ∨ s n k + d n k ≤ s n i)
    (haPast : ∀ n i, a n i ≤ s n i) (hbPast : ∀ n i, b n i ≤ s n i)
    (T : ℝ≥0) (ha : ∀ n i, a n i ∈ Set.Icc 0 T)
    (hb : ∀ n i, b n i ∈ Set.Icc 0 T)
    (hd : ∀ n, ∑ i, (d n i : ℝ) ≤ T)
    (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hab : ∀ n i, dist (a n i) (b n i) ≤ δ n)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ω, ‖F t ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω, (∑ i,
      (F (a n i) ω-F (b n i) ω)*(B j (s n i+d n i) ω-B j (s n i) ω))^2 ∂P)
      atTop (𝓝 0) := by
  classical
  have := Fintype.ofFinite ι
  have hFm (t : ℝ≥0) : Measurable (F t) :=
    (hF t).mono ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl
  have hmesh := brownianCoefficientSampleMesh_tendsto_meanSquare P κ F hFm T a b
    ha hb δ hδ hab hc C hC (fun t _ ω => hbound t ω)
  have hupper (n : ℕ) :
      (∫ ω, (∑ i, (F (a n i) ω-F (b n i) ω)*
        (B j (s n i+d n i) ω-B j (s n i) ω))^2 ∂P) ≤
        (T : ℝ)*(∫ ω, (brownianCoefficientSampleMesh F (a n) (b n) ω)^2 ∂P) := by
    have h := brownianDisjointIntervalSum_secondMoment_le B P hB hind j (s n) (d n)
      (hdisj n) (fun i ω => F (a n i) ω-F (b n i) ω)
      (fun i => ((hF _).mono ((ginibreBrownianAugmentedFiltration B P hB).mono (haPast n i))
          le_rfl).sub
        ((hF _).mono ((ginibreBrownianAugmentedFiltration B P hB).mono (hbPast n i)) le_rfl))
      (fun i => (hFi _).sub (hFi _))
      (brownianCoefficientSampleMesh F (a n) (b n))
      (brownianCoefficientSampleMesh_integrable_sq P F hFm (a n) (b n) C hC hbound)
      (fun i ω => Finset.le_sup' (f := fun k => ‖F (a n k) ω-F (b n k) ω‖) (Finset.mem_univ i))
    exact h.trans (mul_le_mul_of_nonneg_right (hd n) (integral_nonneg fun ω => sq_nonneg _))
  apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hupper
  simpa using hmesh.const_mul (T : ℝ)

end
end GinibrePoincare

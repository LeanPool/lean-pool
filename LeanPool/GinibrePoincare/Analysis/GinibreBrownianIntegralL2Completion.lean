/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralL2Completion.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPartialCauchy

/-! Completion of actual mean-square Cauchy sequences, applied to the genuine partial sums. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem actualMeanSquareCauchy_exists_L2_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Ω → ℝ) (hs : ∀ n, MemLp (S n) 2 P)
    (hc : Tendsto (fun q : ℕ×ℕ => ∫ ω, (S q.1 ω-S q.2 ω)^2 ∂P) atTop (𝓝 0)) :
    ∃ I : Lp ℝ 2 P, Tendsto (fun n => (hs n).toLp (S n)) atTop (𝓝 I) := by
  let Z := fun n => (hs n).toLp (S n)
  have he (q : ℕ×ℕ) : dist (Z q.1) (Z q.2) = Real.sqrt (∫ ω, (S q.1 ω-S q.2 ω)^2 ∂P) := by
    have hh : (∫ ω, (S q.1 ω-S q.2 ω)^2 ∂P) = ‖Z q.1-Z q.2‖^2 := by
      rw [← integral_square_eq_L2_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Z q.1) (Z q.2), (hs q.1).coeFn_toLp, (hs q.2).coeFn_toLp]
        with ω hω h1 h2
      simp only [hω, Pi.sub_apply]
      dsimp only [Z]
      rw [h1, h2]
    rw [hh, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]
  have hcz : CauchySeq Z := by
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    simpa only [he, Real.sqrt_zero] using hc.sqrt
  exact cauchySeq_tendsto_of_complete hcz

theorem brownianUniformPartialSum_exists_L2_limit {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T t : ℝ≥0) (ht : t ≤ T)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Set.Icc 0 T, ∀ ω, ‖F s ω‖ ≤ C) :
    ∃ I : Lp ℝ 2 P, Tendsto (fun n =>
      (brownianUniformPartialSum_memLp_two B P hB hind j F hF hFi T (n+1) t).toLp
        (brownianUniformPartialSum (B j) F T (n+1) t)) atTop (𝓝 I) := by
  have := Fintype.ofFinite ι
  exact actualMeanSquareCauchy_exists_L2_limit P _
    (fun n => brownianUniformPartialSum_memLp_two B P hB hind j F hF hFi T (n+1) t)
    (brownianUniformPartialSum_tendsto_difference_meanSquare B P hB hind j F hF hFi T t ht hc C hC
        hbound)

theorem actualMeanSquareCauchy_exists_L2_limit_inProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Ω → ℝ) (hs : ∀ n, MemLp (S n) 2 P)
    (hc : Tendsto (fun q : ℕ×ℕ => ∫ ω, (S q.1 ω-S q.2 ω)^2 ∂P) atTop (𝓝 0)) :
    ∃ I : Lp ℝ 2 P, Tendsto (fun n => (hs n).toLp (S n)) atTop (𝓝 I) ∧
      TendstoInMeasure P S atTop (fun ω => I ω) := by
  obtain ⟨I, hI⟩ := actualMeanSquareCauchy_exists_L2_limit P S hs hc
  exact ⟨I, hI, (tendstoInMeasure_of_tendsto_Lp hI).congr (fun n => (hs n).coeFn_toLp)
      EventuallyEq.rfl⟩

end
end GinibrePoincare

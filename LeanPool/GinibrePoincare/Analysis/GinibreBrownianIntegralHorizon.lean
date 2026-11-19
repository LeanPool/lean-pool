/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralHorizon.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralContinuous
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralHorizonComparison
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralLimitTransfer

/-! The genuinely constructed continuous Brownian integral agrees with the
actual uniform left sums at every smaller horizon. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianContinuousIntegral_horizon_limit {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (T t : ℝ≥0) (ht : t ≤ T)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ω, ‖F s ω‖ ≤ C)
    (I : Ω → ℝ) (hI : MemLp I 2 P)
    (hlim : Tendsto (fun n => ∫ ω,
      (brownianUniformPartialSum (B j) F T (n + 1) t ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (brownianUniformLeftSum (B j) F t (n+1) ω-I ω)^2 ∂P) atTop (𝓝 0) ∧
    TendstoInMeasure P (fun n => brownianUniformLeftSum (B j) F t (n+1)) atTop I := by
  have := Fintype.ofFinite ι
  have hFi (s : ℝ≥0) : MemLp (F s) 2 P := MemLp.of_bound
    ((hF s).mono ((ginibreBrownianAugmentedFiltration B P hB).le s) le_rfl).aestronglyMeasurable
    C (Eventually.of_forall (hbound s))
  have hR (n : ℕ) : MemLp (brownianUniformLeftSum (B j) F t (n+1)) 2 P :=
    brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi t (n+1)
  have hcomp := brownianUniformPartialSum_horizon_difference_tendsto_meanSquare
    B P hB hind j F hF hFi T t ht hc C hC hbound
  have hm := actualMeanSquareLimit_transfer P _ _ I
    (fun n => brownianUniformPartialSum_memLp_two B P hB hind j F hF hFi T (n+1) t)
    hR hI hcomp hlim
  exact ⟨hm, ginibre_tendstoInMeasure_of_meanSquare P _ I
    (fun n => ((hR n).sub hI).integrable_sq) hm⟩

/-- The actual continuous integral has a genuine uniform left-sum limit on
all horizons below T, in addition to its original martingale properties. -/
theorem brownianContinuousIntegral_exists_all_horizons {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F t))
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ω, ‖F t ω‖ ≤ C) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      Martingale M (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => M t ω)) ∧ (∀ t, MemLp (M t) 2 P) ∧
      M 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun n => brownianUniformPartialSum (B j) F T (n+1) t) atTop (M t)) ∧
      ∀ t ≤ T, TendstoInMeasure P (fun n => brownianUniformLeftSum (B j) F t (n+1)) atTop (M t) :=
          by
  have := Fintype.ofFinite ι
  obtain ⟨M, hM, hMC, hML, hM0, hMP, hMS⟩ :=
    brownianContinuousIntegral_exists B P hB hind j F hF T hc C hC hbound
  refine ⟨M, hM, hMC, hML, hM0, hMP,?_⟩
  intro t ht
  exact (brownianContinuousIntegral_horizon_limit B P
    (fun i => (hB i).toIsPreBrownianReal) hind j F hF T t ht hc C hC hbound
    (M t) (hML t) (hMS t)).2

end
end GinibrePoincare

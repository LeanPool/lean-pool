/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPuncturedApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedCauchy
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralHorizon

/-! Genuine continuous stochastic integral approximants for a bounded adapted
integrand continuous at every positive time. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianPuncturedIntegral_continuous_approximants {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, ‖F t ω‖ ≤ C)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ M : ℕ → ℝ≥0 → Ω → ℝ,
      (∀ n, Martingale (M n) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P) ∧
      (∀ n ω, Continuous (fun t => M n t ω)) ∧
      (∀ n t, MemLp (M n t) 2 P) ∧
      (∀ n, M n 0 =ᵐ[P] (fun _ => 0)) ∧
      (∀ (n : ℕ) (t : ℝ≥0), t ≤ T → Tendsto (fun k => ∫ ω,
        (brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F (1/((n : ℝ)+1)))
          t (k+1) ω-M n t ω)^2 ∂P) atTop (𝓝 0)) ∧
      Tendsto (fun q : ℕ × ℕ => ∫ ω, (M q.1 T ω-M q.2 T ω)^2 ∂P) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  let ε := fun n : ℕ => 1/((n : ℝ)+1)
  have he (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let A := fun n => brownianInitialTimeCutoff F (ε n)
  have ha (n : ℕ) := brownianInitialTimeCutoff_adapted F (ε n) _ hF
  have hac (n : ℕ) : ∀ᵐ ω ∂P, ContinuousOn (fun t => A n t ω) (Set.Icc 0 T) :=
    hc.mono fun ω hω => (brownianInitialTimeCutoff_continuous F (he n) ω hω).continuousOn
  have hab (n : ℕ) : ∀ t ω, ‖A n t ω‖ ≤ C :=
    fun t ω => brownianInitialTimeCutoff_bound F (ε n) C hb t ω
  have hex (n : ℕ) := brownianContinuousIntegral_exists B P hB hind j (A n) (ha n)
    T (hac n) C hC (hab n)
  choose M hM hMC hML hM0 hMP hMS using hex
  have hleft (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) : Tendsto (fun k => ∫ ω,
      (brownianUniformLeftSum (B j) (A n) t (k+1) ω-M n t ω)^2 ∂P) atTop (𝓝 0) :=
    (brownianContinuousIntegral_horizon_limit B P (fun i => (hB i).toIsPreBrownianReal)
      hind j (A n) (ha n) T t ht (hac n) C hC (hab n) (M n t) (hML n t) (hMS n t)).1
  refine ⟨M, hM, hMC, hML, hM0, hleft,?_⟩
  apply brownianInitialCutoff_integral_limits_cauchy B P
    (fun i => (hB i).toIsPreBrownianReal) hind j F hF C hC hb T hT
    (fun n => M n T) (fun n => hML n T)
  intro n
  convert hleft n T le_rfl using 1
  funext k
  apply integral_congr_ae
  exact ae_of_all P fun ω => by dsimp [A, ε]; ring

end
end GinibrePoincare

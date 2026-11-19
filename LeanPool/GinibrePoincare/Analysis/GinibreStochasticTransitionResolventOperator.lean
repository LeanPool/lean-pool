/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionResolventOperator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedResolvent
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceOperator
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticBoundedDense

/-!
# Ginibre stochastic transition resolvent operator

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalStochasticL2ResolventOperator_apply`,
`ginibreBoundedLp_measurable_version`, `ginibreSymmetricSource_operators_eq_of_bounded_values`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The actual stochastic normalized Laplace integral bundled as a continuous linear map. -/
def ginibreOriginalStochasticL2ResolventOperator {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (c : ℝ) (hc : 0 < c) :
    Lp ℝ 2 (ginibreMeasure n) →L[ℝ] Lp ℝ 2 (ginibreMeasure n) :=
  actualContractionLaplaceOperator
    (ginibreOriginalStochasticL2Operator hn α P B hB hiB)
    (ginibreOriginalStochasticL2Operator_strong_continuous hn α P B hB hiB)
    (ginibreOriginalStochasticL2Operator_norm_le hn α P B hB hiB) c hc

theorem ginibreOriginalStochasticL2ResolventOperator_apply {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (c : ℝ) (hc : 0 < c)
    (u : Lp ℝ 2 (ginibreMeasure n)) :
    ginibreOriginalStochasticL2ResolventOperator hn α P B hB hiB c hc u =
      ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c u := rfl

/-- A globally bounded measurable version of every essentially bounded real L² value. -/
theorem ginibreBoundedLp_measurable_version {n : ℕ} (_ : 0 < n)
    (f : Lp ℝ 2 (ginibreMeasure n)) (A : ℝ)
    (hb : ∀ᵐ z ∂ginibreMeasure n, ‖f z‖ ≤ A) :
    ∃ v : Configuration n → ℝ, Measurable v ∧ (∀ z, ‖v z‖≤max A 0) ∧
      (f : Configuration n → ℝ)=ᵐ[ginibreMeasure n] v := by
  let v := actualBoundedRealVersion f (max A 0)
  have hm : Measurable v := by
    exact Measurable.ite
      (measurableSet_le (Lp.stronglyMeasurable f).measurable.norm measurable_const)
      (Lp.stronglyMeasurable f).measurable measurable_const
  have hb' : ∀ᵐ z ∂ginibreMeasure n, ‖f z‖≤max A 0 := hb.mono fun z hz => hz.trans (le_max_left _ _)
  exact ⟨v, hm, actualBoundedRealVersion_bound f (max A 0) (le_max_right _ _),
    (actualBoundedRealVersion_ae _ f _ hb').symm⟩

/-- Equality on genuinely bounded values extends to the full symmetric L² source,
with no assumption that either target operator preserves symmetry. -/
theorem ginibreSymmetricSource_operators_eq_of_bounded_values (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R S : ginibreFullSymmetricValues n →L[ℝ] E)
    (heq : ∀ u : ginibreFullSymmetricValues n,
      (∃ A : ℝ, ∀ᵐ z ∂ginibreMeasure n, ‖u.val z‖≤A) → R u=S u) : R=S := by
  apply ContinuousLinearMap.ext
  intro u
  have ht := ginibreFullSymmetricBoundedTruncation_tendsto n u
  have hh (m : ℕ) : R (ginibreFullSymmetricBoundedTruncation n m u)=
      S (ginibreFullSymmetricBoundedTruncation n m u) :=
    heq _ ⟨2*((m : ℝ)+1), ginibreFullSymmetricBoundedTruncation_bound n m u⟩
  have hRt := R.continuous.tendsto u |>.comp ht
  have hSt : Tendsto (fun m => R (ginibreFullSymmetricBoundedTruncation n m u)) atTop (𝓝 (S u)) :=
      by
    convert (S.continuous.tendsto u |>.comp ht) using 1
    funext m
    exact hh m
  exact tendsto_nhds_unique hRt hSt

end
end GinibrePoincare

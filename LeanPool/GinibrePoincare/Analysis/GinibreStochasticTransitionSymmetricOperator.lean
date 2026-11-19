/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionSymmetricOperator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationOperator
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Sampling
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionResolventIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticResolventSemigroupComparison

/-!
# Ginibre stochastic transition symmetric operator

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalSymmetricStochasticL2Operator_zero`,
`ginibreOriginalSymmetricStochasticL2Operator_laplace`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The restriction of the original stochastic `L²` transition operator to the
permutation-invariant subspace `ginibreFullSymmetricValues n`, which it preserves. -/
def ginibreOriginalSymmetricStochasticL2Operator {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n :=
  ((ginibreOriginalStochasticL2Operator hn α P B hB hiB T).comp
    (ginibreFullSymmetricValues n).subtypeL).codRestrict (ginibreFullSymmetricValues n)
      (ginibreOriginalStochasticL2Operator_preserves_symmetric hn α P B hB hiB T)

theorem ginibreOriginalSymmetricStochasticL2Operator_val {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (u : ginibreFullSymmetricValues n) :
    (ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T u).val=
      ginibreOriginalStochasticL2Operator hn α P B hB hiB T u.val := rfl

theorem ginibreOriginalSymmetricStochasticL2Operator_continuous {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (u : ginibreFullSymmetricValues n) :
    Continuous (fun T => ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T u) :=
  Continuous.subtype_mk (ginibreOriginalStochasticL2Operator_strong_continuous hn α P B hB hiB
      u.val) _

theorem ginibreOriginalSymmetricStochasticL2Operator_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (u : ginibreFullSymmetricValues n) :
    ‖ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T u‖≤‖u‖ :=
  ginibreOriginalStochasticL2Operator_norm_le hn α P B hB hiB T u.val

theorem ginibreOriginalSymmetricStochasticL2Operator_zero {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (u : ginibreFullSymmetricValues n) :
    ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB 0 u=u := by
  apply Subtype.ext
  rw [ginibreOriginalSymmetricStochasticL2Operator_val, ginibreOriginalStochasticL2Operator_zero]
  rfl

theorem ginibreOriginalSymmetricStochasticL2Operator_laplace {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (u : ginibreFullSymmetricValues n) :
    (∫ s in Ioi (0 : ℝ), (((α : ℝ)/(n : ℝ))*Real.exp (-((α : ℝ)/(n : ℝ))*s)) •
      ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB s.toNNReal u)=
      ginibreFullSymmetricResolvent n hn u := by
  have hc : 0<(α : ℝ)/(n : ℝ) := div_pos hα (Nat.cast_pos.mpr hn)
  have hI := actualContractionLaplace_integrable
    (ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_continuous hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_norm_le hn α P B hB hiB)
    ((α : ℝ)/(n : ℝ)) hc u
  apply Subtype.ext
  change (ginibreFullSymmetricValues n).subtypeL
    (∫ s in Ioi (0 : ℝ), (((α : ℝ)/(n : ℝ))*Real.exp (-((α : ℝ)/(n : ℝ))*s)) •
      ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB s.toNNReal u)=_
  rw [← (ginibreFullSymmetricValues n).subtypeL.integral_comp_comm hI]
  change ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) u.val=_
  exact ginibreOriginalStochasticL2Resolvent_eq_analytic hn α hα P B hB hiB u

end
end GinibrePoincare

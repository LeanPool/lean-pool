/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorStochasticSemigroup.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorSemigroupComparison
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorStochasticResolvent
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Semigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2ZeroSpeed
/-!
# Correspondence operator stochastic semigroup

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_complex_stochastic_semigroup_eq`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The original Brownian-driven Ginibre diffusion is exactly the unrestricted
analytic weak-form semigroup, at the paper's speed α/n. -/
theorem correspondenceOperator_stochastic_semigroup_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB T =
      correspondenceOperatorRealEvolution n hn ((α/n)*T) := by
  by_cases hα : α=0
  · subst α
    apply ContinuousLinearMap.ext
    intro u
    rw [ginibreOriginalStochasticL2Operator_zero_speed]
    simp only [zero_div, zero_mul]
    exact (correspondenceOperatorRealEvolution_zero_apply hn u).symm
  · have hαp : 0<(α : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hα)
    have hc : 0<α/(n : ℝ≥0) := div_pos (pos_iff_ne_zero.mpr hα)
      (by exact_mod_cast hn)
    apply correspondenceOperatorContractionSemigroup_eq_from_actual_laplace hn
      (ginibreOriginalStochasticL2Operator hn α P B hB hiB)
      (ginibreOriginalStochasticL2Operator_strong_continuous hn α P B hB hiB)
      (ginibreOriginalStochasticL2Operator_norm_le hn α P B hB hiB)
      (by intro s t u; rw [ginibreOriginalStochasticL2Operator_semigroup]; rfl)
      (by intro u; rw [ginibreOriginalStochasticL2Operator_zero]; rfl) (α/n) hc
    intro u
    simpa only [NNReal.coe_div, NNReal.coe_natCast, ginibreOriginalStochasticL2Resolvent] using
      correspondenceOperator_stochastic_resolvent_eq hn α hαp P B hB hiB u

/-- The actual stochastic transition on complex observables acts componentwise
on the real and imaginary L² classes; these are the literal two components
of the complex expectation. -/
def correspondenceOperatorComplexStochasticTransition {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : GinibreFullComplexL2 n) : GinibreFullComplexL2 n :=
  ginibreFullComplexOfReal n
    (ginibreOriginalStochasticL2Operator hn α P B hB hiB T (ginibreFullComplexRe n f)) +
  Complex.I • ginibreFullComplexOfReal n
    (ginibreOriginalStochasticL2Operator hn α P B hB hiB T (ginibreFullComplexIm n f))

/-- Stochastic and analytic identification on the entire unrestricted complex
L² space, including all nonsymmetric observables. -/
theorem correspondenceOperator_complex_stochastic_semigroup_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : GinibreFullComplexL2 n) :
    correspondenceOperatorComplexStochasticTransition hn α P B hB hiB T f =
      correspondenceOperatorEvolution n hn ((α/n)*T) f := by
  unfold correspondenceOperatorComplexStochasticTransition
  rw [correspondenceOperator_stochastic_semigroup_eq hn α P B hB hiB T]
  rw [← correspondenceOperatorEvolution_ofReal,← correspondenceOperatorEvolution_ofReal,
    ← map_smul,← map_add, ginibreFullComplex_decomposition]

end
end GinibrePoincare

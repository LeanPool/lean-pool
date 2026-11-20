/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorInvariantDensity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorOUSmoothing
public import LeanPool.GinibrePoincare.Analysis.CollisionNull
public import LeanPool.GinibrePoincare.Analysis.GinibreMassFiniteness
public import Mathlib.Probability.Kernel.Composition.MeasureComp
/-!
# Correspondence operator invariant density

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_invariant_absolutelyContinuous_ginibre`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
/-- Ginibre and configuration Lebesgue measure have the same null sets. -/
theorem correspondenceOperator_volume_absolutelyContinuous_ginibre {n : ℕ} (hn : 0 < n) :
    (volume : Measure (Configuration n)) ≪ ginibreMeasure n := by
  have hac : (volume : Measure (Configuration n)) ≪ complexGaussianMeasure n := by
    rw [complexGaussianDensityIdentification n hn]
    apply withDensity_absolutelyContinuous'
    · apply Measurable.aemeasurable
      unfold complexGaussianDensity gaussianWeight configurationNormSq
      fun_prop
    · exact ae_of_all _ (fun z => by
        unfold complexGaussianDensity gaussianWeight
        apply ne_of_gt
        apply ENNReal.ofReal_pos.mpr
        have hnR : 0<(n : ℝ) := by exact_mod_cast hn
        positivity)
  exact hac.trans (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure (ginibreMassEvaluation
      n hn))

/-- Every positive-time concrete Brownian transition has a density against the
actual invariant Ginibre measure. -/
theorem correspondenceOperator_transition_absolutelyContinuous_ginibre
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ≥0) (hα : 0 < α) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (t : ℝ≥0) (ht : 0 < t)
    (z : {z : Configuration n // CollisionFree z}) :
    ginibreBrownianTransitionKernel hn α B P t z ≪ ginibreMeasure n := by
  rw [ginibreBrownianTransitionKernel_apply_eq_process_law hn α B P hB t z]
  exact (correspondenceOperator_original_endpoint_absolutelyContinuous_volume hn α hα B P hB hind
    z.val z.property t ht).trans (correspondenceOperator_volume_absolutelyContinuous_ginibre hn)

/-- Invariance at a single strictly positive time already forces every arbitrary
initial invariant measure to possess a Ginibre density. No L² density hypothesis
or permutation symmetry is imposed. -/
theorem correspondenceOperator_invariant_absolutelyContinuous_ginibre
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ≥0) (hα : 0 < α) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (t : ℝ≥0) (ht : 0 < t)
    (ν : Measure {z : Configuration n // CollisionFree z})
    (hInv : ginibreBrownianTransitionKernel hn α B P t ∘ₘ ν = ν.map Subtype.val) :
    ν.map Subtype.val ≪ ginibreMeasure n := by
  rw [← hInv]
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  have he : (fun z => ginibreBrownianTransitionKernel hn α B P t z s)=fun _ => 0 := by
    funext z
    exact (correspondenceOperator_transition_absolutelyContinuous_ginibre hn α hα B P hB hind t ht
        z) hs0
  rw [he, lintegral_zero]
end
end GinibrePoincare

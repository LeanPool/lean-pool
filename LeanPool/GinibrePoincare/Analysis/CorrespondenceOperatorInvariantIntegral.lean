/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorInvariantIntegral.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorInvariantDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionContinuousMean
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
/-!
# Correspondence operator invariant integral

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_invariant_observable_integral`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
theorem correspondenceOperator_invariant_observable_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ≥0) (_ : 0 < α) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (ν : Measure {z : Configuration n // CollisionFree z}) [IsProbabilityMeasure ν]
    (hρ : ν.map Subtype.val ≪ ginibreMeasure n) (t : ℝ≥0)
    (hInv : ginibreBrownianTransitionKernel hn α B P t ∘ₘ ν = ν.map Subtype.val)
    (v : Configuration n → ℝ) (hv : Measurable v) (C : ℝ) (hb : ∀ z, ‖v z‖ ≤ C) :
    (∫z, ginibreStationaryContinuousTransitionMean α B P v (t : ℝ) z
      ∂(ν.map Subtype.val))=∫z, v z∂(ν.map Subtype.val) := by
  let κ := ginibreBrownianTransitionKernel hn α B P t
  have he : ginibreStationaryContinuousTransitionMean α B P v (t : ℝ) =ᵐ[ν.map Subtype.val]
      (fun z=>∫ω, v (ginibreBrownianMaximalProcess n α z B t ω)∂P) := by
    apply hρ.ae_le
    filter_upwards [ginibreStationaryContinuousTransitionMean_eq_original_ae hn α P B hB hind v]
      with z hz
    simpa using hz (t : ℝ)
  rw [(ginibreInitialCollisionEmbedding n).integral_map]
  have heν := ae_of_ae_map measurable_subtype_coe.aemeasurable he
  calc
    _ = ∫z, ∫y, v y∂κ z∂ν := by
      apply integral_congr_ae
      filter_upwards [heν] with z hz
      rw [hz]
      rw [ginibreBrownianTransitionKernel_apply_eq_process_law hn α B P hB t z]
      have hx := ginibreBrownianMaximalProcess_stronglyAdapted hn α z.val B P hB
      exact (integral_map ((hx t).mono ((ginibreBrownianAugmentedFiltration B P (fun i => (hB
          i).toIsPreBrownianReal)).le t)).measurable.aemeasurable
        hv.aestronglyMeasurable).symm
    _ = ∫y, v y∂(κ ∘ₘ ν) := by
      let := ginibreBrownianTransitionKernel_isMarkov hn α B P hB t
      have hi : Integrable v (κ ∘ₘ ν) :=
        Integrable.of_bound hv.aestronglyMeasurable C (ae_of_all _ hb)
      rw [Measure.comp_eq_comp_const_apply] at hi ⊢
      simpa using (ProbabilityTheory.Kernel.integral_comp hi).symm
    _ = _ := by rw [hInv]
end
end GinibrePoincare

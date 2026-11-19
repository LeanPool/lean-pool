/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionPermutationMean.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationNoise
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionContinuousMean

/-!
# Ginibre stochastic transition permutation mean

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreStationaryContinuousTransitionMean_permute`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreStationaryContinuousTransitionMean_permute {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (σ : ParticlePermutation n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (v : Configuration n → ℝ) (hv : Measurable v) (T : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) :
    ginibreStationaryContinuousTransitionMean α B P (fun y => v (permute σ y)) (T : ℝ) z=
      ginibreStationaryContinuousTransitionMean α B P v (T : ℝ) (permute σ z) := by
  rw [ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB _ z hz,
    ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB v (permute σ z)
      (ginibreCollisionFree_permute σ hz), Real.toNNReal_coe]
  let F := fun N : GinibreContinuousNoise n =>
    v (ginibreDrivenMaximalValue n α N.val (permute σ z) T)
  have hF : Measurable F := hv.comp (ginibreDrivenMaximalValue_measurable hn α (permute σ z) T)
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  have hPN : Measurable (fun ω => ginibreContinuousNoisePermute σ
      (ginibreBrownianFullContinuousNoise n B α ω)) :=
    (ginibreContinuousNoisePermute_continuous σ).measurable.comp hN
  have he := congrArg (fun ν : Measure (GinibreContinuousNoise n) => ∫ N, F N ∂ν)
    (ginibreBrownian_continuous_noise_permute_law σ B P hB hiB α)
  rw [integral_map hPN.aemeasurable hF.aestronglyMeasurable,
    integral_map hN.aemeasurable hF.aestronglyMeasurable] at he
  refine (integral_congr_ae (ae_of_all P ?_)).trans he
  intro ω
  change v (permute σ (ginibreDrivenMaximalValue n α _ z T))=
    v (ginibreDrivenMaximalValue n α _ (permute σ z) T)
  congr 1
  have hNoise : ((ginibreContinuousNoisePermute σ (ginibreBrownianFullContinuousNoise n B α ω)).val
      :
      ℝ → Configuration n)=fun s => permute σ ((ginibreBrownianFullContinuousNoise n B α ω).val s)
          := by
    funext s
    exact ginibreParticlePermutationCLM_apply σ _
  rw [hNoise, ginibreDrivenMaximalValue_permute]

end
end GinibrePoincare

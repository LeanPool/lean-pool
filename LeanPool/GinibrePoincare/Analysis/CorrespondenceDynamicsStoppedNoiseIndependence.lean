/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsStoppedNoiseIndependence.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsBrownianStrongMarkov
/-!
# Correspondence dynamics stopped noise independence

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrownian_stopped_noise_independent`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem correspondenceBrownian_stopped_noise_independent
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (Y : Ω → A) (hY : @Measurable Ω A hτ.measurableSpace _ Y) :
    let N := fun ω => correspondenceNoiseShift n (τ ω) (ginibreBrownianFullContinuousNoise n B α ω)
    Measurable N ∧ P.map N = P.map (ginibreBrownianFullContinuousNoise n B α) ∧
      IndepFun N Y P := by
  let N := fun ω => correspondenceNoiseShift n (τ ω) (ginibreBrownianFullContinuousNoise n B α ω)
  have htm : Measurable τ := by
    convert hτ.measurable'.untopD 0 using 1
    rfl
  have hN : Measurable N := (correspondenceNoiseShift_continuous n).measurable.comp
    (htm.prodMk (ginibreBrownianFullContinuousNoise_measurable n B P hB α))
  have hLaw : P.map N = P.map (ginibreBrownianFullContinuousNoise n B α) := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using
      correspondenceBrownian_stopping_fresh_noise n B P hB hind α τ hτ univ MeasurableSet.univ
  refine ⟨hN, hLaw,?_⟩
  apply (indepFun_iff_measure_inter_preimage_eq_mul).mpr
  intro C D hC hD
  have hh := correspondenceBrownian_stopping_fresh_noise n B P hB hind α τ hτ (Y ⁻¹' D) (hY hD)
  have hh' := congrArg (fun μ : Measure (GinibreContinuousNoise n) => μ C) hh
  rw [Measure.map_apply hN hC, Measure.restrict_apply (hN hC), _root_.smul_apply,
    ← hLaw, Measure.map_apply hN hC] at hh'
  simpa only [N, smul_eq_mul, mul_comm] using hh'

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianConditionalMarkov.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianChapmanKolmogorov

/-!
# Ginibre Hamiltonian conditional Markov

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_transition_tested_past`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

open Classical in
theorem ginibreBrownian_transition_tested_past
    {Ω A : Type*} [mAmbient : MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) s) _ Y)
    (b : Set A) (hb : MeasurableSet b)
    (a : Set {z : Configuration n // CollisionFree z}) (ha : MeasurableSet a) :
    P {ω | Y ω ∈ b ∧ ginibreBrownianStateProcess α z B (s+t) ω ∈ a} =
      ∫⁻ ω, if Y ω ∈ b then
        ginibreBrownianStateTransitionKernel α B P t (ginibreBrownianStateProcess α z B s ω) a else
            0 ∂P := by
  classical
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let Z := fun ω => (Y ω, ginibreBrownianStateProcess α z B s ω)
  let μ := P.map (ginibreBrownianFullContinuousNoise n B α)
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let : IsProbabilityMeasure μ := (by infer_instance)
  have hZa : Measurable Z := (hY.prodMk
    (ginibreBrownianStateProcess_adapted hn α z B P hB s)).mono (F.le s) le_rfl
  have hYamb : Measurable Y := hY.mono (F.le s) le_rfl
  have hXa : Measurable (ginibreBrownianStateProcess α z B (s+t)) :=
    (ginibreBrownianStateProcess_adapted hn α z B P hB (s+t)).mono (F.le (s+t)) le_rfl
  let g := fun p : (A × {z : Configuration n // CollisionFree z}) × GinibreContinuousNoise n =>
    (p.1.1, ginibreCanonicalStateValue α t (p.1.2, p.2))
  have hg : Measurable g := (measurable_fst.comp measurable_fst).prodMk
    ((ginibreCanonicalStateValue_measurable hn α t).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hK : Measurable (fun y : A × {z : Configuration n // CollisionFree z} =>
      if y.1 ∈ b then ginibreBrownianStateTransitionKernel α B P t y.2 a else 0) :=
    (((ginibreBrownianStateTransitionKernel α B P t).measurable_coe ha).comp measurable_snd).ite
      (hb.preimage measurable_fst) measurable_const
  change P ((fun ω => (Y ω, ginibreBrownianStateProcess α z B (s+t) ω)) ⁻¹' (b ×ˢ a)) = _
  rw [← Measure.map_apply (hYamb.prodMk hXa) (hb.prod ha),
    ginibreBrownian_future_past_joint_law hn α z B P hB hind s t Y hY,
    Measure.map_apply hg (hb.prod ha), Measure.prod_apply (hg (hb.prod ha))]
  rw [← lintegral_map hK hZa]
  apply lintegral_congr
  intro y
  change μ (Prod.mk y ⁻¹' (g ⁻¹' (b ×ˢ a))) = _
  by_cases hy : y.1 ∈ b
  · simp only [hy, ite_true]
    have he : Prod.mk y ⁻¹' (g ⁻¹' (b ×ˢ a)) =
        (fun N => ginibreCanonicalStateValue (α : ℝ) t (y.2, N)) ⁻¹' a := by
      ext N
      simp [g, hy]
    rw [he]
    change μ ((fun N => ginibreCanonicalStateValue (α : ℝ) t (y.2, N)) ⁻¹' a) =
      ginibreCanonicalStateTransitionKernel (α : ℝ) t μ y.2 a
    rw [ginibreCanonicalStateTransitionKernel_apply hn]
    have hf : Measurable (fun N => ginibreCanonicalStateValue (α : ℝ) t (y.2, N)) :=
      (ginibreCanonicalStateValue_measurable hn α t).comp (measurable_const.prodMk measurable_id)
    exact (Measure.map_apply hf ha).symm
  · simp only [hy, ite_false]
    have he : Prod.mk y ⁻¹' (g ⁻¹' (b ×ˢ a)) = ∅ := by
      ext N
      simp [g, hy]
    rw [he, measure_empty]

end
end GinibrePoincare

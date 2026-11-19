/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianChapmanKolmogorov.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMarkovLaw

/-!
# Ginibre Hamiltonian Chapman Kolmogorov

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownianStateTransitionKernel_chapmanKolmogorov`,
`ginibreBrownianStateTransitionKernel_zero`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- The time-`t` transition kernel on collision-free configurations whose noise law is the image
of `P` under the Brownian driving noise of `B`. -/
def ginibreBrownianStateTransitionKernel {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) (t : ℝ≥0) :
    Kernel {z : Configuration n // CollisionFree z} {z : Configuration n // CollisionFree z} :=
  ginibreCanonicalStateTransitionKernel α t (P.map (ginibreBrownianFullContinuousNoise n B α))

theorem ginibreBrownianStateTransitionKernel_apply_eq_process_law
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (t : ℝ≥0) (z : {z : Configuration n // CollisionFree z}) :
    ginibreBrownianStateTransitionKernel α B P t z = P.map (ginibreBrownianStateProcess α z B t) :=
        by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let : IsProbabilityMeasure (P.map (ginibreBrownianFullContinuousNoise n B α)) :=
    (by infer_instance)
  unfold ginibreBrownianStateTransitionKernel
  have hf : Measurable (fun N => ginibreCanonicalStateValue (α : ℝ) t (z, N)) :=
    (ginibreCanonicalStateValue_measurable hn α t).comp (measurable_const.prodMk measurable_id)
  rw [ginibreCanonicalStateTransitionKernel_apply hn, Measure.map_map hf hm]
  rfl

theorem ginibreBrownian_state_future_law {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    P.map (ginibreBrownianStateProcess α z B (s+t)) =
      ((P.map (ginibreBrownianStateProcess α z B s)).prod
        (P.map (ginibreBrownianFullContinuousNoise n B α))).map (ginibreCanonicalStateValue α t) :=
            by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let Z := ginibreBrownianStateProcess α z B s
  let N := ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α
  have hZpast : @Measurable Ω _ (F s) _ Z := ginibreBrownianStateProcess_adapted hn α z B P hB s
  have hZa : Measurable Z := hZpast.mono (F.le s) le_rfl
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  have hNa : Measurable N := ginibreBrownianFullContinuousNoise_measurable n _ P hBs α
  have hi := (brownianFamily_future_continuous_noise_independent_augmented_variable
    n B P hB hind α s Z hZpast).symm
  have hLaw := hi.map_prod_eq_prod_map_map hZa.aemeasurable hNa.aemeasurable
  rw [← brownianFamily_shift_continuous_noise_law_eq n B P hB hind α s,
    ← hLaw, Measure.map_map (ginibreCanonicalStateValue_measurable hn α t) (hZa.prodMk hNa)]
  exact Measure.map_congr (ginibreBrownian_state_restart_ae hn α z B P hB hind s t)

theorem ginibreBrownianStateTransitionKernel_chapmanKolmogorov
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    ginibreBrownianStateTransitionKernel α B P (s+t) =
      (ginibreBrownianStateTransitionKernel α B P t) ∘ₖ
        (ginibreBrownianStateTransitionKernel α B P s) := by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let μ := P.map (ginibreBrownianFullContinuousNoise n B α)
  let : IsProbabilityMeasure μ := (by infer_instance)
  ext z a ha
  rw [Kernel.comp_apply' _ _ z ha, ginibreBrownianStateTransitionKernel_apply_eq_process_law hn α B
      P hB (s+t),
    ginibreBrownian_state_future_law hn α z B P hB hind s t,
    ginibreBrownianStateTransitionKernel_apply_eq_process_law hn α B P hB s]
  rw [Measure.map_apply (ginibreCanonicalStateValue_measurable hn α t) ha,
    Measure.prod_apply ((ginibreCanonicalStateValue_measurable hn α t) ha)]
  apply lintegral_congr
  intro y
  change μ (Prod.mk y ⁻¹' (ginibreCanonicalStateValue (α : ℝ) t ⁻¹' a)) =
    ginibreCanonicalStateTransitionKernel (α : ℝ) t μ y a
  rw [ginibreCanonicalStateTransitionKernel_apply hn]
  have hf : Measurable (fun N => ginibreCanonicalStateValue (α : ℝ) t (y, N)) :=
    (ginibreCanonicalStateValue_measurable hn α t).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hf ha]
  rfl

theorem ginibreBrownianStateTransitionKernel_zero
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    ginibreBrownianStateTransitionKernel α B P 0=Kernel.id := by
  ext1 z
  rw [ginibreBrownianStateTransitionKernel_apply_eq_process_law hn α B P hB]
  have he : ginibreBrownianStateProcess α z B 0=(fun _ => z) := by
    funext ω
    apply Subtype.ext
    let N := ginibreBrownianFullContinuousNoise n B α ω
    change ginibreDrivenMaximalValue n α N.val z.val 0=z.val
    simpa only [ginibreDrivenMaximalPath, Real.toNNReal_zero] using
      ginibreDrivenMaximalPath_initial n α N.val N.val.continuous N.property z.val z.property
  rw [he, Measure.map_const]
  simp [Kernel.id_apply]

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOUReferenceStopped.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUReferenceProcess
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitCountableEvaluation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime

/-! The actual global OU reference admits genuine compact collision-free
stopping on every prescribed positive finite horizon. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreHamiltonianOU_reference_compact_stopped_exists {Ω : Type*} [mAmbient :
    MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (T : ℝ≥0) (hT : 0 < T) :
    ∃ K : Set (Configuration n), IsCompact K ∧ (∀ x ∈ K, CollisionFree x) ∧
      ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, Y t ω ∈ K) ∧
      (∀ ω, Y 0 ω = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
          Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0 < θ ω ∧ θ ω ≤ T) ∧
      (∀ t ω, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω) ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • Y s.toNNReal ω := by
  obtain ⟨ρ, hρ, hBall⟩ := Metric.mem_nhds_iff.mp ((isOpen_collisionFree n).mem_nhds hz)
  let r := ρ/2
  have hr : 0 < r := by dsimp [r]; linarith
  let K := Metric.closedBall z r
  have hKCF : ∀ x ∈ K, CollisionFree x := by
    intro x hx
    apply hBall
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by dsimp [r]; linarith)
  let U := ginibreHamiltonianOUReferenceProcess n α z B
  have hUC := ginibreHamiltonianOUReferenceProcess_continuous n α z B
  have hUA := ginibreHamiltonianOUReferenceProcess_stronglyAdapted n α z B P hB
  let V : ℝ≥0 → Ω → Configuration n := fun t ω => U t ω-z
  have hVC (ω : Ω) : Continuous (fun t => V t ω) := (hUC ω).sub continuous_const
  have hVA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
      i).toIsPreBrownianReal)) V :=
    fun t => (hUA t).sub stronglyMeasurable_const
  let θ := hittingBtwn V {x | r ≤ ‖x‖} 0 T
  have hStop := ginibreContinuous_norm_exit_isStoppingTime _ V hVA hVC r T
  have hθT (ω : Ω) : θ ω ≤ T := hittingBtwn_le ω
  have hθpos (ω : Ω) : 0 < θ ω :=
    drivenContinuous_closed_hitting_pos V _ (isClosed_le continuous_const continuous_norm) T hT ω
      (hVC ω) (by simpa [V, U, ginibreHamiltonianOUReferenceProcess_zero] using not_le_of_gt hr)
  let Y : ℝ≥0 → Ω → Configuration n := fun t ω => U (min t (θ ω)) ω
  have hYC (ω : Ω) : Continuous (fun t => Y t ω) := (hUC ω).comp (continuous_id.min
      continuous_const)
  have hYR (t : ℝ≥0) (ω : Ω) : Y t ω ∈ K := by
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    exact drivenContinuous_norm_le_until_hitting V r T ω (hVC ω)
      (by simp [V, U, ginibreHamiltonianOUReferenceProcess_zero, hr.le]) _ (min_le_right t (θ ω))
  have hYA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
      i).toIsPreBrownianReal)) Y := by
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    intro s
    have hm (k : ℕ) : @StronglyMeasurable Ω (Configuration n) _ (F s)
        (fun ω => U (min s (stoppingUpperGrid k (θ ω))) ω) :=
      (adapted_capped_upper_grid_evaluation_measurable F U hUA.adapted θ hStop k
          s).stronglyMeasurable
    apply stronglyMeasurable_of_tendsto atTop hm
    rw [tendsto_pi_nhds]
    intro ω
    exact (hUC ω).continuousAt.tendsto.comp (tendsto_const_nhds.min (stoppingUpperGrid_tendsto (θ
        ω)))
  refine ⟨K, isCompact_closedBall z r, hKCF, Y, hYC, hYR,?_, hYA, θ, hStop,
    fun ω => ⟨hθpos ω, hθT ω⟩, fun t ω => rfl,?_⟩
  · intro ω
    simp [Y, U, ginibreHamiltonianOUReferenceProcess_zero]
  · filter_upwards [ginibreHamiltonianOUReferenceProcess_original_equation n α z B P hB] with ω hω
    intro t ht
    change U (min t (θ ω)) ω = _
    have huEq : U t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • U s.toNNReal ω := hω t
    rw [min_eq_left ht, huEq]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) (t : ℝ) := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hs
    have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hsI.2
    change (-2*α/(n : ℝ)) • U s.toNNReal ω = (-2*α/(n : ℝ)) • U (min s.toNNReal (θ ω)) ω
    rw [min_eq_left (hst.trans ht)]

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsStoppedPast.lean.
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
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianStoppedAdaptation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion
/-!
# Correspondence dynamics stopped past

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem correspondence_ginibre_stopped_value_measurable
    {Ω : Type*} [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) (fun ω => (τ ω : WithTop ℝ≥0))) :
    @Measurable Ω (Configuration n) hτ.measurableSpace _
      (fun ω => ginibreBrownianMaximalProcess n α z B (τ ω) ω) := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have hzero : F 0 ≤ hτ.measurableSpace := hτ.le_measurableSpace_of_const_le
    (fun ω => WithTop.coe_le_coe.mpr (bot_le : (0 : ℝ≥0) ≤ τ ω))
  have hnull (A : Set Ω) (hA : P A = 0) : MeasurableSet[hτ.measurableSpace] A :=
    hzero A (ginibreNullAugmentation_null_measurable P _ A hA)
  let μ := P.trim hτ.measurableSpace_le
  let : μ.IsComplete := by
    constructor
    intro A hA
    exact hnull A (measure_eq_zero_of_trim_eq_zero hτ.measurableSpace_le hA)
  let U : ℕ → ℝ≥0 → Ω → Configuration n := fun k =>
    ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k
  have hU (k : ℕ) : IsStronglyProgressive F (U k) :=
    (ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB _
      (le_add_of_nonneg_right (Nat.cast_nonneg k)) k).isStronglyProgressive_of_continuous
      (ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B _
        (le_add_of_nonneg_right (Nat.cast_nonneg k)) k)
  let g : ℕ → Ω → Configuration n := fun k ω => U k (τ ω) ω
  have hg (k : ℕ) : @Measurable Ω (Configuration n) hτ.measurableSpace _ (g k) := by
    convert measurable_stoppedValue (hU k) hτ using 1
    funext ω
    change U k (τ ω) ω = U k (WithTop.untopA (τ ω : WithTop ℝ≥0)) ω
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hl : ∀ᵐ ω ∂P, Tendsto (fun k => g k ω) atTop
      (𝓝 (ginibreBrownianMaximalProcess n α z B (τ ω) ω)) := by
    filter_upwards [ginibreBrownianHamiltonianBoundedStop_exhausts_ae hn α z hz B P hB hind]
      with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω (τ ω)] with k hk
    change ginibreBrownianMaximalProcess n α z B (τ ω) ω =
      ginibreBrownianMaximalProcess n α z B
        (min (τ ω) (ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k ω)) ω
    rw [min_eq_left hk]
  have hlμ : ∀ᵐ ω ∂μ, Tendsto (fun k => g k ω) atTop
      (𝓝 (ginibreBrownianMaximalProcess n α z B (τ ω) ω)) := by
    rw [ae_iff] at hl ⊢
    rw [trim_measurableSet_eq _ (hnull _ hl)]
    exact hl
  exact (aemeasurable_iff_measurable (μ := μ)).mp
    (aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hg k).aestronglyMeasurable)
        hlμ).aemeasurable

end
end GinibrePoincare

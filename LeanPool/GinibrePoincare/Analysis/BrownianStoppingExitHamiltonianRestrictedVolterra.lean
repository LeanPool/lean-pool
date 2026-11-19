/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianRestrictedVolterra.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianStoppedAdaptation

/-! Actual plain-noise equation on the survival event, and uniform compact drift bounds. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianHamiltonianStoppedProcess_initial {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω) :
    ginibreBrownianHamiltonianStoppedProcess n α z B R T 0 ω = z := by
  change ginibreDrivenMaximalValue n α _ z (min 0 _) = z
  rw [min_eq_left (zero_le : (0 : ℝ≥0) ≤ _)]
  have hi := ginibreDrivenMaximalPath_initial n α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz
  simpa only [ginibreDrivenMaximalPath, Real.toNNReal_zero] using hi

theorem ginibreBrownianHamiltonianStoppedProcess_restricted_volterra {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T S : ℝ≥0) :
    ∀ᵐ ω ∂P, S ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω →
      ∀ t ∈ Icc 0 S,
        ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω =
          ginibreBrownianHamiltonianStoppedProcess n α z B R T 0 ω +
          (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω
              0) +
          ∫ s in (0 : ℝ)..(t : ℝ), ginibreLangevinDrift n α
            (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω) := by
  filter_upwards [ginibreBrownianHamiltonianStoppedProcess_equation_ae hn α z hz B P hB R hR T,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω he hNoise
  intro hS t ht
  have h := (he t).2
  rw [min_eq_left (ht.2.trans hS)] at h
  have hzero : ginibreConfigurationBrownianNoise n B α ω 0 = 0 := by
    rw [← hNoise 0]
    exact (ginibreBrownianFullContinuousNoise n B α ω).property
  rw [ginibreBrownianHamiltonianStoppedProcess_initial n α z hz B R T ω, hzero, sub_zero]
  exact h

theorem ginibreBrownianHamiltonianStoppedDrift_continuous {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) :
    Continuous (fun s : ℝ => ginibreLangevinDrift n α
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω)) := by
  have hX : Continuous (fun s : ℝ =>
      ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω) :=
    (ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B R hR T ω).comp
      continuous_real_toNNReal
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (ginibreLangevinDrift_contDiffAt n α
    (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω)
    (ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T (Real.toNNReal s)
        ω).1).continuousAt.comp
      (f := fun u : ℝ => ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal u) ω)
      (x := s) hX.continuousAt

theorem ginibreBrownianHamiltonianStoppedDrift_bounded {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) : ∃ M > (0 : ℝ), ∀ s : ℝ, ∀ ω : Ω,
      ‖ginibreLangevinDrift n α
        (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω)‖ ≤ M := by
  have hc : ContinuousOn (ginibreLangevinDrift n α) (ginibreHamiltonianSublevel n R) :=
    fun x hx => (ginibreLangevinDrift_contDiffAt n α x hx.1).continuousAt.continuousWithinAt
  obtain ⟨M, hM, hb⟩ := ((ginibreHamiltonianSublevel_isCompact hn R).image_of_continuousOn
      hc).isBounded.exists_pos_norm_le
  refine ⟨M, hM, fun s ω => hb _ ?_⟩
  exact ⟨_, ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T (Real.toNNReal s) ω,
      rfl⟩

theorem ginibreBrownianHamiltonianBoundedStop_survival_measurable {Ω : Type*}
    [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T S : ℝ≥0) : MeasurableSet {ω | S ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω} := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have hs := (ginibreBrownianHamiltonianBoundedStop_isStoppingTime hn α z hz B P hB R hR
      T).measurableSet_ge S
  have hm := F.le S _ hs
  convert hm using 1
  ext ω
  change (S ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) ↔
    ((S : ℝ≥0∞) ≤ (ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ≥0∞))
  exact ENNReal.coe_le_coe.symm

end
end GinibrePoincare

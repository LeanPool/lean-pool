/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinNoiseStability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinLocal
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathLocalStability

/-! # Noise stability for the actual locally regular gradient flow
This provides the local quantitative continuity needed for measurable stochastic
flow selection. The drift's compact Lipschitz coefficient is proved internally.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ContDiff NNReal Topology
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual C² gradient drift is Lipschitz on every compact Euclidean ball. -/
theorem bakryEmeryLangevinDrift_closedBall_lipschitz (W : E → ℝ)
    (hW : ContDiff ℝ 2 W) (R : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (bakryEmeryLangevinDrift W) (closedBall 0 R) := by
  have hb : ContDiff ℝ 1 (bakryEmeryLangevinDrift W) :=
    contDiff_iff_contDiffAt.mpr (fun x => bakryEmeryLangevinDrift_contDiffAt W x hW.contDiffAt)
  have hd : Continuous (fun x => ‖fderiv ℝ (bakryEmeryLangevinDrift W) x‖) :=
    (hb.continuous_fderiv (by norm_num)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hd.continuousOn
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K, Convex.lipschitzOnWith_of_nnNorm_fderiv_le
    (fun x _ => (hb.differentiable (by norm_num)) x) ?_ (convex_closedBall 0 R)⟩
  intro x hx
  have hh := hC x hx
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hh
  exact_mod_cast hh.trans (le_max_left C 0)

/-- Two actual confined solutions depend continuously on their additive noise.
The comparison uses an internally constructed Lipschitz extension of the actual
compact-ball drift, and the equations remain those of the original drift. -/
theorem bakryEmeryLangevin_noise_stability_on_ball (W : E → ℝ)
    (hW : ContDiff ℝ 2 W) (R : ℝ) :
    ∃ K : ℝ≥0, ∀ (a : E) (N M X Y : ℝ → E) (T δ : ℝ),
      0 ≤ T → 0 ≤ δ →
      ContinuousOn X (Icc 0 T) → ContinuousOn Y (Icc 0 T) →
      (∀ t ∈ Icc 0 T, X t ∈ closedBall 0 R) →
      (∀ t ∈ Icc 0 T, Y t ∈ closedBall 0 R) →
      (∀ t ∈ Icc 0 T, X t = a + N t +
        ∫ s in (0 : ℝ)..t, bakryEmeryLangevinDrift W (X s)) →
      (∀ t ∈ Icc 0 T, Y t = a + M t +
        ∫ s in (0 : ℝ)..t, bakryEmeryLangevinDrift W (Y s)) →
      (∀ t ∈ Icc 0 T, ‖N t - M t‖ ≤ δ) →
      ∀ t ∈ Icc 0 T, ‖X t - Y t‖ ≤ δ * Real.exp ((K : ℝ) * T) := by
  obtain ⟨K, hK⟩ := bakryEmeryLangevinDrift_closedBall_lipschitz W hW R
  obtain ⟨g, hg, heq⟩ := hK.extend_finite_dimension
  refine ⟨lipschitzExtensionConstant E * K, ?_⟩
  intro a N M X Y T δ hT hδ hX hY hXR hYR hEqX hEqY hNM
  have hInt (Z : ℝ → E) (hZR : ∀ t ∈ Icc 0 T, Z t ∈ closedBall 0 R)
      (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ s in (0 : ℝ)..t, g (Z s)) =
        ∫ s in (0 : ℝ)..t, bakryEmeryLangevinDrift W (Z s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact (heq (hZR s ⟨hs.1, hs.2.trans ht.2⟩)).symm
  have hEqXg (t : ℝ) (ht : t ∈ Icc 0 T) : X t = a + N t + ∫ s in (0 : ℝ)..t, g (X s) := by
    rw [hInt X hXR t ht]
    exact hEqX t ht
  have hEqYg (t : ℝ) (ht : t ∈ Icc 0 T) : Y t = a + M t + ∫ s in (0 : ℝ)..t, g (Y s) := by
    rw [hInt Y hYR t ht]
    exact hEqY t ht
  exact drivenVolterra_lipschitz_stability_on g _ hg a N M X Y T δ hT hδ hX hY hEqXg hEqYg hNM

end
end GinibrePoincare

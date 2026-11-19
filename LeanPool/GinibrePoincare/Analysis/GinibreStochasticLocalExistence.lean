/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLocalExistence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathLocalUniqueness
public import Mathlib.Probability.BrownianMotion.Basic

/-! # Actual local collision-free Brownian-driven Ginibre paths

The cumulative noise has the paper's coefficient √(2α/n²). Independence of
coordinates is unnecessary for this pathwise existence theorem; it is needed
for the associated isotropic diffusion law.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The configuration noise `t ↦ (√(2α / n²) (B (j, 0) t + i B (j, 1) t))ⱼ` built from the real
Brownian family `B`, with negative times sent to `0`. -/
def ginibreConfigurationBrownianNoise {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) (t : ℝ) : Configuration n :=
  fun j => Real.sqrt (2*α/(n : ℝ)^2) •
    ((B (j, 0) t.toNNReal ω : ℂ)+Complex.I*(B (j, 1) t.toNNReal ω : ℂ))

theorem ginibreConfigurationBrownianNoise_actual {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, Continuous (ginibreConfigurationBrownianNoise n B α ω) ∧
      ginibreConfigurationBrownianNoise n B α ω 0 = 0 := by
  have hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) :=
    ae_all_iff.mpr (fun i => (hB i).cont)
  have hz : ∀ᵐ ω ∂P, ∀ i, B i 0 ω = 0 :=
    ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
  filter_upwards [hc, hz] with ω hc hz
  constructor
  · apply continuous_pi
    intro j
    exact ((Complex.continuous_ofReal.comp ((hc (j, 0)).comp continuous_real_toNNReal)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        ((hc (j, 1)).comp continuous_real_toNNReal)))).const_smul (Real.sqrt (2*α/(n : ℝ)^2))
  · ext j
    simp [ginibreConfigurationBrownianNoise, hz]

theorem ginibreBrownian_driven_local_collision_free_exists {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) :
    ∀ᵐ ω ∂P, ∃ τ > (0 : ℝ), ∃ X : ℝ → Configuration n,
      ContinuousOn X (Icc 0 τ) ∧ X 0 = z ∧
      ∀ t ∈ Icc 0 τ, CollisionFree (X t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t ∧
        X t = z+ginibreConfigurationBrownianNoise n B α ω t+
          ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u) := by
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  exact ginibreDrivenPath_continuous_noise_local_exists n α z hz _ hω.1 hω.2

end
end GinibrePoincare

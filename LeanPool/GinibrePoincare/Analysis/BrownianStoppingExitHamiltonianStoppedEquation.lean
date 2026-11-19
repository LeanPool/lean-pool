/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianStoppedEquation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianStoppedPath

/-! The actual localized path has the genuine stopped-original-noise Volterra equation. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianHamiltonianStoppedProcess_eq_before {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T t : ℝ≥0) (ω : Ω)
    (ht : t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) :
    ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω =
      ginibreBrownianMaximalProcess n α z B t ω := by
  unfold ginibreBrownianHamiltonianStoppedProcess
  rw [min_eq_left ht]

theorem ginibreBrownianHamiltonianStoppedProcess_equation_ae {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      let s := min t (ginibreBrownianHamiltonianBoundedStop n α z B R T ω)
      IntervalIntegrable (fun u : ℝ => ginibreLangevinDrift n α
        (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal u) ω)) volume 0 (s : ℝ)
            ∧
      ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω =
        z + ginibreConfigurationBrownianNoise n B α ω s +
        ∫ u in (0 : ℝ)..(s : ℝ), ginibreLangevinDrift n α
          (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal u) ω) := by
  filter_upwards [ginibreBrownianMaximalProcess_equation_ae n α z B P hB] with ω hω
  intro t
  dsimp only
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T ω
  let s : ℝ≥0 := min t σ
  have hσ := ginibreDrivenHamiltonianBoundedStop_lt_lifetime hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T
  have hs : (s : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω :=
    (ENNReal.coe_le_coe.mpr (min_le_right t σ)).trans_lt hσ
  have he := hω s hs
  have heq (u : ℝ) (hu : u ∈ Icc 0 (s : ℝ)) :
      ginibreBrownianMaximalProcess n α z B (Real.toNNReal u) ω =
        ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal u) ω := by
    symm
    apply ginibreBrownianHamiltonianStoppedProcess_eq_before
    have hus : Real.toNNReal u ≤ s := by
      exact_mod_cast (show (Real.toNNReal u : ℝ) ≤ (s : ℝ) by rw [Real.coe_toNNReal u hu.1]; exact
                                                                hu.2)
    exact hus.trans (min_le_right t σ)
  have hi := he.2.1.congr (fun u hu => by
    have hu' : u ∈ Ioc (0 : ℝ) (s : ℝ) := by
      simpa only [Set.uIoc, min_eq_left s.coe_nonneg, max_eq_right s.coe_nonneg] using hu
    exact congrArg (ginibreLangevinDrift n α) (heq u ⟨hu'.1.le, hu'.2⟩))
  have hInt : (∫ u in (0 : ℝ)..(s : ℝ), ginibreLangevinDrift n α
      (ginibreBrownianMaximalProcess n α z B (Real.toNNReal u) ω)) =
    ∫ u in (0 : ℝ)..(s : ℝ), ginibreLangevinDrift n α
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal u) ω) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) (s : ℝ) := by
      simpa only [Set.uIcc_of_le s.coe_nonneg] using hu
    exact congrArg (ginibreLangevinDrift n α) (heq u hu')
  refine ⟨hi, ?_⟩
  change ginibreBrownianMaximalProcess n α z B s ω = _
  rw [← hInt]
  exact he.2.2

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCIRCoefficientProcess.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRIntegral

/-! The genuine localized CIR amplitude is bounded, continuous and adapted:
all stochastic integral coefficient hypotheses follow from actual compact localization. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- A continuous function of the Hamiltonian-stopped configuration is adapted, has continuous
paths, and is bounded, since the stopped process stays in a compact Hamiltonian sublevel set. -/
theorem ginibreBrownianHamiltonianStoppedProcess_continuous_function_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (f : Configuration n → ℝ) (hf : Continuous f) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun t ω => f (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)) ∧
    (∀ ω, Continuous (fun t => f (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω))) ∧
    ∃ C > (0 : ℝ), ∀ t ω, ‖f (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)‖ ≤ C := by
  have hAdapt := ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB R hR T
  have hCont := ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B R hR T
  refine ⟨fun t => (hf.measurable.comp (hAdapt t).measurable).stronglyMeasurable,
    fun ω => hf.comp (hCont ω),?_⟩
  obtain ⟨C, hC, hb⟩ := ((ginibreHamiltonianSublevel_isCompact hn R).image
      hf).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun t ω => hb _ ?_⟩
  exact ⟨_, ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T t ω, rfl⟩

/-- At a uniform grid time of `[0, t]`, with `t` before the Hamiltonian stop, the stopped
configuration is the maximal one. -/
theorem ginibreBrownianHamiltonianStoppedProcess_grid_eq_maximal
    {Ω : Type*} {n : ℕ} (α : ℝ) (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (R : ℝ) (T t : ℝ≥0) (k j : ℕ) (hj : j ∈ Finset.range (k + 1)) (ω : Ω)
    (ht : t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) :
    ginibreBrownianHamiltonianStoppedProcess n α z B R T (itoUniformNNTime t (k + 1) j) ω =
      ginibreBrownianMaximalProcess n α z B (itoUniformNNTime t (k + 1) j) ω := by
  change ginibreBrownianMaximalProcess n α z B
    (min (itoUniformNNTime t (k+1) j) (ginibreBrownianHamiltonianBoundedStop n α z B R T ω)) ω = _
  rw [min_eq_left ((itoUniformNNTime_le_end t (k+1) j (Nat.succ_pos k)
    (Finset.mem_range.mp hj).le).trans ht)]

theorem ginibreBrownianHamiltonianStoppedProcess_CIR_amplitude_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    let a := fun t ω => Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω))
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) a
        ∧
    (∀ ω, Continuous (fun t => a t ω)) ∧
    ∃ C > (0 : ℝ), ∀ t ω, ‖a t ω‖ ≤ C := by
  exact ginibreBrownianHamiltonianStoppedProcess_continuous_function_properties hn α z hz B P hB
    R hR T (fun x => Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius x))
    (Real.continuous_sqrt.comp
      (continuous_const.mul (ginibre_contDiff_pairwiseRadius n).continuous))
end
end GinibrePoincare

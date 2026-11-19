/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterSmallProbability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterBarrierExpectation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Genuine logarithmic small-center probability estimates for the original SDE. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_small_stopped_probability
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 ≤ δ → δ < C → ∀ ε : ℝ, 0 < ε →
      ∀ τ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (τ ω : WithTop ℝ≥0)) →
      (∀ ω, τ ω ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) →
      P.real {ω | ginibreCenterSquared n (ginibreBrownianHamiltonianStoppedProcess n α z B R T (τ ω)
          ω) ≤ δ} ≤
        (Real.log (C+ε)-Real.log (ginibreCenterSquared n z+ε)+(4*(α : ℝ)/(n : ℝ))*(T : ℝ))/
          (Real.log (C+ε)-Real.log (δ+ε)) := by
  obtain ⟨C, hC, hBound⟩ := ginibreHamiltonianSublevel_centerSquared_bound (show 0 < n by omega) R
  refine ⟨C, hC,?_⟩
  intro δ hδ hδC ε hε τ hτ hτσ
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let Y := fun ω => ginibreCenterLogBarrier n ε (X (τ ω) ω)+Real.log (C+ε)
  obtain ⟨hY0, hEY⟩ := ginibreBrownian_center_barrier_stopped_expectation hn α z hz B P hB hind R hR
      T hε τ hτ hτσ
  have hY : Integrable Y P := hY0.add (integrable_const _)
  have hnonneg : 0 ≤ᵐ[P] Y := ae_of_all P (fun ω => by
    have hb := hBound _ (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T
        (τ ω) ω)
    have hp := add_pos_of_nonneg_of_pos (ginibreCenterSquared_nonneg n (X (τ ω) ω)) hε
    have hl := Real.log_le_log hp (add_le_add hb (le_refl ε))
    change 0 ≤ -Real.log (ginibreCenterSquared n (X (τ ω) ω)+ε)+Real.log (C+ε)
    linarith)
  have hden : 0 < Real.log (C+ε)-Real.log (δ+ε) := sub_pos.mpr
    (Real.log_lt_log (add_pos_of_nonneg_of_pos hδ hε) (add_lt_add_of_lt_of_le hδC (le_refl ε)))
  have hm := mul_meas_ge_le_integral_of_nonneg hnonneg hY (Real.log (C+ε)-Real.log (δ+ε))
  have hSub : {ω | ginibreCenterSquared n (X (τ ω) ω) ≤ δ} ⊆
      {ω | Real.log (C+ε)-Real.log (δ+ε) ≤ Y ω} := by
    intro ω hω
    have hl := Real.log_le_log (add_pos_of_nonneg_of_pos (ginibreCenterSquared_nonneg n _) hε)
      (add_le_add hω (le_refl ε))
    change Real.log (C+ε)-Real.log (δ+ε) ≤ -Real.log (ginibreCenterSquared n (X (τ ω) ω)+ε)+Real.log
        (C+ε)
    linarith
  have hMeasure := measureReal_mono (μ := P) hSub
  have hMean : (∫ ω, Y ω ∂P) ≤ Real.log (C+ε)-Real.log (ginibreCenterSquared n z+ε)+
      (4*(α : ℝ)/(n : ℝ))*(T : ℝ) := by
    have he := integral_add hY0 (integrable_const (Real.log (C+ε)) (μ := P))
    simp only [integral_const, probReal_univ, one_smul] at he
    change (∫ ω, Y ω ∂P) = _ at he
    rw [he]
    unfold ginibreCenterLogBarrier at hEY ⊢
    linarith
  apply (le_div_iff₀ hden).mpr
  have hMul := mul_le_mul_of_nonneg_left hMeasure hden.le
  nlinarith
end
end GinibrePoincare

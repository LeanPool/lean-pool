/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationMaximal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationGrid

/-!
# Brownian integral continuous modification maximal

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `realMartingale_uniform_probability_cauchy`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The continuous-time maximal probability inequality follows from the actual
martingale and actual path continuity, without an assumed maximal estimate. -/
theorem realMartingale_continuous_maximal_lt_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P)
    (T : ℝ≥0) (hT : MemLp (M T) 2 P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (ε : ℝ≥0) (hε : 0 < ε) :
    P {ω | ∃ t ∈ Set.Icc 0 T, (ε : ℝ) < ‖M t ω‖} ≤
      ENNReal.ofReal (∫ ω, (M T ω)^2 ∂P)/(ε : ℝ≥0∞)^2 := by
  let E : ℕ → Set Ω := fun n =>
    {ω | ∃ k ≤ n+1, (ε : ℝ) ≤ ‖M (itoUniformNNTime T (n+1) k) ω‖}
  let A : ℕ → Set Ω := fun N => ⋂ n ≥ N, E n
  have hA : Monotone A := by
    intro i j hij ω hω
    simp only [A, Set.mem_iInter] at *
    exact fun n hn => hω n (hij.trans hn)
  have hbound : ∀ N, P (A N) ≤
      ENNReal.ofReal (∫ ω, (M T ω)^2 ∂P)/(ε : ℝ≥0∞)^2 := by
    intro N
    calc
      P (A N) ≤ P (E N) := measure_mono (by
        intro ω hω
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hω N) le_rfl)
      _ ≤ _ := realMartingale_uniform_grid_maximal_le P ℱ M hM T hT
        (N+1) (Nat.succ_pos N) ε hε
  calc
    _ ≤ P (⋃ N, A N) := measure_mono_ae (by
      filter_upwards [hcont] with ω hc
      intro hω
      have he := continuousPath_uniform_grid_detects T (fun t => M t ω) hc ε hω
      obtain ⟨N, hN⟩ := eventually_atTop.mp he
      exact Set.mem_iUnion.mpr ⟨N, Set.mem_iInter.mpr (fun n =>
        Set.mem_iInter.mpr (fun hn => hN n hn))⟩)
    _ ≤ _ := by rw [hA.measure_iUnion]; exact iSup_le hbound

/-- Differences of two actual continuous martingales satisfy the same uniform
estimate. This turns terminal mean-square Cauchy estimates into uniform
probability Cauchy estimates. -/
theorem realMartingale_continuous_difference_maximal_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M N : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M ℱ P) (hN : Martingale N ℱ P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hcontM : ∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (hcontN : ∀ᵐ ω ∂P, ContinuousOn (fun t => N t ω) (Set.Icc 0 T))
    (ε : ℝ≥0) (hε : 0 < ε) :
    P {ω | ∃ t ∈ Set.Icc 0 T, (ε : ℝ) < ‖M t ω - N t ω‖} ≤
      ENNReal.ofReal (∫ ω, (M T ω - N T ω)^2 ∂P)/(ε : ℝ≥0∞)^2 := by
  apply realMartingale_continuous_maximal_lt_le P ℱ (M-N) (hM.sub hN) T
    (hMT.sub hNT) ?_ ε hε
  filter_upwards [hcontM, hcontN] with ω hm hn
  exact hm.sub hn

/-- Genuine terminal mean-square convergence of continuous martingale
 differences implies uniform convergence in probability on the whole interval. -/
theorem realMartingale_uniform_probability_cauchy
    {Ω J : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M N : J → ℝ≥0 → Ω → ℝ)
    (hM : ∀ j, Martingale (M j) ℱ P) (hN : ∀ j, Martingale (N j) ℱ P)
    (T : ℝ≥0) (hMT : ∀ j, MemLp (M j T) 2 P) (hNT : ∀ j, MemLp (N j T) 2 P)
    (hcontM : ∀ j, ∀ᵐ ω ∂P, ContinuousOn (fun t => M j t ω) (Set.Icc 0 T))
    (hcontN : ∀ j, ∀ᵐ ω ∂P, ContinuousOn (fun t => N j t ω) (Set.Icc 0 T))
    (l : Filter J)
    (hterm : Tendsto (fun j => ∫ ω, (M j T ω - N j T ω) ^ 2 ∂P) l (𝓝 0))
    (ε : ℝ≥0) (hε : 0 < ε) :
    Tendsto (fun j => P {ω | ∃ t ∈ Set.Icc 0 T,
      (ε : ℝ) < ‖M j t ω - N j t ω‖}) l (𝓝 0) := by
  have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hterm
  have hd := ENNReal.Tendsto.div_const hn
    (b := (ε : ℝ≥0∞)^2) (Or.inr (pow_ne_zero 2 (by exact_mod_cast hε.ne')))
  simp only [ENNReal.ofReal_zero, ENNReal.zero_div] at hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
    (fun j => bot_le) (fun j => realMartingale_continuous_difference_maximal_le
      P ℱ (M j) (N j) (hM j) (hN j) T (hMT j) (hNT j) (hcontM j) (hcontN j) ε hε)

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationGrid.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationSquare
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoUniformRefinement
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Brownian integral continuous modification grid

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `realMartingale_uniform_grid_maximal_le`, `continuousPath_uniform_grid_detects`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Every time in the interval is approximated by an actual left uniform sample. -/
theorem itoUniformNNTime_exists_close (T s : ℝ≥0) (hs : s ≤ T)
    (N : ℕ) (hN : 0 < N) :
    ∃ k ≤ N, dist (itoUniformNNTime T N k) s ≤ (T : ℝ)/N := by
  by_cases hT : T = 0
  · subst T
    have : s = 0 := le_antisymm hs (bot_le)
    subst s
    exact ⟨0, Nat.zero_le _, by simp [itoUniformNNTime, itoUniformTime]⟩
  have hTR : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  let r : ℝ := (s : ℝ)*N/T
  have hr : 0 ≤ r := by positivity
  have hrN : r ≤ N := by
    dsimp [r]
    apply (div_le_iff₀ hTR).mpr
    have hsR : (s : ℝ) ≤ T := hs
    nlinarith
  let k := Nat.floor r
  have hkN : k ≤ N := Nat.floor_le_of_le hrN
  have hk : (k : ℝ) ≤ r := Nat.floor_le hr
  have hkr : r < (k : ℝ)+1 := Nat.lt_floor_add_one r
  have hleft : (T : ℝ)*k/N ≤ s := by
    apply (div_le_iff₀ hNR).mpr
    have hh := (le_div_iff₀ hTR).mp hk
    nlinarith
  have hright : (s : ℝ) - (T : ℝ)*k/N ≤ T/N := by
    have hh := (div_lt_iff₀ hTR).mp hkr
    apply (le_div_iff₀ hNR).mpr
    field_simp at *
    nlinarith
  refine ⟨k, hkN,?_⟩
  simpa [NNReal.dist_eq, itoUniformNNTime_coe, itoUniformTime,
    abs_of_nonpos (sub_nonpos.mpr hleft)] using hright

/-- Sampling a continuous-time martingale on a clipped uniform grid gives the
actual terminal-second-moment maximal estimate, with no earlier L² assumptions. -/
theorem realMartingale_uniform_grid_maximal_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P)
    (T : ℝ≥0) (hT : MemLp (M T) 2 P) (N : ℕ) (hN : 0 < N)
    (ε : ℝ≥0) (hε : 0 < ε) :
    P {ω | ∃ k ≤ N, (ε : ℝ) ≤ ‖M (itoUniformNNTime T N k) ω‖} ≤
      ENNReal.ofReal (∫ ω, (M T ω)^2 ∂P)/(ε : ℝ≥0∞)^2 := by
  let τ : ℕ → ℝ≥0 := fun k => min (itoUniformNNTime T N k) T
  have hτ : Monotone τ := (itoUniformNNTime_mono T N).min monotone_const
  have hs := realMartingale_monotone_sampling P ℱ M hM τ hτ
  have hL : ∀ k, MemLp (M (τ k)) 2 P := fun k =>
    realMartingale_memLp_two_of_le P ℱ M hM T (τ k) (min_le_right _ _) hT
  have hd := realMartingale_finite_maximal_le P _ _ hs hL ε hε N
  have hτN : τ N = T := by simp [τ, itoUniformNNTime_end T N hN]
  have he : {ω | ∃ k ≤ N, (ε : ℝ) ≤ ‖M (itoUniformNNTime T N k) ω‖} =
      {ω | ∃ k ≤ N, (ε : ℝ) ≤ ‖M (τ k) ω‖} := by
    ext ω
    constructor <;> rintro ⟨k, hk, h⟩ <;> refine ⟨k, hk,?_⟩
    · simpa [τ, min_eq_left (itoUniformNNTime_le_end T N k hN hk)] using h
    · simpa [τ, min_eq_left (itoUniformNNTime_le_end T N k hN hk)] using h
  rw [he]
  simpa only [hτN] using hd

/-- A strict excursion of a continuous path is detected on every sufficiently
fine actual uniform grid. -/
theorem continuousPath_uniform_grid_detects (T : ℝ≥0) (f : ℝ≥0 → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 T)) (ε : ℝ)
    (h : ∃ s ∈ Set.Icc 0 T, ε < ‖f s‖) :
    ∀ᶠ n : ℕ in atTop, ∃ k ≤ n+1, ε ≤ ‖f (itoUniformNNTime T (n+1) k)‖ := by
  obtain ⟨s, hs, he⟩ := h
  have hc := fun n => itoUniformNNTime_exists_close T s hs.2 (n+1) (Nat.succ_pos n)
  choose k hk hd using hc
  let a : ℕ → ℝ≥0 := fun n => itoUniformNNTime T (n+1) (k n)
  have ha : Tendsto a atTop (𝓝 s) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) hd
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have ham : ∀ n, a n ∈ Set.Icc 0 T := fun n =>
    ⟨bot_le, itoUniformNNTime_le_end T (n+1) (k n) (Nat.succ_pos n) (hk n)⟩
  have hw : Tendsto a atTop (𝓝[Set.Icc 0 T] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha, Eventually.of_forall ham⟩
  have hn := ((hf s hs).tendsto.comp hw).norm
  filter_upwards [hn.eventually (eventually_gt_nhds he)] with n hn
  exact ⟨k n, hk n, hn.le⟩

end
end GinibrePoincare

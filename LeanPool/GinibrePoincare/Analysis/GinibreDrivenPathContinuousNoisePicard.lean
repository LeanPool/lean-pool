/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathContinuousNoisePicard.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathDriftRegularity
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Local existence with an actual continuous additive driving path -/

@[expose] public section
open Set Metric
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem drivenContinuousNoise_lipschitz_local_correction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (N : ℝ → E) (hN : Continuous N) (z : E) :
    ∃ Y : ℝ → E, Y 0 = z ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt Y (b (Y t+N t)) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      hN.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (N 0)).trans (hC 0 (by norm_num))
  let L : ℝ≥0 := ⟨‖b z‖+(K : ℝ)*(1+C), by positivity⟩
  let ε : ℝ≥0 := min 1 (L+1)⁻¹
  have hε : 0 < (ε : ℝ) := by
    dsimp [ε]
    exact_mod_cast (lt_min (by norm_num : (0 : ℝ≥0) < 1) (inv_pos.mpr (by positivity : 0 < L+1)))
  have hε1 : (ε : ℝ) ≤ 1 := by exact_mod_cast (min_le_left (1 : ℝ≥0) (L+1)⁻¹)
  have hLε : (L : ℝ)*(ε : ℝ) ≤ 1 := by
    have hh : (ε : ℝ) ≤ ((L : ℝ)+1)⁻¹ := by exact_mod_cast (min_le_right (1 : ℝ≥0) (L+1)⁻¹)
    have hp : 0 < (L : ℝ)+1 := by positivity
    have hh' : (ε : ℝ)*((L : ℝ)+1) ≤ 1 := (le_div_iff₀ hp).mp (by simpa only [one_div] using hh)
    nlinarith [L.coe_nonneg]
  let t₀ : Icc (-(ε : ℝ)) (ε : ℝ) := ⟨0, by constructor <;> linarith⟩
  have hPic : IsPicardLindelof (fun t y => b (y+N t)) t₀ z 1 0 L K := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simpa only [dist_add_right] using hb.dist_le_mul (x+N t) (y+N t)
    · intro y hy
      exact hb.continuous.comp (continuous_const.add hN) |>.continuousOn
    · intro t ht y hy
      have hNt := hC t (show t ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      have hyz : ‖y-z‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm, NNReal.coe_one] using hy
      have hsum : ‖y+N t-z‖ ≤ 1+C := by
        calc
          _ = ‖(y-z)+N t‖ := by congr 1; abel
          _ ≤ ‖y-z‖+‖N t‖ := norm_add_le _ _
          _ ≤ 1+C := add_le_add hyz hNt
      have hdist := hb.dist_le_mul (y+N t) z
      have hnorm : ‖b (y+N t)‖ ≤ ‖b z‖+‖b (y+N t)-b z‖ :=
        norm_le_insert' _ _
      change ‖b (y+N t)‖ ≤ ‖b z‖+(K : ℝ)*(1+C)
      rw [dist_eq_norm, dist_eq_norm] at hdist
      nlinarith [mul_le_mul_of_nonneg_left hsum K.coe_nonneg]
    · simpa [t₀] using hLε
  obtain ⟨Y, hY0, hY⟩ := hPic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨Y, hY0, ε, hε, ?_⟩
  intro t ht
  exact (hY t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem ginibreDrivenPath_continuous_noise_local_correction (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) :
    ∃ Y : ℝ → Configuration n, Y 0 = z ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt Y (ginibreLangevinDrift n α (Y t+N t)) t := by
  obtain ⟨K, s, hs, hb⟩ := ginibreLangevinDrift_local_lipschitz n α z hz
  obtain ⟨g, hg, heq⟩ := hb.extend_finite_dimension
  obtain ⟨Y, hY0, ε, hε, hY⟩ :=
    drivenContinuousNoise_lipschitz_local_correction g _ hg N hN z
  have hYcont : ContinuousAt Y 0 := (hY 0 (by constructor <;> linarith)).continuousAt
  have hXcont : ContinuousAt (fun t => Y t+N t) 0 := hYcont.add hN.continuousAt
  have hX0 : Y 0+N 0 = z := by rw [hY0, hN0, add_zero]
  have hev : ∀ᶠ t in nhds 0, Y t+N t ∈ s := hXcont.eventually (by
    dsimp only
    rw [hX0]
    change s ∈ nhds z
    exact hs)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨Y, hY0, min ε δ, lt_min hε hδ, ?_⟩
  intro t ht
  have hte : t ∈ Ioo (-ε) ε := ⟨by linarith [min_le_left ε δ, ht.1], ht.2.trans_le (min_le_left ε
                                     δ)⟩
  have hts : Y t+N t ∈ s := hδs (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [min_le_right ε δ, ht.1], ht.2.trans_le (min_le_right ε δ)⟩)
  rw [heq hts]
  exact hY t hte

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathUniformLocalExistence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathContinuousNoisePicard

/-! A uniform actual Volterra existence interval for bounded continuous noises. -/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem drivenContinuousNoise_lipschitz_uniform_local {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (z : E) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ε > (0 : ℝ), ∀ N : ℝ → E, Continuous N → N 0 = 0 →
      (∀ t ∈ Icc (-1 : ℝ) 1, ‖N t‖ ≤ M) →
      ∃ X : ℝ → E, ContinuousOn X (Icc 0 ε) ∧ X 0 = z ∧
        ∀ t ∈ Icc 0 ε, X t = z+N t+∫ s in (0 : ℝ)..t, b (X s) := by
  let L : ℝ≥0 := ⟨‖b z‖+(K : ℝ)*(1+M), by positivity⟩
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
  refine ⟨ε, hε, ?_⟩
  intro N hN hN0 hC
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
      have hyz : ‖y-z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_eq_norm, NNReal.coe_one]
                                   using hy
      have hsum : ‖y+N t-z‖ ≤ 1+M := by
        calc
          _ = ‖(y-z)+N t‖ := by congr 1; abel
          _ ≤ ‖y-z‖+‖N t‖ := norm_add_le _ _
          _ ≤ 1+M := add_le_add hyz hNt
      have hdist := hb.dist_le_mul (y+N t) z
      have hnorm : ‖b (y+N t)‖ ≤ ‖b z‖+‖b (y+N t)-b z‖ :=
        norm_le_insert' _ _
      change ‖b (y+N t)‖ ≤ ‖b z‖+(K : ℝ)*(1+M)
      rw [dist_eq_norm, dist_eq_norm] at hdist
      nlinarith [mul_le_mul_of_nonneg_left hsum K.coe_nonneg]
    · simpa [t₀] using hLε
  obtain ⟨Y, hY0, hY⟩ := hPic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hYc : ContinuousOn Y (Icc 0 (ε : ℝ)) := by
    intro t ht
    exact ((hY t ⟨by linarith [ht.1], ht.2⟩).continuousWithinAt).mono
      (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
  let X := fun t => Y t+N t
  have hXc : ContinuousOn X (Icc 0 (ε : ℝ)) := hYc.add hN.continuousOn
  refine ⟨X, hXc, ?_, ?_⟩
  · dsimp [X]; rw [hY0, hN0, add_zero]
  · intro t ht
    have hbc : ContinuousOn (fun s => b (X s)) (Icc 0 t) :=
      (hb.continuous.comp_continuousOn hXc).mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hYc.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩))
      (fun s hs => (hY s ⟨by linarith [hs.1], hs.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [hs.1]) (hs.2.trans_le ht.2)) |>.hasDerivWithinAt)
      (hbc.intervalIntegrable_of_Icc ht.1)
    dsimp [X]
    rw [hFTC, hY0]
    abel

end
end GinibrePoincare

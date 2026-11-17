/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/SobolevValueTruncation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.SobolevTruncation

/-! # Concrete smooth truncation of scalar values

These maps are bounded, fix zero, and approach the identity together with their
ordinary derivatives. Their derivative bound is uniform over truncation scales.
-/


@[expose] public section


open Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

def sobolevValueTruncation (m : ℕ) (x : ℝ) : ℝ := sobolevCutoff m x * x

theorem sobolevValueTruncation_smooth (m : ℕ) : ContDiff ℝ ∞ (sobolevValueTruncation m) :=
  (sobolevCutoff_smooth m).mul contDiff_id

theorem sobolevValueTruncation_zero (m : ℕ) : sobolevValueTruncation m 0 = 0 := by
  simp [sobolevValueTruncation]

theorem sobolevValueTruncation_norm_le (m : ℕ) (x : ℝ) :
    ‖sobolevValueTruncation m x‖ ≤ ‖x‖ := by
  rw [sobolevValueTruncation, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (sobolevCutoff_mem_unit m x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (sobolevCutoff_mem_unit m x).2

theorem sobolevValueTruncation_deriv (m : ℕ) (x : ℝ) :
    deriv (sobolevValueTruncation m) x = deriv (sobolevCutoff m) x * x + sobolevCutoff m x := by
  change deriv (sobolevCutoff m * id) x = _
  simpa only [id_eq, mul_one] using
    (((sobolevCutoff_smooth m).differentiable (by simp) x).hasDerivAt.mul
      (hasDerivAt_id x)).deriv

theorem sobolevValueTruncation_bounded (m : ℕ) (x : ℝ) :
    ‖sobolevValueTruncation m x‖ ≤ 2 * ((m : ℝ) + 1) := by
  by_cases hx : |x / ((m : ℝ) + 1)| ≤ 2
  · have hr : |x| ≤ 2 * ((m : ℝ) + 1) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < (m : ℝ) + 1)] at hx
      exact (div_le_iff₀ (by positivity)).mp hx
    exact (sobolevValueTruncation_norm_le m x).trans (by simpa using hr)
  · have hb : x / ((m : ℝ) + 1) ∉ tsupport (sobolevCutoffBump : ℝ → ℝ) := by
      rw [sobolevCutoffBump.tsupport_eq]
      simpa only [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump, sub_zero] using hx
    simp only [sobolevValueTruncation, sobolevCutoff,
      image_eq_zero_of_notMem_tsupport hb, zero_mul, norm_zero]
    positivity

/-- Uniform actual derivative bound; it is derived from the fixed bump. -/
theorem sobolevValueTruncation_deriv_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ m x,
    ‖deriv (sobolevValueTruncation m) x‖ ≤ B := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  refine ⟨2 * M + 1, by positivity, ?_⟩
  intro m x
  have hc : ‖sobolevCutoff m x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sobolevCutoff_mem_unit m x).1]
    exact (sobolevCutoff_mem_unit m x).2
  have hd : ‖deriv (sobolevCutoff m) x * x‖ ≤ 2 * M := by
    by_cases hx : |x / ((m : ℝ) + 1)| ≤ 2
    · have hr : |x| ≤ 2 * ((m : ℝ) + 1) := by
        rw [abs_div, abs_of_pos (by positivity : 0 < (m : ℝ) + 1)] at hx
        exact (div_le_iff₀ (by positivity)).mp hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc
        |deriv (sobolevCutoff m) x| * |x| ≤
            (M / ((m : ℝ) + 1)) * (2 * ((m : ℝ) + 1)) :=
          mul_le_mul (hM m x) hr (abs_nonneg _) (by positivity)
        _ = 2 * M := by field_simp
    · have hb : x / ((m : ℝ) + 1) ∉ tsupport (sobolevCutoffBump : ℝ → ℝ) := by
        rw [sobolevCutoffBump.tsupport_eq]
        simpa only [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump, sub_zero] using hx
      rw [sobolevCutoff_deriv, deriv_of_notMem_tsupport hb]
      simp only [zero_div, zero_mul, norm_zero]
      positivity
  rw [sobolevValueTruncation_deriv]
  exact (norm_add_le _ _).trans (add_le_add hd hc)

/-- Both the scalar truncation and its actual derivative converge to the identity. -/
theorem sobolevValueTruncation_tendsto (x : ℝ) :
    Tendsto (fun m => sobolevValueTruncation m x) atTop (𝓝 x) ∧
      Tendsto (fun m => deriv (sobolevValueTruncation m) x) atTop (𝓝 1) := by
  constructor
  · simpa only [sobolevValueTruncation, one_mul] using (sobolevCutoff_tendsto x).1.mul_const x
  · simp_rw [sobolevValueTruncation_deriv]
    simpa using ((sobolevCutoff_tendsto x).2.mul_const x).add (sobolevCutoff_tendsto x).1
end
end GinibrePoincare

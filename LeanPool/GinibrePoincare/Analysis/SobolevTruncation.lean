/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/SobolevTruncation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EntropyL2Closure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Sobolev Truncation
-/


@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- A fixed smooth cutoff, equal to one on the unit interval. -/
def sobolevCutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- Spatial truncations expanding to all of the real line. -/
def sobolevCutoff (n : ℕ) (x : ℝ) : ℝ := sobolevCutoffBump (x / ((n : ℝ) + 1))

theorem sobolevCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (sobolevCutoff n) := by
  unfold sobolevCutoff
  exact sobolevCutoffBump.contDiff.comp (by fun_prop)

theorem sobolevCutoff_compact (n : ℕ) : HasCompactSupport (sobolevCutoff n) := by
  have hn : ((n : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have h := sobolevCutoffBump.hasCompactSupport.comp_isClosedEmbedding
    (Homeomorph.mulRight₀ (((n : ℝ) + 1)⁻¹) hn).isClosedEmbedding
  unfold sobolevCutoff
  simpa [div_eq_mul_inv, Function.comp_def] using h

theorem sobolevCutoff_mem_unit (n : ℕ) (x : ℝ) :
    0 ≤ sobolevCutoff n x ∧ sobolevCutoff n x ≤ 1 :=
  ⟨sobolevCutoffBump.nonneg, sobolevCutoffBump.le_one⟩

theorem sobolevCutoff_deriv (n : ℕ) (x : ℝ) :
    deriv (sobolevCutoff n) x = deriv (sobolevCutoffBump : ℝ → ℝ)
      (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
  have h := ((sobolevCutoffBump.contDiff (n := 1)).differentiable (by norm_num) (x / ((n : ℝ) +
    1))).hasDerivAt
    |>.comp x ((hasDerivAt_id x).div_const ((n : ℝ) + 1))
  unfold sobolevCutoff
  simpa [Function.comp_def, div_eq_mul_inv] using h.deriv

/-- Uniform derivative control of the expanding cutoffs. -/
theorem sobolevCutoff_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n x,
    |deriv (sobolevCutoff n) x| ≤ M / ((n : ℝ) + 1) := by
  obtain ⟨M, hM⟩ := ((sobolevCutoffBump.contDiff (n := 1)).continuous_deriv
    (by norm_num)).bounded_above_of_compact_support sobolevCutoffBump.hasCompactSupport.deriv
  refine ⟨M, (norm_nonneg _).trans (hM 0), ?_⟩
  intro n x
  rw [sobolevCutoff_deriv, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hM _) (by positivity)

/-- Both the cutoff and its derivative have the required pointwise limits. -/
theorem sobolevCutoff_tendsto (x : ℝ) :
    Tendsto (fun n => sobolevCutoff n x) atTop (𝓝 1) ∧
      Tendsto (fun n => deriv (sobolevCutoff n) x) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop)
  have hx : Tendsto (fun n : ℕ => x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hi.const_mul x
  constructor
  · have h := (sobolevCutoffBump.contDiff (n := 1)).continuous.continuousAt.tendsto.comp hx
    have hz : sobolevCutoffBump (0 : ℝ) = 1 :=
      sobolevCutoffBump.one_of_mem_closedBall (by simp [sobolevCutoffBump])
    simpa [sobolevCutoff, hz, Function.comp_def] using h
  · obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => by simpa using hM n x)
    simpa [div_eq_mul_inv] using hi.const_mul M

/-- Multiplication by the expanding cutoff converges in both value and derivative. -/
theorem sobolevCutoff_mul_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x : ℝ) :
    Tendsto (fun n => sobolevCutoff n x * f x) atTop (𝓝 (f x)) ∧
      Tendsto (fun n => deriv (fun y => sobolevCutoff n y * f y) x) atTop (𝓝 (deriv f x)) := by
  have hder (n : ℕ) : deriv (fun y => sobolevCutoff n y * f y) x =
      deriv (sobolevCutoff n) x * f x + sobolevCutoff n x * deriv f x :=
    (((sobolevCutoff_smooth n).differentiable (by simp) x).hasDerivAt.mul
      (hf.differentiable (by norm_num) x).hasDerivAt).deriv
  constructor
  · simpa using (sobolevCutoff_tendsto x).1.mul_const (f x)
  · simp_rw [hder]
    simpa using ((sobolevCutoff_tendsto x).2.mul_const (f x)).add
      ((sobolevCutoff_tendsto x).1.mul_const (deriv f x))

/-- Spatial truncation converges in the weighted H¹ seminorm and L² norm.
Only the actual square integrability of the value and derivative is required. -/
theorem sobolevCutoff_L2_errors_tendsto (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hv : MemLp f 2 μ) (hd : MemLp (deriv f) 2 μ) :
    Tendsto (fun n => ∫ x, (sobolevCutoff n x * f x - f x) ^ 2 ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x,
      (deriv (fun y => sobolevCutoff n y * f y) x - deriv f x) ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  have hg (n : ℕ) : ContDiff ℝ 1 (fun x => sobolevCutoff n x * f x) :=
    ((sobolevCutoff_smooth n).of_le (by simp)).mul hf
  have hder (n : ℕ) (x : ℝ) : deriv (fun y => sobolevCutoff n y * f y) x =
      deriv (sobolevCutoff n) x * f x + sobolevCutoff n x * deriv f x :=
    (((sobolevCutoff_smooth n).differentiable (by simp) x).hasDerivAt.mul
      (hf.differentiable (by norm_num) x).hasDerivAt).deriv
  have hb (n : ℕ) (x : ℝ) : |deriv (sobolevCutoff n) x| ≤ M := by
    refine (hM n x).trans ?_
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hc (n : ℕ) (x : ℝ) : (sobolevCutoff n x - 1) ^ 2 ≤ 1 := by
    obtain ⟨h0, h1⟩ := sobolevCutoff_mem_unit n x
    nlinarith
  constructor
  · have h := tendsto_integral_of_dominated_convergence (fun x => (f x) ^ 2)
      (fun n => ((hg n).continuous.sub hf.continuous |>.pow 2).aestronglyMeasurable)
      hv.integrable_sq
      (fun n => ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have he : (sobolevCutoff n x * f x - f x) ^ 2 =
            (sobolevCutoff n x - 1) ^ 2 * (f x) ^ 2 := by ring
        change (sobolevCutoff n x * f x - f x) ^ 2 ≤ (f x) ^ 2
        rw [he]
        simpa using mul_le_mul_of_nonneg_right (hc n x) (sq_nonneg (f x))))
      (ae_of_all _ (fun x => by
        simpa using (((sobolevCutoff_mul_tendsto f hf x).1.sub_const (f x)).pow 2)))
    simpa using h
  · have h := tendsto_integral_of_dominated_convergence
      (fun x => 2 * M ^ 2 * (f x) ^ 2 + 2 * (deriv f x) ^ 2)
      (fun n => (((hg n).continuous_deriv le_rfl).sub (hf.continuous_deriv le_rfl)
        |>.pow 2).aestronglyMeasurable)
      ((hv.integrable_sq.const_mul (2 * M ^ 2)).add (hd.integrable_sq.const_mul 2))
      (fun n => ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (deriv (fun y => sobolevCutoff n y * f y) x - deriv f x) ^ 2 ≤ _
        rw [hder]
        have hbs : (deriv (sobolevCutoff n) x) ^ 2 ≤ M ^ 2 := by
          have hbb := hb n x
          nlinarith [sq_abs (deriv (sobolevCutoff n) x), abs_nonneg (deriv (sobolevCutoff n) x)]
        have ha := mul_le_mul_of_nonneg_right hbs (sq_nonneg (f x))
        have hb' := mul_le_mul_of_nonneg_right (hc n x) (sq_nonneg (deriv f x))
        nlinarith [sq_nonneg (deriv (sobolevCutoff n) x * f x -
          (sobolevCutoff n x - 1) * deriv f x)]))
      (ae_of_all _ (fun x => by
        simpa using (((sobolevCutoff_mul_tendsto f hf x).2.sub_const (deriv f x)).pow 2)))
    simpa using h

end
end GinibrePoincare

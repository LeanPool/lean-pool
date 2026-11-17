/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/L2BoundedCoefficientConvergence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevTruncation
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Strong L² limits for bounded scalar coefficients -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] (μ : Measure α)

/-- Multiplication by a genuinely bounded measurable coefficient preserves L². -/
theorem L2_boundedCoefficient_memLp (a : α → ℝ)
    (ha : AEStronglyMeasurable a μ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, ‖a x‖ ≤ B) (g : Lp V 2 μ) : MemLp (fun x => a x • g x) 2 μ := by
  apply ((Lp.memLp g).const_smul B).of_le (ha.smul (Lp.aestronglyMeasurable g))
  apply ae_of_all
  intro x
  change ‖a x • g x‖ ≤ ‖B • g x‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs B, abs_of_nonneg hB]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- Uniform coefficient control gives a bound for the actual L² multiplier. -/
theorem L2_boundedCoefficient_norm_le (a : α → ℝ)
    (ha : AEStronglyMeasurable a μ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, ‖a x‖ ≤ B) (g : Lp V 2 μ) :
    ‖(L2_boundedCoefficient_memLp μ a ha B hB hb g).toLp (fun x => a x • g x)‖ ≤ B * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(L2_boundedCoefficient_memLp μ a ha B hB hb g).coeFn_toLp] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- Almost-everywhere converging, uniformly bounded coefficients converge as
multipliers on each fixed actual L² vector. -/
theorem L2_boundedCoefficient_tendsto_fixed
    (a : ℕ → α → ℝ) (c : α → ℝ)
    (ha : ∀ j, AEStronglyMeasurable (a j) μ) (hc : AEStronglyMeasurable c μ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ j x, ‖a j x‖ ≤ B) (hcb : ∀ x, ‖c x‖ ≤ B)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun j => a j x) atTop (𝓝 (c x))) (g : Lp V 2 μ) :
    Tendsto (fun j => (L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) g).toLp
      (fun x => a j x • g x)) atTop
      (𝓝 ((L2_boundedCoefficient_memLp μ c hc B hB hcb g).toLp (fun x => c x • g x))) := by
  have hi := ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp
    g)).const_mul ((2 * B) ^ 2)
  have he := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun x => (2 * B) ^ 2 * ‖g x‖ ^ 2)
    (fun j => ((((ha j).sub hc).smul (Lp.aestronglyMeasurable g)).norm.pow 2)) hi
    (fun j => ae_of_all _ (fun x => by
      change ‖‖(a j x - c x) • g x‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, mul_pow]
      have hb' : ‖a j x - c x‖ ≤ 2 * B :=
        (norm_sub_le _ _).trans (by linarith [hb j x, hcb x])
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith [norm_nonneg (a j x - c x)]))
    (ht.mono (fun x hx => by simpa using ((hx.sub_const (c x)).smul_const (g x)).norm.pow 2))
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hd (j : ℕ) : dist ((L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) g).toLp
      (fun x => a j x • g x)) ((L2_boundedCoefficient_memLp μ c hc B hB hcb g).toLp
      (fun x => c x • g x)) = Real.sqrt (∫ x, ‖(a j x - c x) • g x‖ ^ 2 ∂μ) := by
    rw [L2_dist_eq_sqrt_integral_norm_error]
    congr 1
    apply integral_congr_ae
    filter_upwards [(L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) g).coeFn_toLp,
      (L2_boundedCoefficient_memLp μ c hc B hB hcb g).coeFn_toLp] with x hx hy
    rw [hx, hy, sub_smul]
  simp_rw [hd]
  simpa using he.sqrt

/-- The same multiplier convergence holds when the L² vector also varies. -/
theorem L2_boundedCoefficient_tendsto
    (a : ℕ → α → ℝ) (c : α → ℝ)
    (ha : ∀ j, AEStronglyMeasurable (a j) μ) (hc : AEStronglyMeasurable c μ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ j x, ‖a j x‖ ≤ B) (hcb : ∀ x, ‖c x‖ ≤ B)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun j => a j x) atTop (𝓝 (c x)))
    (v : ℕ → Lp V 2 μ) (g : Lp V 2 μ) (hv : Tendsto v atTop (𝓝 g)) :
    Tendsto (fun j => (L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) (v j)).toLp
      (fun x => a j x • v j x)) atTop
      (𝓝 ((L2_boundedCoefficient_memLp μ c hc B hB hcb g).toLp (fun x => c x • g x))) := by
  let d j := (L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) (v j - g)).toLp
    (fun x => a j x • (v j - g) x)
  have hd : Tendsto d atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun j =>
      L2_boundedCoefficient_norm_le μ (a j) (ha j) B hB (hb j) (v j - g))
    simpa using (hv.sub_const g).norm.const_mul B
  have he (j : ℕ) :
      (L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) (v j)).toLp
        (fun x => a j x • v j x) = d j +
      (L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) g).toLp (fun x => a j x • g x) := by
    apply Lp.ext
    filter_upwards [(L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) (v j)).coeFn_toLp,
      Lp.coeFn_add (d j) ((L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) g).toLp (fun x
        => a j x • g x)),
      (L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) (v j - g)).coeFn_toLp,
      (L2_boundedCoefficient_memLp μ (a j) (ha j) B hB (hb j) g).coeFn_toLp,
      Lp.coeFn_sub (v j) g] with x h1 h2 h3 h4 h5
    rw [h1, h2]
    change a j x • v j x = d j x + _
    change d j x = _ at h3
    rw [h3, h4, h5]
    simp [smul_sub]
  simp_rw [he]
  simpa using hd.add (L2_boundedCoefficient_tendsto_fixed μ a c ha hc B hB hb hcb ht g)
end
end GinibrePoincare

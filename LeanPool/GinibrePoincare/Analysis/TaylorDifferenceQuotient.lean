/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/TaylorDifferenceQuotient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BernoulliGaussianCLT
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor difference quotient

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `centeredDifference_integral_square_error`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The centered difference quotient at a positive mesh size. -/
def centeredDifference (f : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (f (x + h) - f (x - h)) / (2 * h)

/-- Taylor's formula with a global second-derivative bound. -/
theorem taylor_first_order_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (M : ℝ) (hM : ∀ x, |iteratedDeriv 2 f x| ≤ M) (x h : ℝ) :
    |f (x + h) - f x - h * deriv f x| ≤ M * h ^ 2 / 2 := by
  by_cases hz : h = 0
  · simp [hz]
  have hne : x ≠ x + h := by intro he; apply hz; linarith
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hne hf.contDiffOn
  have ht : taylorWithinEval f 1 (Set.uIcc x (x + h)) x (x + h) =
      f x + h * deriv f x := by
    rw [show 1 = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.of_le (by norm_num)).contDiffAt (Set.left_mem_uIcc)]
    simp
  rw [ht] at he
  norm_num at he
  have he' : f (x + h) - f x - h * deriv f x = iteratedDeriv 2 f y * h ^ 2 / 2 := by
    convert he using 1; ring
  rw [he', abs_div, abs_mul, abs_of_nonneg (sq_nonneg h)]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM y) (sq_nonneg h)) (by norm_num)

/-- Uniform Taylor control of the centered quotient, including the exact factor `1/2`. -/
theorem centeredDifference_error_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (M : ℝ) (hM : ∀ x, |iteratedDeriv 2 f x| ≤ M) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |centeredDifference f h x - deriv f x| ≤ M * h / 2 := by
  have hp := taylor_first_order_bound f hf M hM x h
  have hm := taylor_first_order_bound f hf M hM x (-h)
  have he : centeredDifference f h x - deriv f x =
      ((f (x + h) - f x - h * deriv f x) -
       (f (x - h) - f x + h * deriv f x)) / (2 * h) := by
    unfold centeredDifference
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2 * h)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * h)).mpr
  have hs := abs_sub (f (x + h) - f x - h * deriv f x)
    (f (x - h) - f x + h * deriv f x)
  simp only [← sub_eq_add_neg, neg_mul, sub_neg_eq_add, neg_sq] at hm
  nlinarith

/-- Squaring the quotient preserves the uniform Taylor approximation. -/
theorem centeredDifference_square_error_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (L M : ℝ) (hL : ∀ x, |deriv f x| ≤ L)
    (hM : ∀ x, |iteratedDeriv 2 f x| ≤ M) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    |(centeredDifference f h x) ^ 2 - (deriv f x) ^ 2| ≤
      (M * h / 2) * (2 * L + M * h / 2) := by
  have he := centeredDifference_error_bound f hf M hM hh x
  have hq : |centeredDifference f h x| ≤ L + M * h / 2 := by
    have ht := abs_add_le (centeredDifference f h x - deriv f x) (deriv f x)
    rw [sub_add_cancel] at ht
    linarith [hL x]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hsum : |centeredDifference f h x + deriv f x| ≤ 2 * L + M * h / 2 :=
    (abs_add_le _ _).trans (by linarith [hL x])
  rw [show (centeredDifference f h x) ^ 2 - (deriv f x) ^ 2 =
    (centeredDifference f h x - deriv f x) * (centeredDifference f h x + deriv f x) by ring,
    abs_mul]
  exact mul_le_mul he hsum (abs_nonneg _) (by positivity)

/-- Taylor's squared-error estimate integrates uniformly over any probability law. -/
theorem centeredDifference_integral_square_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (L M : ℝ)
    (hL : ∀ x, |deriv f x| ≤ L) (hM : ∀ x, |iteratedDeriv 2 f x| ≤ M)
    {h : ℝ} (hh : 0 < h) :
    |(∫ ω, (centeredDifference f h (X ω)) ^ 2 ∂μ) -
      (∫ ω, (deriv f (X ω)) ^ 2 ∂μ)| ≤
      (M * h / 2) * (2 * L + M * h / 2) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hg : Integrable (fun ω => (deriv f (X ω)) ^ 2) μ := by
    apply Integrable.of_bound
      (((hf.continuous_deriv (by norm_num)).pow 2).measurable.comp hX).aestronglyMeasurable (L ^ 2)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (deriv f (X ω)) ^ 2 ≤ L ^ 2
    have hb := hL (X ω)
    nlinarith [sq_abs (deriv f (X ω)), abs_nonneg (deriv f (X ω))]
  have hqcont : Continuous (centeredDifference f h) := by
    unfold centeredDifference
    fun_prop
  have hq : Integrable (fun ω => (centeredDifference f h (X ω)) ^ 2) μ := by
    apply Integrable.of_bound ((hqcont.pow 2).measurable.comp hX).aestronglyMeasurable
      ((L + M * h / 2) ^ 2)
    apply ae_of_all
    intro ω
    have he := centeredDifference_error_bound f hf M hM hh (X ω)
    have hb := abs_add_le (centeredDifference f h (X ω) - deriv f (X ω)) (deriv f (X ω))
    rw [sub_add_cancel] at hb
    have hqb : |centeredDifference f h (X ω)| ≤ L + M * h / 2 := by linarith [hL (X ω)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (centeredDifference f h (X ω)) ^ 2 ≤ (L + M * h / 2) ^ 2
    nlinarith [sq_abs (centeredDifference f h (X ω)), abs_nonneg (centeredDifference f h (X ω)),
        mul_nonneg hM0 hh.le]
  rw [← integral_sub hq hg, ← Real.norm_eq_abs]
  have he := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => (centeredDifference f h (X ω)) ^ 2 - (deriv f (X ω)) ^ 2)
    (ae_of_all _ (fun ω => by
      simpa only [Real.norm_eq_abs] using
        centeredDifference_square_error_bound f hf L M hL hM hh (X ω)))
  simpa using he

end
end GinibrePoincare

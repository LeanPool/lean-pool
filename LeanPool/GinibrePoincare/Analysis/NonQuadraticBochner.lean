/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticBochner.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPotential
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Concrete one-dimensional weighted Bochner identity
This is the genuine integration-by-parts curvature estimate for a C²
confinement, with all terms defined by Lebesgue integrals. It asserts no
logarithmic Sobolev estimate without the required entropy argument.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Density of a one-dimensional confinement before normalization. -/
def scalarConfinementWeight (W : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (-W x)

/-- Concrete weighted diffusion generator f'' - W'f'. -/
def scalarConfinementGenerator (W f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x - deriv W x * deriv f x

private theorem compact_deriv_integral_zero (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) : (∫ x, deriv F x) = 0 := by
  have hFc : Continuous F := hF.continuous
  have hdFc : Continuous (deriv F) :=
    (show ContDiff ℝ (0 + 1) F from hF).deriv'.continuous
  have hi : Integrable (deriv F) := hdFc.integrable_of_hasCompactSupport hc.deriv
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := F) (g := fun _ : ℝ => (1 : ℝ)) (v := (1 : ℝ))
    (by simpa only [fderiv_apply_one_eq_deriv, mul_one] using hi)
    (by simp) (by simpa using hFc.integrable_of_hasCompactSupport hc)
    (fun x _ => (hF.differentiable (by norm_num)) x)
    (fun x _ => differentiableAt_const 1)
  simp only [fderiv_apply_one_eq_deriv, deriv_const, mul_zero, integral_zero, mul_one] at he
  linarith

/-- Exact integrated one-dimensional Γ₂ identity for compact smooth tests. -/
theorem scalarConfinement_bochner_identity (W f : ℝ → ℝ)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    (∫ x, scalarConfinementGenerator W f x ^ 2 * scalarConfinementWeight W x) =
      (∫ x, deriv (deriv f) x ^ 2 * scalarConfinementWeight W x) +
      ∫ x, deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x := by
  have hW1 : ContDiff ℝ 1 (deriv W) := (show ContDiff ℝ (1 + 1) W from hW).deriv'
  have hf1 : ContDiff ℝ 1 (deriv f) := (show ContDiff ℝ (1 + 1) f from hf).deriv'
  have hW2c : Continuous (deriv (deriv W)) :=
    (show ContDiff ℝ (0 + 1) (deriv W) from hW1).deriv'.continuous
  have hf2c : Continuous (deriv (deriv f)) :=
    (show ContDiff ℝ (0 + 1) (deriv f) from hf1).deriv'.continuous
  have hb : ContDiff ℝ 1 (scalarConfinementWeight W) :=
    Real.contDiff_exp.comp ((hW.of_le (by norm_num)).neg)
  let F := fun x => deriv W x * deriv f x ^ 2 * scalarConfinementWeight W x
  have hF : ContDiff ℝ 1 F := (hW1.mul (hf1.pow 2)).mul hb
  have hFc : HasCompactSupport F := by
    apply hc.deriv.mono
    intro x hx hzero
    apply hx
    simp [F, hzero]
  have hdF (x : ℝ) : deriv F x =
      deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x +
      2 * deriv W x * deriv f x * deriv (deriv f) x * scalarConfinementWeight W x -
      deriv W x ^ 2 * deriv f x ^ 2 * scalarConfinementWeight W x := by
    have hdW := ((hW.differentiable (by norm_num)) x).hasDerivAt
    have hdW1 := ((hW1.differentiable (by norm_num)) x).hasDerivAt
    have hdf1 := ((hf1.differentiable (by norm_num)) x).hasDerivAt
    have hdb := hdW.neg.exp
    have h := (hdW1.mul (hdf1.pow 2)).mul hdb
    change HasDerivAt F _ x at h
    rw [h.deriv]
    dsimp [scalarConfinementWeight]
    ring
  have hi1 : Integrable (fun x => deriv (deriv f) x ^ 2 * scalarConfinementWeight W x) := by
    apply (hf2c.pow 2 |>.mul hb.continuous).integrable_of_hasCompactSupport
    apply hc.deriv.deriv.mono
    intro x hx hzero
    apply hx
    simp [hzero]
  have hi2 : Integrable F := hF.continuous.integrable_of_hasCompactSupport hFc
  have hid : Integrable (deriv F) :=
    ((show ContDiff ℝ (0 + 1) F from hF).deriv'.continuous).integrable_of_hasCompactSupport
        hFc.deriv
  have hpoint (x : ℝ) :
      scalarConfinementGenerator W f x ^ 2 * scalarConfinementWeight W x =
        (deriv (deriv f) x ^ 2 * scalarConfinementWeight W x +
          deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x) - deriv F x := by
    rw [hdF]
    unfold scalarConfinementGenerator
    ring
  have hi2' : Integrable (fun x => deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x)
      := by
    apply (hW2c.mul (hf1.continuous.pow 2) |>.mul hb.continuous).integrable_of_hasCompactSupport
    apply hc.deriv.mono
    intro x hx hzero
    apply hx
    simp [hzero]
  simp_rw [hpoint]
  rw [integral_sub
    (f := fun x => deriv (deriv f) x ^ 2 * scalarConfinementWeight W x +
      deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x)
    (g := deriv F) (hi1.add hi2') hid,
    integral_add
      (f := fun x => deriv (deriv f) x ^ 2 * scalarConfinementWeight W x)
      (g := fun x => deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x) hi1 hi2',
    compact_deriv_integral_zero F hF hFc, sub_zero]

/-- Genuine weighted-generator coercivity from the pointwise confinement
curvature. The curvature is needed only on the test function's support. -/
theorem scalarConfinement_generator_coercivity (W f : ℝ → ℝ) (κ : ℝ)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hcurv : ∀ x ∈ tsupport f, κ ≤ deriv (deriv W) x) :
    κ * (∫ x, deriv f x ^ 2 * scalarConfinementWeight W x) ≤
      ∫ x, scalarConfinementGenerator W f x ^ 2 * scalarConfinementWeight W x := by
  have hf1 : ContDiff ℝ 1 (deriv f) := (show ContDiff ℝ (1 + 1) f from hf).deriv'
  have hW1 : ContDiff ℝ 1 (deriv W) := (show ContDiff ℝ (1 + 1) W from hW).deriv'
  have hW2c : Continuous (deriv (deriv W)) :=
    (show ContDiff ℝ (0 + 1) (deriv W) from hW1).deriv'.continuous
  have hb : Continuous (scalarConfinementWeight W) := Real.continuous_exp.comp hW.continuous.neg
  have hs : HasCompactSupport (fun x => deriv f x ^ 2 * scalarConfinementWeight W x) := by
    apply hc.deriv.mono
    intro x hx hzero
    apply hx
    simp [hzero]
  have hbase : Integrable (fun x => deriv f x ^ 2 * scalarConfinementWeight W x) :=
    (hf1.continuous.pow 2 |>.mul hb).integrable_of_hasCompactSupport hs
  have hs' : HasCompactSupport (fun x => deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight
      W x) := by
    apply hc.deriv.mono
    intro x hx hzero
    apply hx
    simp [hzero]
  have hcurvi : Integrable (fun x => deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W
      x) :=
    (hW2c.mul (hf1.continuous.pow 2) |>.mul hb).integrable_of_hasCompactSupport hs'
  have hineq : κ * (∫ x, deriv f x ^ 2 * scalarConfinementWeight W x) ≤
      ∫ x, deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x := by
    rw [← integral_const_mul]
    apply integral_mono (hbase.const_mul κ) hcurvi
    intro x
    by_cases hx : x ∈ tsupport (deriv f)
    · have hκ := hcurv x (tsupport_deriv_subset hx)
      have hp : 0 ≤ deriv f x ^ 2 * scalarConfinementWeight W x :=
        mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hκ hp
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [scalarConfinement_bochner_identity W f hW hf hc]
  exact hineq.trans (le_add_of_nonneg_left (integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))

end
end GinibrePoincare

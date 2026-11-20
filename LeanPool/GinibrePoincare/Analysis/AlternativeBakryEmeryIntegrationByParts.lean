/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryIntegrationByParts.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBochner

/-! # Weighted integration by parts for the confinement form

This identifies the compact-core weighted derivative adjoint internally.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Exact weighted derivative adjoint under `exp(-W) dx`. -/
theorem bakryEmery_scalar_derivative_adjoint (W f θ : ℝ → ℝ)
    (hW : ContDiff ℝ 1 W) (hf : ContDiff ℝ 1 f) (hθ : ContDiff ℝ 1 θ)
    (hfc : HasCompactSupport f) (hθc : HasCompactSupport θ) :
    (∫ x, deriv f x * θ x * scalarConfinementWeight W x) =
      ∫ x, f x * (deriv W x * θ x - deriv θ x) * scalarConfinementWeight W x := by
  let w := scalarConfinementWeight W
  have hw : ContDiff ℝ 1 w := Real.contDiff_exp.comp hW.neg
  have hg : ContDiff ℝ 1 (fun x => θ x * w x) := hθ.mul hw
  have hgc : HasCompactSupport (fun x => θ x * w x) := hθc.mul_right
  have hdθ : Continuous (deriv θ) :=
    (show ContDiff ℝ (0 + 1) θ from hθ).deriv'.continuous
  have hdf : Continuous (deriv f) :=
    (show ContDiff ℝ (0 + 1) f from hf).deriv'.continuous
  have hdW : Continuous (deriv W) :=
    (show ContDiff ℝ (0 + 1) W from hW).deriv'.continuous
  have hdg : Continuous (deriv (fun x => θ x * w x)) :=
    (show ContDiff ℝ (0 + 1) (fun x => θ x * w x) from hg).deriv'.continuous
  have hi₁ : Integrable (fun x => f x * deriv (fun y => θ y * w y) x) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport hfc.mul_right
  have hi₂ : Integrable (fun x => deriv f x * (θ x * w x)) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hi₃ : Integrable (fun x => f x * (θ x * w x)) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := f) (g := fun x => θ x * w x) (v := (1 : ℝ))
    (by simpa only [fderiv_apply_one_eq_deriv] using hi₂)
    (by simpa only [fderiv_apply_one_eq_deriv] using hi₁) hi₃
    (fun x _ => (hf.differentiable (by norm_num)) x)
    (fun x _ => (hg.differentiable (by norm_num)) x)
  simp only [fderiv_apply_one_eq_deriv] at hb
  have hformula (x : ℝ) :
      deriv (fun y => θ y * w y) x =
        (deriv θ x - deriv W x * θ x) * w x := by
    have hd := (((hθ.differentiable (by norm_num)) x).hasDerivAt).mul
      ((((hW.differentiable (by norm_num)) x).hasDerivAt).neg.exp)
    change HasDerivAt (fun y => θ y * w y) _ x at hd
    rw [hd.deriv]
    dsimp [w, scalarConfinementWeight]
    ring
  simp_rw [hformula] at hb
  have hleft : (∫ x, deriv f x * θ x * w x) =
      ∫ x, deriv f x * (θ x * w x) := by
    congr 1
    funext x
    ring
  have hright : (∫ x, f x * (deriv W x * θ x - deriv θ x) * w x) =
      -(∫ x, f x * ((deriv θ x - deriv W x * θ x) * w x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  change (∫ x, deriv f x * θ x * w x) = _
  rw [hleft, hright]
  linarith

end
end GinibrePoincare

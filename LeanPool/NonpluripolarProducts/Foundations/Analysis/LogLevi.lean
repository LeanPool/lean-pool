/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smooth logarithmic potentials

The Hessian and Levi form below are calculated from the actual real Fréchet
derivatives. Positive regularization removes the logarithmic pole.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace SGPT.Foundations.Analysis

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second-order chain rule for the real logarithm of a nowhere-zero C²
function, stated in terms of the genuine Fréchet Hessian. -/
theorem realHessian_log {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hzero : ∀ x, f x ≠ 0) (x v w : E) :
    realHessian (fun y => Real.log (f y)) x v w =
      realHessian f x v w / f x -
        (fderiv ℝ f x v * fderiv ℝ f x w) / (f x) ^ 2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hfirst : fderiv ℝ (fun y => Real.log (f y)) =
      fun y => (f y)⁻¹ • fderiv ℝ f y :=
    funext (fun y => fderiv.log (hd y) (hzero y))
  have hi : HasFDerivAt (fun y => (f y)⁻¹)
      (-(f x ^ 2)⁻¹ • fderiv ℝ f x) x := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv (hzero x)).comp_hasFDerivAt x (hd x).hasFDerivAt
  rw [realHessian_eq_fderiv, hfirst]
  change (fderiv ℝ ((fun y => (f y)⁻¹) • fderiv ℝ f) x) v w = _
  rw [(hi.smul hD.hasFDerivAt).fderiv]
  simp only [realHessian_eq_fderiv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end Hessian

/-- The smooth regularization of the squared-norm logarithmic pole. -/
def regularizedLogNormSq {E : Type*} [NormedAddCommGroup E]
    (ε : ℝ) (x : E) : ℝ := Real.log (‖x‖ ^ 2 + ε)

section RealNormSquare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem contDiff_regularizedLogNormSq {ε : ℝ} (hε : 0 < ε) {n : ℕ∞ω} :
    ContDiff ℝ n (regularizedLogNormSq (E := H) ε) := by
  apply ((contDiff_norm_sq ℝ).add contDiff_const).log
  intro x
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)

/-- The real Hessian of the regularized logarithmic norm in any real inner
product space. -/
theorem realHessian_regularizedLogNormSq {ε : ℝ} (hε : 0 < ε) (x v w : H) :
    realHessian (regularizedLogNormSq ε) x v w =
      2 * inner ℝ v w / (‖x‖ ^ 2 + ε) -
        4 * inner ℝ x v * inner ℝ x w / (‖x‖ ^ 2 + ε) ^ 2 := by
  have hs : ContDiff ℝ 2 (fun y : H => ‖y‖ ^ 2 + ε) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  have hz : ∀ y : H, ‖y‖ ^ 2 + ε ≠ 0 :=
    fun y => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)
  have hH : realHessian (fun y : H => ‖y‖ ^ 2 + ε) x v w =
      2 * inner ℝ v w := by
    change realHessian ((fun y : H => ‖y‖ ^ 2) + (fun _ : H => ε)) x v w = _
    rw [realHessian_add (contDiff_norm_sq ℝ).contDiffAt contDiffAt_const,
      realHessian_const, add_zero, realHessian_norm_sq]
  change realHessian (fun y : H => Real.log (‖y‖ ^ 2 + ε)) x v w = _
  rw [realHessian_log hs hz, hH]
  simp only [fderiv_add_const, fderiv_norm_sq_apply, smul_apply,
    innerSL_apply_apply]
  ring

end RealNormSquare

section ComplexNormSquare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The underlying real inner product induced by the complex inner product. -/
local instance localRealInnerProductSpace : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

/-- The exact Levi form, with the real inner-product pair combined into the
squared norm of the complex inner product. -/
theorem leviForm_regularizedLogNormSq {ε : ℝ} (hε : 0 < ε) (x v : H) :
    leviForm (regularizedLogNormSq ε) x v =
      ((‖x‖ ^ 2 + ε) * ‖v‖ ^ 2 - ‖inner ℂ x v‖ ^ 2) /
        (‖x‖ ^ 2 + ε) ^ 2 := by
  have hs : ‖x‖ ^ 2 + ε ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)
  have hpair : (inner ℝ x v) ^ 2 + (inner ℝ x (Complex.I • v)) ^ 2 =
      ‖inner ℂ x v‖ ^ 2 := by
    change (inner ℂ x v).re ^ 2 + (inner ℂ x (Complex.I • v)).re ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [inner_smul_right, Complex.I_mul_re, neg_sq]
    ring
  calc
    leviForm (regularizedLogNormSq ε) x v =
        ‖v‖ ^ 2 / (‖x‖ ^ 2 + ε) -
          ((inner ℝ x v) ^ 2 + (inner ℝ x (Complex.I • v)) ^ 2) /
            (‖x‖ ^ 2 + ε) ^ 2 := by
      simp only [leviForm, realHessian_regularizedLogNormSq hε,
        real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
      ring
    _ = _ := by
      rw [hpair]
      field_simp

/-- Complex Cauchy--Schwarz gives a quantitative positive Levi lower bound. -/
theorem leviForm_regularizedLogNormSq_lower_bound {ε : ℝ} (hε : 0 < ε)
    (x v : H) :
    ε * ‖v‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2 ≤
      leviForm (regularizedLogNormSq ε) x v := by
  have hs : 0 < ‖x‖ ^ 2 + ε :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hcs : ‖inner ℂ x v‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) x v) 2
  rw [leviForm_regularizedLogNormSq hε]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hs)).mpr
  nlinarith

theorem leviForm_regularizedLogNormSq_nonneg {ε : ℝ} (hε : 0 < ε) (x v : H) :
    0 ≤ leviForm (regularizedLogNormSq ε) x v :=
  (by positivity : 0 ≤ ε * ‖v‖ ^ 2 / (‖x‖ ^ 2 + ε) ^ 2).trans
    (leviForm_regularizedLogNormSq_lower_bound hε x v)

theorem leviForm_regularizedLogNormSq_pos {ε : ℝ} (hε : 0 < ε)
    (x : H) {v : H} (hv : v ≠ 0) :
    0 < leviForm (regularizedLogNormSq ε) x v := by
  have hvp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hs : 0 < ‖x‖ ^ 2 + ε :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  exact (div_pos (mul_pos hε hvp) (sq_pos_of_pos hs)).trans_le
    (leviForm_regularizedLogNormSq_lower_bound hε x v)

/-- Every positive regularization is genuinely disc-plurisubharmonic on any
subset of a complex inner product space. -/
theorem discPshOn_regularizedLogNormSq {ε : ℝ} (hε : 0 < ε) (U : Set H) :
    DiscPshOn (fun x : H => (regularizedLogNormSq ε x : EReal)) U :=
  discPshOn_of_levi_nonneg (contDiff_regularizedLogNormSq hε)
    (fun x _ v => leviForm_regularizedLogNormSq_nonneg hε x v)

theorem plurisubharmonicAt_regularizedLogNormSq {ε : ℝ} (hε : 0 < ε) (x : H) :
    PlurisubharmonicAt (fun y : H => (regularizedLogNormSq ε y : EReal)) x :=
  (discPshOn_regularizedLogNormSq hε univ).plurisubharmonicOn isOpen_univ x (mem_univ x)

end ComplexNormSquare

end SGPT.Foundations.Analysis

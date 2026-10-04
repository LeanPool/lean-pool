/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Factored from the upstream translation, ray-integral and difference-quotient proofs.
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.EllipticPDE.Analysis.PoincareInequality

/-!
# Calculus along affine segments

The derivative and fundamental theorem of calculus along `t ↦ x + t • v`, at C¹
regularity on an arbitrary real normed vector space. Translation estimates,
difference quotients and ray-integral arguments share these identities.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

/-- The derivative of a differentiable function along an affine segment. -/
theorem hasDerivAt_comp_segment (hf : Differentiable ℝ f) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ((fderiv ℝ f (x + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf.differentiableAt.hasFDerivAt).comp_hasDerivAt t hline

/-- The directional derivative of a C¹ function is continuous along a segment. -/
theorem continuous_segment_deriv (hf : ContDiff ℝ 1 f) (x v : E) :
    Continuous (fun t : ℝ => (fderiv ℝ f (x + t • v)) v) :=
  ((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const

/-- Joint continuity of the squared directional derivative along a segment. -/
theorem continuous_squared_segment_deriv (hf : ContDiff ℝ 1 f) (v : E) :
    Continuous (Function.uncurry fun (x : E) (t : ℝ) =>
      ((fderiv ℝ f (x + t • v)) v) ^ 2) :=
  (((hf.continuous_fderiv (by norm_num)).comp (by fun_prop : Continuous
    fun p : E × ℝ => p.1 + p.2 • v)).clm_apply continuous_const).pow 2

/-- Fundamental theorem of calculus along the segment from `x` to `x + v`. -/
theorem sub_translation_eq_integral (hf : ContDiff ℝ 1 f) (x v : E) :
    f (x + v) - f x = ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • v)) v := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_comp_segment hf.differentiable_one x v t)
    (continuous_segment_deriv hf x v).continuousOn.intervalIntegrable]
  simp

/-- The squared increment is bounded by the integral of the squared segment derivative. -/
theorem sq_sub_translation_le (hf : ContDiff ℝ 1 f) (x v : E) :
    (f (x + v) - f x) ^ 2 ≤ ∫ t in (0 : ℝ)..1, ((fderiv ℝ f (x + t • v)) v) ^ 2 := by
  rw [sub_translation_eq_integral hf x v]
  have := MeasureTheory.sq_intervalIntegral_le (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_segment_deriv hf x v).continuousOn
  simpa using this

end EllipticPdes.Analysis

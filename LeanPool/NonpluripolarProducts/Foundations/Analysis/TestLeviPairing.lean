/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothDistribution

/-!
# Levi operators paired with actual test functions

For locally integrable densities, the distributional Levi operator pairs with
the classical Levi form of the test function. Its support is contained in the
test function's compact support, and its integral under a Haar measure is zero. A localized
deficit pairs with its negative, provided localization contains the support of
the test function. No regularity of the density beyond local integrability is
used in the pairing identity.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Opens E}

/-- The actual Hessian vanishes off the topological support of its function.
No differentiability hypothesis is needed for this support assertion. -/
theorem realHessian_eq_zero_of_notMem_tsupport {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) (v w : E) : realHessian f x v w = 0 := by
  have hD : iteratedFDeriv ℝ 2 f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hxD =>
      hx (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) 2 hxD))
  simp only [realHessian, hD, zero_apply]

theorem tsupport_realHessian_subset (f : E → ℝ) (v w : E) :
    tsupport (fun x => realHessian f x v w) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  exact hx (realHessian_eq_zero_of_notMem_tsupport hxf v w)

/-- Two infinite-order bundled test-function derivatives agree with the
actual real Hessian, with outer direction first. -/
theorem testFunction_lineDerivCLM_lineDerivCLM_apply (φ : 𝓓(Ω, ℝ)) (x v w : E) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ) x =
      realHessian φ x v w := by
  have hinner :
      ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ) : E → ℝ) =
        fun y => fderiv ℝ φ y w :=
    funext (fun y => testFunction_lineDerivCLM_apply_eq_fderiv φ w y)
  rw [testFunction_lineDerivCLM_apply_eq_fderiv, hinner,
    fderiv_fderiv_apply_eq_realHessian
      (φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]

section RegularPairing

variable [MeasurableSpace E] [OpensMeasurableSpace E]
variable {μ : Measure E} {u : E → ℝ}

/-- Local integrability on the test-function domain suffices for integrability
of the density against each second derivative of a test function. -/
theorem integrable_mul_realHessian_testFunction (hu : LocallyIntegrableOn u Ω μ)
    (φ : 𝓓(Ω, ℝ)) (v w : E) :
    Integrable (fun x => u x * realHessian φ x v w) μ := by
  have h := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ))
  simpa only [testFunction_lineDerivCLM_lineDerivCLM_apply,
    ContinuousLinearMap.mul_apply', mul_comm] using h

variable [NormedSpace ℂ E]

/-- The density times the test function's classical Levi form is integrable. -/
theorem integrable_mul_leviForm_testFunction (hu : LocallyIntegrableOn u Ω μ)
    (φ : 𝓓(Ω, ℝ)) (v : E) :
    Integrable (fun x => u x * leviForm φ x v) μ := by
  have h := ((integrable_mul_realHessian_testFunction hu φ v v).add
    (integrable_mul_realHessian_testFunction hu φ (Complex.I • v) (Complex.I • v))).div_const 4
  exact h.congr (Eventually.of_forall (fun x => by simp only [leviForm, Pi.add_apply]; ring))

/-- Pairing a distributional Levi derivative with a test function transfers
both derivatives to that test function, with two cancelling signs. -/
theorem distributionalLeviCLM_regularDistribution_apply
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    distributionalLeviCLM v (regularDistribution μ u hu) φ =
      ∫ x, u x * leviForm φ x v ∂μ := by
  have hA : Integrable (fun x => realHessian φ x v v * u x) μ := by
    simpa only [mul_comm] using integrable_mul_realHessian_testFunction hu φ v v
  have hB : Integrable
      (fun x => realHessian φ x (Complex.I • v) (Complex.I • v) * u x) μ := by
    simpa only [mul_comm] using
      integrable_mul_realHessian_testFunction hu φ (Complex.I • v) (Complex.I • v)
  rw [distributionalLeviCLM_apply, regularDistribution_apply, regularDistribution_apply]
  simp only [testFunction_lineDerivCLM_lineDerivCLM_apply]
  rw [← integral_add hA hB, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [leviForm]; ring)

end RegularPairing

section LeviSupport

variable [NormedSpace ℂ E]

/-- The classical Levi form vanishes outside the support of its function. -/
theorem leviForm_eq_zero_of_notMem_tsupport {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) (v : E) : leviForm f x v = 0 := by
  rw [leviForm, realHessian_eq_zero_of_notMem_tsupport hx,
    realHessian_eq_zero_of_notMem_tsupport hx]
  norm_num

theorem tsupport_leviForm_subset (f : E → ℝ) (v : E) :
    tsupport (fun x => leviForm f x v) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  exact hx (leviForm_eq_zero_of_notMem_tsupport hxf v)

end LeviSupport

section Haar

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The integral of any second directional derivative of a test function is
zero. This follows from the proved integration-by-parts theorem for the
constant density; the constant density need not be globally integrable. -/
theorem integral_realHessian_testFunction (φ : 𝓓(Ω, ℝ)) (v w : E) :
    (∫ x, realHessian φ x v w ∂μ) = 0 := by
  have h := congrArg
    (fun T : 𝓓'(Ω, ℝ) =>
      T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ))
    (lineDerivCLM_regularDistribution (μ := μ)
      (show ContDiff ℝ 1 (fun _ : E => (1 : ℝ)) from contDiff_const) v)
  simp only [Distribution.lineDerivCLM_apply, regularDistribution_apply,
    testFunction_lineDerivCLM_lineDerivCLM_apply, fderiv_const_apply,
    zero_apply, mul_one, mul_zero, integral_zero] at h
  exact neg_eq_zero.mp h

variable [NormedSpace ℂ E]

/-- A test function's Levi form has integral zero. -/
theorem integral_leviForm_testFunction (φ : 𝓓(Ω, ℝ)) (v : E) :
    (∫ x, leviForm φ x v ∂μ) = 0 := by
  have hc : LocallyIntegrableOn (fun _ : E => (1 : ℝ)) Ω μ :=
    locallyIntegrableOn_const 1
  have hA : Integrable (fun x => realHessian φ x v v) μ := by
    simpa only [one_mul] using integrable_mul_realHessian_testFunction hc φ v v
  have hB : Integrable (fun x => realHessian φ x (Complex.I • v) (Complex.I • v)) μ := by
    simpa only [one_mul] using
      integrable_mul_realHessian_testFunction hc φ (Complex.I • v) (Complex.I • v)
  simp only [leviForm]
  rw [integral_div, integral_add hA hB, integral_realHessian_testFunction,
    integral_realHessian_testFunction]
  norm_num

/-- If the localization contains the test-function support, the localized
deficit pairs with the negative distributional Levi derivative of the original
density. No assumptions outside the test-function domain, and no measurability
of the localization set, are needed for this pairing identity. -/
theorem integral_indicator_deficit_mul_leviForm_testFunction {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) {K : Set E}
    (hφK : tsupport (φ : E → ℝ) ⊆ K) (C : ℝ) (v : E) :
    (∫ x, K.indicator (fun y => C - u y) x * leviForm φ x v ∂μ) =
      -distributionalLeviCLM v (regularDistribution μ u hu) φ := by
  classical
  have heq : (fun x => K.indicator (fun y => C - u y) x * leviForm φ x v) =
      fun x => C * leviForm φ x v - u x * leviForm φ x v := by
    funext x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      ring
    · have hzero : leviForm φ x v = 0 :=
        leviForm_eq_zero_of_notMem_tsupport (fun hxφ => hx (hφK hxφ)) v
      simp only [Set.indicator_of_notMem hx, hzero, mul_zero, sub_zero]
  have hconst : Integrable (fun x => C * leviForm φ x v) μ :=
    integrable_mul_leviForm_testFunction (locallyIntegrableOn_const C) φ v
  rw [heq, integral_sub hconst (integrable_mul_leviForm_testFunction hu φ v),
    integral_const_mul, integral_leviForm_testFunction, mul_zero, zero_sub,
    distributionalLeviCLM_regularDistribution_apply]

end Haar

end SGPT.Foundations.Analysis

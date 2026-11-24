/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TopDegreeDensity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ConstantFormProducts
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Local Stokes for genuine alternating form fields

On a finite-dimensional real normed space an actual compactly supported `C¹`
form has an exterior derivative whose evaluation on every fixed vector tuple
is integrable with integral zero. This is the finite sum of genuine directional
integration-by-parts identities, with no closed-current or Stokes hypothesis.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoLocalStokes

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ}

private theorem directional_integral_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : E) :
    Integrable (fun x => fderiv ℝ f x v) μ ∧ (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  have hfint : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hc
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := f) (g := fun _ : E => (1 : ℝ)) (v := v)
    (by simpa using hi) (by simp) (by simpa using hfint)
    (fun x _ => hf.differentiable one_ne_zero x) (fun _ _ => differentiableAt_const 1)
  refine ⟨hi, ?_⟩
  have hz : (0 : ℝ) = -(∫ x, fderiv ℝ f x v ∂μ) := by simpa using hparts
  exact neg_eq_zero.mp hz.symm

/-- Local Stokes for the actual exterior derivative of any degree form field. -/
theorem integrable_and_integral_extDeriv_apply_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {a : E → E [⋀^Fin k]→L[ℝ] ℝ} (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (v : Fin (k + 1) → E) :
    Integrable (fun x => extDeriv a x v) μ ∧ (∫ x, extDeriv a x v ∂μ) = 0 := by
  have hsmooth (i : Fin (k + 1)) : ContDiff ℝ 1 (fun x => a x (i.removeNth v)) :=
    (ContinuousAlternatingMap.apply ℝ E ℝ (i.removeNth v)).contDiff.comp ha
  have hcompact (i : Fin (k + 1)) : HasCompactSupport (fun x => a x (i.removeNth v)) :=
    hc.comp_left (g := fun b : E [⋀^Fin k]→L[ℝ] ℝ => b (i.removeNth v)) (by simp)
  have hdir (i : Fin (k + 1)) := directional_integral_eq_zero μ (hsmooth i) (hcompact i) (v i)
  have heq : (fun x => extDeriv a x v) =
      fun x => ∑ i : Fin (k + 1), (-1 : ℝ) ^ i.val *
        fderiv ℝ (fun y => a y (i.removeNth v)) x (v i) := by
    funext x
    rw [extDeriv_apply (ha.differentiable one_ne_zero x)]
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [heq]
  have hint (i : Fin (k + 1)) : Integrable (fun x => (-1 : ℝ) ^ i.val *
      fderiv ℝ (fun y => a y (i.removeNth v)) x (v i)) μ :=
    (hdir i).1.const_mul _
  refine ⟨integrable_finsetSum _ fun i _ => hint i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, (hdir i).2, mul_zero]

open FirstPass StronglyPositiveForms TopDegreeDensity ConstantFormProducts

/-- The preceding local Stokes identity evaluates the genuine top density as well. -/
theorem integrable_and_integral_topDensity_extDeriv_eq_zero {n : ℕ}
    {a : ComplexModel n → RealForm n k} (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (h : k + 1 = 2 * n) :
    Integrable (fun z => topDensity (castForm h (extDeriv a z))) ∧
      (∫ z, topDensity (castForm h (extDeriv a z))) = 0 := by
  have ht := integrable_and_integral_extDeriv_apply_eq_zero volume ha hc
    ((topBasis n) ∘ Fin.cast h)
  simpa only [topDensity, castForm_apply] using ht

end

end SGPT.Foundations.Analysis.Pending.XiaoLocalStokes

/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WirtingerCalculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts for Wirtinger derivatives

On a finite-dimensional complex space `E` with an additive Haar measure, the directional
Wirtinger derivatives `∂_v = (D_v - i D_{iv}) / 2` and `∂bar_v = (D_v + i D_{iv}) / 2` satisfy
`∫ f · ∂bar_v g = - ∫ ∂bar_v f · g` and `∫ f · ∂_v g = - ∫ ∂_v f · g` for `C¹` functions one of
which has compact support.  Conjugation exchanges `∂_v` and `∂bar_v`.
-/

@[expose] public section

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.CauchyGreen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Wirtinger derivative `∂/∂w` along the complex line spanned by `v`. -/
def dDir (v : E) (f : E → ℂ) (x : E) : ℂ :=
  (fderiv ℝ f x v - I * fderiv ℝ f x (I • v)) / 2

theorem fderiv_conj_apply {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) (w : E) :
    fderiv ℝ (fun y ↦ conj (f y)) x w = conj (fderiv ℝ f x w) := by
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp x hf.hasFDerivAt
  exact congrArg (fun L : E →L[ℝ] ℂ ↦ L w) h.fderiv

theorem dDir_conj {v : E} {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    dDir v (fun y ↦ conj (f y)) x = conj (dbarDir v f x) := by
  simp only [dDir, dbarDir, fderiv_conj_apply hf, map_div₀, map_add, map_mul, conj_I, map_ofNat]
  ring

theorem dbarDir_conj {v : E} {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    dbarDir v (fun y ↦ conj (f y)) x = conj (dDir v f x) := by
  simp only [dDir, dbarDir, fderiv_conj_apply hf, map_div₀, map_sub, map_mul, conj_I]
  simp only [map_ofNat]
  ring

variable [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_fderiv_apply' {f : E → ℂ} (hf : ContDiff ℝ 1 f) (w : E) :
    Continuous fun x ↦ fderiv ℝ f x w :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Real integration by parts in direction `w`, with the compact support on either side. -/
theorem integral_mul_fderiv_eq_neg_of_hasCompactSupport {f g : E → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) (w : E) :
    ∫ x, f x * fderiv ℝ g x w ∂μ = - ∫ x, fderiv ℝ f x w * g x ∂μ := by
  have hf' := continuous_fderiv_apply' hf w
  have hg' := continuous_fderiv_apply' hg w
  have hint : ∀ {a b : E → ℂ}, Continuous a → Continuous b →
      (HasCompactSupport a ∨ HasCompactSupport b) →
      Integrable (fun x ↦ a x * b x) μ := by
    intro a b ha hb h
    rcases h with h | h
    · exact (ha.mul hb).integrable_of_hasCompactSupport h.mul_right
    · exact (ha.mul hb).integrable_of_hasCompactSupport h.mul_left
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ ↦ hf.differentiable one_ne_zero x) (fun x _ ↦ hg.differentiable one_ne_zero x)
  · refine hint hf' hg.continuous ?_
    exact hfg.imp (fun h ↦ h.fderiv_apply (𝕜 := ℝ) w) id
  · refine hint hf.continuous hg' ?_
    exact hfg.imp id (fun h ↦ h.fderiv_apply (𝕜 := ℝ) w)
  · exact hint hf.continuous hg.continuous hfg

omit [FiniteDimensional ℂ E] in
theorem integrable_mul_fderiv_of_hasCompactSupport {f g : E → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) (w : E) :
    Integrable (fun x ↦ f x * fderiv ℝ g x w) μ := by
  have hc := hf.continuous.mul (continuous_fderiv_apply' hg w)
  rcases hfg with h | h
  · exact hc.integrable_of_hasCompactSupport h.mul_right
  · exact hc.integrable_of_hasCompactSupport (h.fderiv_apply (𝕜 := ℝ) w).mul_left

omit [FiniteDimensional ℂ E] in
theorem integrable_fderiv_mul_of_hasCompactSupport {f g : E → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) (w : E) :
    Integrable (fun x ↦ fderiv ℝ f x w * g x) μ := by
  have h := integrable_mul_fderiv_of_hasCompactSupport (μ := μ) hg hf hfg.symm w
  simpa only [mul_comm] using h

/-- **Integration by parts for `∂bar_v`.** -/
theorem integral_mul_dbarDir_eq_neg {f g : E → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) (v : E) :
    ∫ x, f x * dbarDir v g x ∂μ = - ∫ x, dbarDir v f x * g x ∂μ := by
  have e1 : (fun x ↦ f x * dbarDir v g x) = fun x ↦
      (2 : ℂ)⁻¹ * (f x * fderiv ℝ g x v) + (I / 2) * (f x * fderiv ℝ g x (I • v)) := by
    funext x; simp only [dbarDir]; ring
  have e2 : (fun x ↦ dbarDir v f x * g x) = fun x ↦
      (2 : ℂ)⁻¹ * (fderiv ℝ f x v * g x) + (I / 2) * (fderiv ℝ f x (I • v) * g x) := by
    funext x; simp only [dbarDir]; ring
  rw [e1, e2, integral_add ((integrable_mul_fderiv_of_hasCompactSupport hf hg hfg v).const_mul _)
      ((integrable_mul_fderiv_of_hasCompactSupport hf hg hfg _).const_mul _),
    integral_add ((integrable_fderiv_mul_of_hasCompactSupport hf hg hfg v).const_mul _)
      ((integrable_fderiv_mul_of_hasCompactSupport hf hg hfg _).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_mul_fderiv_eq_neg_of_hasCompactSupport hf hg hfg,
    integral_mul_fderiv_eq_neg_of_hasCompactSupport hf hg hfg]
  ring

/-- **Integration by parts for `∂_v`.** -/
theorem integral_mul_dDir_eq_neg {f g : E → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfg : HasCompactSupport f ∨ HasCompactSupport g) (v : E) :
    ∫ x, f x * dDir v g x ∂μ = - ∫ x, dDir v f x * g x ∂μ := by
  have e1 : (fun x ↦ f x * dDir v g x) = fun x ↦
      (2 : ℂ)⁻¹ * (f x * fderiv ℝ g x v) + (-I / 2) * (f x * fderiv ℝ g x (I • v)) := by
    funext x; simp only [dDir]; ring
  have e2 : (fun x ↦ dDir v f x * g x) = fun x ↦
      (2 : ℂ)⁻¹ * (fderiv ℝ f x v * g x) + (-I / 2) * (fderiv ℝ f x (I • v) * g x) := by
    funext x; simp only [dDir]; ring
  rw [e1, e2, integral_add ((integrable_mul_fderiv_of_hasCompactSupport hf hg hfg v).const_mul _)
      ((integrable_mul_fderiv_of_hasCompactSupport hf hg hfg _).const_mul _),
    integral_add ((integrable_fderiv_mul_of_hasCompactSupport hf hg hfg v).const_mul _)
      ((integrable_fderiv_mul_of_hasCompactSupport hf hg hfg _).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_mul_fderiv_eq_neg_of_hasCompactSupport hf hg hfg,
    integral_mul_fderiv_eq_neg_of_hasCompactSupport hf hg hfg]
  ring

end

end SGPT.Foundations.Analysis.Pending.CauchyGreen

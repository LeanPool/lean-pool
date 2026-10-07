/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Smooth integration by parts for the shear fields. -/

public section
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace CKN

private theorem contDiff_fderiv_apply_continuous
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    Continuous (fun x => fderiv ℝ f x v) := by
  let F : E → E → ℝ := fun _ y => f y
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
    exact hf.comp contDiff_snd
  have hD : ContDiff ℝ 0 (fun x => fderiv ℝ (F x) (x) v) := by
    exact ContDiff.fderiv_apply hF contDiff_id contDiff_const (by simp)
  simpa [F] using hD.continuous

private theorem hasCompactSupport_fderiv_apply
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (fun x => fderiv ℝ f x v) := by
  apply hf.mono'
  intro x hx
  exact (tsupport_fderiv_apply_subset ℝ v)
    (subset_tsupport (f := fun x => fderiv ℝ f x v) hx)

theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiff_compact_right
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E]
       [FiniteDimensional ℝ E]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {f g : E → ℝ} {v : E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = -∫ x, fderiv ℝ f x v * g x ∂μ := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    contDiff_fderiv_apply_continuous hf v
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    contDiff_fderiv_apply_continuous hg v
  have hdfc := hasCompactSupport_fderiv_apply hgc v
  have hfg' : Integrable (fun x => f x * fderiv ℝ g x v) μ :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport (hdfc.mul_left)
  have hf'g : Integrable (fun x => fderiv ℝ f x v * g x) μ :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left)
  have hfg : Integrable (fun x => f x * g x) μ :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
  · intro x hx
    exact (hf.differentiable (by simp)).differentiableAt
  · intro x hx
    exact (hg.differentiable (by simp)).differentiableAt

end CKN

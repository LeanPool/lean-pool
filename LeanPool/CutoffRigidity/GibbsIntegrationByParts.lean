/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Gibbs
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Integration by parts for the actual Gibbs density

The paper uses integration by parts against `exp (-V) dx` to relate its
Langevin generator and Dirichlet form. This file proves the directional
identity against the actual `gibbsMeasure`, by differentiating the density
and applying the Lebesgue/Haar integration-by-parts theorem.

All required product integrability and differentiability assumptions are
explicit. Thus no compact-support or generator-domain conclusion is silently
assumed for the eigenfunctions used later in the paper.
-/

public section

open MeasureTheory

namespace CutoffRigidity

/-- Gibbs integrability is precisely integrability with the exponential weight. -/
theorem integrable_gibbsMeasure_iff
    {E : Type*} [MeasurableSpace E] (m : Measure E) {V : E → ℝ} (hV : Measurable V)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) :
    Integrable f (gibbsMeasure m V) ↔ Integrable (fun x => Real.exp (-V x) • f x) m := by
  rw [gibbsMeasure, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- Differentiating `exp (-V) f` produces the weighted divergence term. -/
theorem fderiv_gibbsWeight_mul_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V f : E → ℝ} {x v : E} (hV : DifferentiableAt ℝ V x)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => Real.exp (-V y) * f y) x v =
      Real.exp (-V x) * (fderiv ℝ f x v - f x * fderiv ℝ V x v) := by
  have he : HasFDerivAt (fun y => Real.exp (-V y))
      (Real.exp (-V x) • -fderiv ℝ V x) x := hV.hasFDerivAt.neg.exp
  rw [fderiv_fun_mul he.differentiableAt hf, he.fderiv]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
  ring

/-- Directional integration by parts for the actual Gibbs measure.
The three product-integrability hypotheses give the precise domain on which
this formula is proved. -/
theorem integral_mul_fderiv_gibbs_eq_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : Measure E) [m.IsAddHaarMeasure]
    {V f g : E → ℝ} (hV : Differentiable ℝ V) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : E)
    (hfg : Integrable (fun x => f x * g x) (gibbsMeasure m V))
    (hfg' : Integrable (fun x => f x * fderiv ℝ g x v) (gibbsMeasure m V))
    (hdfg : Integrable
      (fun x => (fderiv ℝ f x v - f x * fderiv ℝ V x v) * g x) (gibbsMeasure m V)) :
    (∫ x, f x * fderiv ℝ g x v ∂gibbsMeasure m V) =
      -(∫ x, (fderiv ℝ f x v - f x * fderiv ℝ V x v) * g x ∂gibbsMeasure m V) := by
  have hVm : Measurable V := hV.continuous.measurable
  let φ : E → ℝ := fun x => Real.exp (-V x) * f x
  have hφ : Differentiable ℝ φ := hV.neg.exp.mul hf
  have hφg : Integrable (fun x => φ x * g x) m := by
    have h := (integrable_gibbsMeasure_iff m hVm _).mp hfg
    simpa only [φ, smul_eq_mul, mul_assoc] using h
  have hφg' : Integrable (fun x => φ x * fderiv ℝ g x v) m := by
    have h := (integrable_gibbsMeasure_iff m hVm _).mp hfg'
    simpa only [φ, smul_eq_mul, mul_assoc] using h
  have hderiv (x : E) : fderiv ℝ φ x v * g x =
      Real.exp (-V x) * ((fderiv ℝ f x v - f x * fderiv ℝ V x v) * g x) := by
    rw [show fderiv ℝ φ x v = _ from fderiv_gibbsWeight_mul_apply (hV x) (hf x)]
    ring
  have hφ'g : Integrable (fun x => fderiv ℝ φ x v * g x) m := by
    simp_rw [hderiv]
    exact (integrable_gibbsMeasure_iff m hVm _).mp hdfg
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hφ'g hφg' hφg (fun x _ => hφ x) (fun x _ => hg x)
  rw [integral_gibbsMeasure m hVm, integral_gibbsMeasure m hVm]
  simpa only [φ, hderiv, smul_eq_mul, mul_assoc] using hibp

end CutoffRigidity

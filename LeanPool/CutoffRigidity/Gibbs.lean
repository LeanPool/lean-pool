/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity

/-!
# Gibbs measures and full support

The paper's invariant measure has density `exp (-V)`. A positive density
preserves null sets and full support. Thus continuous tensor norms that
vanish almost everywhere also vanish everywhere, as used in rigidity.
The invariance and diffusion construction are separate obligations.
-/

public section

open MeasureTheory

namespace CutoffRigidity

variable {E : Type*} [MeasurableSpace E]

/-- Gibbs measure relative to a reference volume. The potential's additive
normalization is supplied separately when a probability measure is required. -/
@[expose] noncomputable def gibbsMeasure (m : Measure E) (V : E → ℝ) : Measure E :=
  m.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))

theorem gibbsMeasure_absolutelyContinuous (m : Measure E) (V : E → ℝ) :
    gibbsMeasure m V ≪ m := withDensity_absolutelyContinuous _ _

/-- Integrating against the paper's Gibbs measure means integrating against
its actual exponential density, also for vector-valued integrands. -/
theorem integral_gibbsMeasure (m : Measure E) {V : E → ℝ} (hV : Measurable V)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) :
    ∫ x, f x ∂gibbsMeasure m V = ∫ x, Real.exp (-V x) • f x ∂m := by
  rw [gibbsMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- An additively normalized potential defines a genuine probability measure. -/
theorem gibbsMeasure_isProbabilityMeasure (m : Measure E) (V : E → ℝ)
    (hfinite : Integrable (fun x => Real.exp (-V x)) m)
    (hnormalized : ∫ x, Real.exp (-V x) ∂m = 1) :
    IsProbabilityMeasure (gibbsMeasure m V) := by
  constructor
  rw [gibbsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfinite
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-V x)).le)), hnormalized]
  simp

/-- The additive normalization of the potential used at the start of the
paper, with its finite positive partition integral made explicit. -/
theorem gibbsMeasure_normalize_potential (m : Measure E) (V : E → ℝ)
    (hfinite : Integrable (fun x => Real.exp (-V x)) m)
    (hpositive : 0 < ∫ x, Real.exp (-V x) ∂m) :
    IsProbabilityMeasure (gibbsMeasure m
      (fun x => V x + Real.log (∫ y, Real.exp (-V y) ∂m))) := by
  have heq (x : E) :
      Real.exp (-(V x + Real.log (∫ y, Real.exp (-V y) ∂m))) =
        Real.exp (-V x) / (∫ y, Real.exp (-V y) ∂m) := by
    rw [neg_add, Real.exp_add,
      Real.exp_neg (Real.log (∫ y, Real.exp (-V y) ∂m)), Real.exp_log hpositive]
    rfl
  apply gibbsMeasure_isProbabilityMeasure
  · simp_rw [heq]
    exact hfinite.div_const _
  · simp_rw [heq]
    simp only [div_eq_mul_inv, integral_mul_const]
    exact mul_inv_cancel₀ (ne_of_gt hpositive)

theorem absolutelyContinuous_gibbsMeasure (m : Measure E) {V : E → ℝ}
    (hV : Measurable V) : m ≪ gibbsMeasure m V := by
  apply withDensity_absolutelyContinuous' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => ne_of_gt
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

/-- Positivity of the Gibbs density makes its null sets exactly those of volume. -/
theorem gibbsMeasure_ae_eq_iff (m : Measure E) {V : E → ℝ}
    (hV : Measurable V) {F : Type*} {f g : E → F} :
    f =ᵐ[gibbsMeasure m V] g ↔ f =ᵐ[m] g := by
  exact ⟨(absolutelyContinuous_gibbsMeasure m hV).ae_eq,
    (gibbsMeasure_absolutelyContinuous m V).ae_eq⟩

variable [TopologicalSpace E]

theorem gibbsMeasure_isOpenPosMeasure (m : Measure E) [m.IsOpenPosMeasure]
    {V : E → ℝ} (hV : Measurable V) : (gibbsMeasure m V).IsOpenPosMeasure :=
  (absolutelyContinuous_gibbsMeasure m hV).isOpenPosMeasure

/-- The almost-everywhere-to-everywhere step in the rigidity proof, for a
continuous quantity such as the norm of the Hessian. -/
theorem gibbsMeasure_eq_of_ae_eq (m : Measure E) [m.IsOpenPosMeasure]
    {V : E → ℝ} (hV : Measurable V) {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : E → F} (hf : Continuous f) (hg : Continuous g)
    (hae : f =ᵐ[gibbsMeasure m V] g) : f = g := by
  exact MeasureTheory.Measure.eq_of_ae_eq
    ((gibbsMeasure_ae_eq_iff m hV).mp hae) hf hg

/-- Vanishing integrated squared tensor norm implies pointwise vanishing.
This is the positivity and full-support step after the integrated Bochner
inequality; it applies in particular to a continuous Hessian tensor. -/
theorem gibbsMeasure_eq_zero_of_integral_norm_sq_eq_zero
    (m : Measure E) [m.IsOpenPosMeasure] {V : E → ℝ} (hV : Measurable V)
    {F : Type*} [NormedAddCommGroup F] {H : E → F} (hH : Continuous H)
    (hfinite : Integrable (fun x => ‖H x‖ ^ 2) (gibbsMeasure m V))
    (hzero : ∫ x, ‖H x‖ ^ 2 ∂gibbsMeasure m V = 0) : H = 0 := by
  have hnorm : (fun x => ‖H x‖ ^ 2) =ᵐ[gibbsMeasure m V] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖H x‖) hfinite).mp hzero
  apply gibbsMeasure_eq_of_ae_eq m hV (g := fun _ => (0 : F)) hH continuous_const
  filter_upwards [hnorm] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

end CutoffRigidity

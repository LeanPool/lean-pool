/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Real change of variables between different finite-dimensional carriers

A fixed genuine continuous linear equivalence identifies the two
carriers. Its positive Haar normalization is retained explicitly. The
remaining determinant is the ordinary endomorphism determinant from
the pinned change-of-variables theorem.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal NNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

/-- Linear Haar scale obtained from `Measure.addHaarScalarFactor`. -/
noncomputable def linearHaarScale (J : E ≃L[ℝ] F) : ℝ≥0 :=
  Measure.addHaarScalarFactor (ν.map J.symm) μ

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem linearHaarScale_pos (J : E ≃L[ℝ] F) : 0 < linearHaarScale μ ν J :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (ν.map J.symm) μ

omit [FiniteDimensional ℝ F] in
theorem linearHaarScale_map (J : E ≃L[ℝ] F) :
    ν.map J.symm = linearHaarScale μ ν J • μ :=
  Measure.isAddLeftInvariant_eq_smul (ν.map J.symm) μ

omit [FiniteDimensional ℝ F] in
theorem lintegral_linear_image (J : E ≃L[ℝ] F) (s : Set E) (g : F → ℝ≥0∞) :
    (∫⁻ y in J '' s, g y ∂ν) =
      (linearHaarScale μ ν J : ℝ≥0∞) * ∫⁻ x in s, g (J x) ∂μ := by
  let e : E ≃ᵐ F := J.toHomeomorph.toMeasurableEquiv
  have ht : (ν.map e.symm).restrict s = (ν.restrict (e '' s)).map e.symm := by
    rw [e.symm.restrict_map]
    congr 1
    exact congrArg ν.restrict (e.image_eq_preimage_symm s).symm
  have h : (∫⁻ x in s, g (e x) ∂ν.map e.symm) = ∫⁻ y in e '' s, g y ∂ν := by
    rw [ht, lintegral_map_equiv]
    simp only [MeasurableEquiv.apply_symm_apply]
  change (∫⁻ y in e '' s, g y ∂ν) = _
  rw [← h]
  change (∫⁻ x in s, g (J x) ∂ν.map J.symm) = _
  rw [linearHaarScale_map μ ν J, Measure.restrict_smul, lintegral_smul_measure]
  rfl

omit [FiniteDimensional ℝ F] in
theorem lintegral_image_eq_linearHaarScale_jacobian (J : E ≃L[ℝ] F)
    {f : E → F} {f' : E → E →L[ℝ] F} {s : Set E}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : Set.InjOn f s) (g : F → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y ∂ν) = (linearHaarScale μ ν J : ℝ≥0∞) *
      ∫⁻ x in s, ENNReal.ofReal |(J.symm.toContinuousLinearMap.comp (f' x)).det| *
        g (f x) ∂μ := by
  have him : f '' s = J '' ((fun x => J.symm (f x)) '' s) := by
    rw [Set.image_image]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [him, lintegral_linear_image μ ν J]
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs
    (fun x hx => HasFDerivAt.comp_hasFDerivWithinAt x
      J.symm.toContinuousLinearMap.hasFDerivAt (hf' x hx))
    (fun x hx y hy h => hinj hx hy (J.symm.injective h)) (fun y => g (J y))
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using
    congrArg (fun t : ℝ≥0∞ => (linearHaarScale μ ν J : ℝ≥0∞) * t) hchange

end VacuumBellSeparation

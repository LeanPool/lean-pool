/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DivCurlCutoffCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffDerivatives

/-!
# High-contrast homogenization: Provider.Response.AdaptedCutoffGradientField

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The gradient field of the adapted cutoff

The div-curl estimate reads a cutoff through its gradient field: it needs that
field to be essentially bounded on the cube, to have smooth components, and to
have a bounded componentwise derivative.  The adapted cutoff carries instead a
bound for its first derivative and a bound for its second iterated derivative,
so the componentwise derivative of the gradient field has to be recovered from
the second iterated derivative.

This module performs that recovery in adapted coordinates and reads off the
three cutoff data of the div-curl estimate with one common dimension-only
coefficient.  The reference-cube div-curl coefficient then loses both of its
free parameters.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory Book.Ch05.Section53.JUpperBoundWeakNorms

open scoped ENNReal

variable {d : ℕ}

/-! ## The common derivative coefficient -/

/-- The common dimension-only coefficient of the adapted cutoff's first two
derivatives in adapted coordinates. -/
@[expose]
def adaptedCutoffDerivativeCoeff (d : ℕ) : ℝ :=
  1024 * (d : ℝ) ^ 4 *
    (max 1 (max smoothTransitionProfile.derivBound
      smoothTransitionProfile.secondDerivBound)) ^ 2

/-- The defining equation of the common derivative coefficient. -/
theorem adaptedCutoffDerivativeCoeff_eq (d : ℕ) :
    adaptedCutoffDerivativeCoeff d =
      1024 * (d : ℝ) ^ 4 *
        (max 1 (max smoothTransitionProfile.derivBound
          smoothTransitionProfile.secondDerivBound)) ^ 2 := rfl

/-- The common derivative coefficient is nonnegative. -/
theorem adaptedCutoffDerivativeCoeff_nonneg (d : ℕ) :
    0 ≤ adaptedCutoffDerivativeCoeff d := by
  rw [adaptedCutoffDerivativeCoeff]
  positivity

/-! ## Smoothness of the pullback -/

/-- The pullback of the adapted cutoff by the grid matrix is smooth. -/
theorem adaptedPreYoungCutoff_pullback_smooth [NeZero d] {q : Mat d}
    (hq : q.PosDef) (t : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) := by
  have hlinear : ContDiff ℝ (⊤ : ℕ∞) (matVecMul q) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)).contDiff
  simpa only [Function.comp_def] using
    (adaptedPreYoungCutoff_smooth hq t).comp hlinear

/-! ## The three cutoff data of the div-curl estimate -/

/-- **The componentwise derivative of the gradient field.**  Each component of
the gradient field of the pulled-back adapted cutoff has derivative bounded by
the common coefficient times the square of the reciprocal side length.  The
second iterated derivative dominates each componentwise derivative. -/
theorem scalarCutoffGradientField_adaptedPreYoungCutoff_pullback_fderiv_bound
    [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ) (Q : TriadicCube d) :
    ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => scalarCutoffGradientField
          (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) x i) z‖ ≤
        adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-2 * t) :=
  scalarCutoffGradientField_component_fderiv_bound_on_cubeSet_of_hessian_bound Q
    (adaptedPreYoungCutoff_pullback_smooth hq t)
    (fun z _ => adaptedPreYoungCutoff_pullback_iteratedFDeriv_two_bound hq t z)

/-- **The sup norm of the gradient field.**  It is bounded by the common
coefficient times the reciprocal side length. -/
theorem cubeLpNorm_infty_scalarCutoffGradientField_adaptedPreYoungCutoff_pullback_le
    [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ) (Q : TriadicCube d) :
    cubeLpNorm Q ∞ (scalarCutoffGradientField
        (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y))) ≤
      adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-t) :=
  cubeLpNorm_infty_scalarCutoffGradientField_le_of_bound_on_cubeSet Q
    (mul_nonneg (adaptedCutoffDerivativeCoeff_nonneg d) (by positivity))
    (fun z _ => adaptedPreYoungCutoff_pullback_fderiv_bound hq t z)

/-- The gradient field of the pulled-back adapted cutoff is essentially bounded
on every triadic cube. -/
theorem memLp_top_scalarCutoffGradientField_adaptedPreYoungCutoff_pullback
    [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ) (Q : TriadicCube d) :
    MemLp (scalarCutoffGradientField
        (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y))) ∞
      (normalizedCubeMeasure Q) :=
  memLp_top_scalarCutoffGradientField_of_bound_on_cubeSet Q
    (adaptedPreYoungCutoff_pullback_smooth hq t)
    (fun z _ => adaptedPreYoungCutoff_pullback_fderiv_bound hq t z)

/-- Each component of that gradient field is smooth. -/
theorem contDiff_scalarCutoffGradientField_adaptedPreYoungCutoff_pullback
    [NeZero d] {q : Mat d} (hq : q.PosDef) (t : ℤ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => scalarCutoffGradientField
      (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) x i) :=
  contDiff_scalarCutoffGradientField_component
    (adaptedPreYoungCutoff_pullback_smooth hq t) i

/-! ## The div-curl coefficient at the adapted cutoff -/

/-- **The div-curl coefficient at the adapted cutoff.**  Inserting the two
cutoff bounds leaves a dimension-only prefactor times the reciprocal side
length; no bound is carried. -/
theorem divCurlWeakNormCoeff_originCube_adaptedPreYoungCutoff_le (d : ℕ)
    [NeZero d] (t : ℤ) :
    divCurlWeakNormCoeff (originCube d t)
        (adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-2 * t))
        (adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-t)) ≤
      divCurlDimensionCoeff d *
        (adaptedCutoffDerivativeCoeff d * (3 : ℝ) ^ (-t)) :=
  divCurlWeakNormCoeff_originCube_le t le_rfl le_rfl

/-! ## The div-curl weak-norm term at the adapted cutoff -/

end

end Response
end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluation
public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceMomentsTestExtension
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexifiedFunctional

/-!
# Literal wave evaluation as a complex-linear original-source functional

Linearity is proved for the actual compact Fourier integral before its
complex extension is formed. No continuity or weighted bound is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Gaussian Gaussian.HilbertComplexification

theorem integrable_complexSpatialFourier (f : SpatialTestFunction) (z : Fin 3 → ℂ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ)))) * (f.1 x : ℂ)) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ))))) := by
    unfold spatialDot
    fun_prop
  exact (hc.mul (Complex.continuous_ofReal.comp f.2.1.continuous)).integrable_of_hasCompactSupport
    ((f.2.2.comp_left Complex.ofReal_zero).mul_left)

theorem complexSpatialFourier_add (f g : SpatialTestFunction) (z : Fin 3 → ℂ) :
    complexSpatialFourier (f + g) z = complexSpatialFourier f z + complexSpatialFourier g z := by
  unfold complexSpatialFourier
  change (∫ x : EuclideanSpace ℝ (Fin 3),
    Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ)))) *
      ((f.1 x + g.1 x : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_add, mul_add]
  exact integral_add (integrable_complexSpatialFourier f z) (integrable_complexSpatialFourier g z)

theorem complexSpatialFourier_smul (a : ℝ) (f : SpatialTestFunction) (z : Fin 3 → ℂ) :
    complexSpatialFourier (a • f) z = a • complexSpatialFourier f z := by
  unfold complexSpatialFourier
  rw [← integral_smul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ)))) *
    ((a * f.1 x : ℝ) : ℂ) = a •
      (Complex.exp (-(Complex.I * spatialDot z (fun j => (x j : ℂ)))) * (f.1 x : ℂ))
  rw [Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The real-linear map evaluating the complex source wave at the specified mass-shell point. -/
noncomputable def complexSourceWaveLinear (z : ComplexSpacetime) : TimeZeroSource →ₗ[ℝ] ℂ where
  toFun u := complexSourceWave u z
  map_add' u v := by
    change complexSpatialFourier (u.1 + v.1) z.2 + Complex.I * z.1 *
      complexSpatialFourier (u.2 + v.2) z.2 = _
    simp only [complexSpatialFourier_add, complexSourceWave]
    ring
  map_smul' a u := by
    change complexSpatialFourier (a • u.1) z.2 + Complex.I * z.1 *
      complexSpatialFourier (a • u.2) z.2 = _
    simp only [complexSpatialFourier_smul, complexSourceWave, Complex.real_smul,
      RingHom.id_apply]
    ring

/-- Linear map for the complex source test wave, of type `ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ`. -/
noncomputable def complexSourceTestWave {m : ℝ} (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (z : ComplexSpacetime) :
    ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ :=
  complexifyFunctional ((complexSourceWaveLinear z).comp
    ((localizedTimeZeroSources U).subtype : SourceTestSpace hm U →ₗ[ℝ] TimeZeroSource))

theorem complexSourceTestWave_apply {m : ℝ} (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (z : ComplexSpacetime)
    (x : ComplexSourceTestSpace hm U) :
    complexSourceTestWave hm U z x =
      complexSourceWave x.re.1 z + Complex.I * complexSourceWave x.im.1 z := rfl

theorem complexSourceTestInclusion_decompose {m : ℝ} (hm : 0 < m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (x : ComplexSourceTestSpace hm U) :
    complexSourceTestInclusion hm U x =
      ofReal (x.re : SourceHilbert hm U) + Complex.I • ofReal (x.im : SourceHilbert hm U) := by
  conv_lhs => rw [← mk_re_im x]
  rw [complexSourceTestInclusion_mk]
  exact eq_ofReal_add_I_smul (mk (x.re : SourceHilbert hm U) (x.im : SourceHilbert hm U))

end VacuumBellSeparation

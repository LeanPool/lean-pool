/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceReserveWave
public import LeanPool.VacuumBellSeparation.Shell.SpatialFourierEnergyCircle

/-!
# The actual entire field and momentum Fourier functionals

The two components are recovered from the original wave at opposite
complex energies. The division identity is stated only for nonzero
energy; the entire momentum component itself is defined everywhere.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification

/-- Complex-linear spatial Fourier transform on Schwartz functions. -/
noncomputable def complexSpatialFourierLinear (z : Fin 3 → ℂ) : SpatialTestFunction →ₗ[ℝ] ℂ where
  toFun f := complexSpatialFourier f z
  map_add' f g := complexSpatialFourier_add f g z
  map_smul' a f := complexSpatialFourier_smul a f z

private theorem differentiable_complexSpatialFourier_spatial (f : SpatialTestFunction) :
    Differentiable ℂ (complexSpatialFourier f) := by
  have hs : Differentiable ℂ (fun w : ComplexSpacetime => complexSpatialFourier f w.2) :=
    fun w => (hasFDerivAt_complexSpatialFourier f w).differentiableAt
  have hpair : Differentiable ℂ (fun z : Fin 3 → ℂ => ((0 : ℂ), z)) :=
    (differentiable_const (0 : ℂ)).prodMk differentiable_id
  simpa only [Function.comp_def] using
    (Differentiable.comp (f := fun z : Fin 3 → ℂ => ((0 : ℂ), z))
      (g := fun w : ComplexSpacetime => complexSpatialFourier f w.2) hs hpair)

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Linear map for the complex source field Fourier, of type `ComplexSourceTestSpace hm U →ₗ[ℂ]
ℂ`. -/
noncomputable def complexSourceFieldFourier (z : Fin 3 → ℂ) :
    ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ :=
  complexifyFunctional (((complexSpatialFourierLinear z).comp
    (LinearMap.fst ℝ SpatialTestFunction SpatialTestFunction)).comp
      ((localizedTimeZeroSources U).subtype : SourceTestSpace hm U →ₗ[ℝ] TimeZeroSource))

/-- Linear map for the complex source momentum Fourier, of type `ComplexSourceTestSpace hm U →ₗ[ℂ]
ℂ`. -/
noncomputable def complexSourceMomentumFourier (z : Fin 3 → ℂ) :
    ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ :=
  complexifyFunctional (((complexSpatialFourierLinear z).comp
    (LinearMap.snd ℝ SpatialTestFunction SpatialTestFunction)).comp
      ((localizedTimeZeroSources U).subtype : SourceTestSpace hm U →ₗ[ℝ] TimeZeroSource))

theorem complexSourceFieldFourier_apply (z : Fin 3 → ℂ) (x : ComplexSourceTestSpace hm U) :
    complexSourceFieldFourier hm U z x =
      complexSpatialFourier x.re.1.1 z + Complex.I * complexSpatialFourier x.im.1.1 z := rfl

theorem complexSourceMomentumFourier_apply (z : Fin 3 → ℂ) (x : ComplexSourceTestSpace hm U) :
    complexSourceMomentumFourier hm U z x =
      complexSpatialFourier x.re.1.2 z + Complex.I * complexSpatialFourier x.im.1.2 z := rfl

theorem complexSourceTestWave_components (z : ComplexSpacetime)
    (x : ComplexSourceTestSpace hm U) :
    complexSourceTestWave hm U z x = complexSourceFieldFourier hm U z.2 x +
      Complex.I * z.1 * complexSourceMomentumFourier hm U z.2 x := by
  simp only [complexSourceTestWave_apply, complexSourceWave,
    complexSourceFieldFourier_apply, complexSourceMomentumFourier_apply]
  ring

theorem complexSourceFieldFourier_opposite_energy (e : ℂ) (z : Fin 3 → ℂ)
    (x : ComplexSourceTestSpace hm U) :
    complexSourceFieldFourier hm U z x =
      (complexSourceTestWave hm U (e, z) x + complexSourceTestWave hm U (-e, z) x) / 2 := by
  simp only [complexSourceTestWave_components]
  ring

theorem complexSourceMomentumFourier_opposite_energy {e : ℂ} (he : e ≠ 0)
    (z : Fin 3 → ℂ) (x : ComplexSourceTestSpace hm U) :
    complexSourceMomentumFourier hm U z x =
      (complexSourceTestWave hm U (e, z) x - complexSourceTestWave hm U (-e, z) x) /
        (2 * Complex.I * e) := by
  simp only [complexSourceTestWave_components]
  field_simp [he]
  ring

theorem complexSourceFieldFourier_norm_bound (e : ℂ) (z : Fin 3 → ℂ)
    (x : ComplexSourceTestSpace hm U) {M : ℝ}
    (hp : ‖complexSourceTestWave hm U (e, z) x‖ ≤ M)
    (hn : ‖complexSourceTestWave hm U (-e, z) x‖ ≤ M) :
    ‖complexSourceFieldFourier hm U z x‖ ≤ M := by
  rw [complexSourceFieldFourier_opposite_energy hm U e z x, norm_div, Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    ((norm_add_le _ _).trans (by linarith))

theorem complexSourceMomentumFourier_norm_bound {e : ℂ} (he : e ≠ 0)
    (z : Fin 3 → ℂ) (x : ComplexSourceTestSpace hm U) {M : ℝ}
    (hp : ‖complexSourceTestWave hm U (e, z) x‖ ≤ M)
    (hn : ‖complexSourceTestWave hm U (-e, z) x‖ ≤ M) :
    ‖complexSourceMomentumFourier hm U z x‖ ≤ M / ‖e‖ := by
  rw [complexSourceMomentumFourier_opposite_energy hm U he z x,
    norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  have hb := (norm_sub_le _ _).trans (show
    ‖complexSourceTestWave hm U (e, z) x‖ + ‖complexSourceTestWave hm U (-e,
      z) x‖ ≤ 2 * M by linarith)
  calc
    _ ≤ (2 * M) / (2 * ‖e‖) := div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by ring

theorem differentiable_complexSourceFieldFourier (x : ComplexSourceTestSpace hm U) :
    Differentiable ℂ (fun z : Fin 3 → ℂ => complexSourceFieldFourier hm U z x) := by
  simp only [complexSourceFieldFourier_apply]
  exact (differentiable_complexSpatialFourier_spatial x.re.1.1).add
    ((differentiable_complexSpatialFourier_spatial x.im.1.1).const_mul Complex.I)

theorem differentiable_complexSourceMomentumFourier (x : ComplexSourceTestSpace hm U) :
    Differentiable ℂ (fun z : Fin 3 → ℂ => complexSourceMomentumFourier hm U z x) := by
  simp only [complexSourceMomentumFourier_apply]
  exact (differentiable_complexSpatialFourier_spatial x.re.1.2).add
    ((differentiable_complexSpatialFourier_spatial x.im.1.2).const_mul Complex.I)

end VacuumBellSeparation

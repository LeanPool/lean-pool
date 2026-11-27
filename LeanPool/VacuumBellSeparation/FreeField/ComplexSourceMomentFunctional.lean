/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialFourierMomentCoefficients

/-!
# Literal polynomial moments as complex-linear original-source functionals
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Gaussian Gaussian.HilbertComplexification

theorem spatialTestMoment_add (f g : SpatialTestFunction) (α : Fin 3 → ℕ) :
    spatialTestMoment (f + g) α = spatialTestMoment f α + spatialTestMoment g α := by
  unfold spatialTestMoment
  change (∫ x, spatialMonomial α x * ((f.1 x + g.1 x : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_add, mul_add]
  exact integral_add (integrable_spatialTestMoment f α) (integrable_spatialTestMoment g α)

theorem spatialTestMoment_smul (a : ℝ) (f : SpatialTestFunction) (α : Fin 3 → ℕ) :
    spatialTestMoment (a • f) α = a • spatialTestMoment f α := by
  unfold spatialTestMoment
  rw [← integral_smul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change spatialMonomial α x * ((a * f.1 x : ℝ) : ℂ) =
    a • (spatialMonomial α x * (f.1 x : ℂ))
  rw [Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Linear map for the spatial test moment linear, of type `SpatialTestFunction →ₗ[ℝ] ℂ where toFun
f`. -/
noncomputable def spatialTestMomentLinear (α : Fin 3 → ℕ) : SpatialTestFunction →ₗ[ℝ] ℂ where
  toFun f := spatialTestMoment f α
  map_add' f g := spatialTestMoment_add f g α
  map_smul' a f := spatialTestMoment_smul a f α

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- Linear map for the complex source field moment, of type `ComplexSourceTestSpace hm U →ₗ[ℂ]
ℂ`. -/
noncomputable def complexSourceFieldMoment (α : Fin 3 → ℕ) :
    ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ :=
  complexifyFunctional (((spatialTestMomentLinear α).comp
    (LinearMap.fst ℝ SpatialTestFunction SpatialTestFunction)).comp
      ((localizedTimeZeroSources U).subtype : SourceTestSpace hm U →ₗ[ℝ] TimeZeroSource))

/-- Linear map for the complex source momentum moment, of type `ComplexSourceTestSpace hm U →ₗ[ℂ]
ℂ`. -/
noncomputable def complexSourceMomentumMoment (α : Fin 3 → ℕ) :
    ComplexSourceTestSpace hm U →ₗ[ℂ] ℂ :=
  complexifyFunctional (((spatialTestMomentLinear α).comp
    (LinearMap.snd ℝ SpatialTestFunction SpatialTestFunction)).comp
      ((localizedTimeZeroSources U).subtype : SourceTestSpace hm U →ₗ[ℝ] TimeZeroSource))

theorem complexSourceFieldMoment_apply (α : Fin 3 → ℕ) (x : ComplexSourceTestSpace hm U) :
    complexSourceFieldMoment hm U α x =
      spatialTestMoment x.re.1.1 α + Complex.I * spatialTestMoment x.im.1.1 α := rfl

theorem complexSourceMomentumMoment_apply (α : Fin 3 → ℕ) (x : ComplexSourceTestSpace hm U) :
    complexSourceMomentumMoment hm U α x =
      spatialTestMoment x.re.1.2 α + Complex.I * spatialTestMoment x.im.1.2 α := rfl

end VacuumBellSeparation

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RapidityCoordinates
public import LeanPool.VacuumBellSeparation.FreeField.Existence

/-!
# Jacobian of the genuine massive-shell rapidity coordinates

The shell density times the positive Jacobian is the constant 1/(2(2π)^3).
Both transverse coordinates remain present throughout.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- Rapidity coordinate given by `PiLp.proj 2 (fun _ : Fin 3 => ℝ) i`. -/
noncomputable def rapidityCoordinate (i : Fin 3) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

/-- Continuous linear map for the transverse mass deriv, of type `EuclideanSpace ℝ (Fin 3) →L[ℝ]
ℝ`. -/
noncomputable def transverseMassDeriv (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (1 / (2 * transverseMass m x)) •
    ((2 * x 1) • rapidityCoordinate 1 + (2 * x 2) • rapidityCoordinate 2)

theorem hasFDerivAt_transverseMass {m : ℝ} (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (transverseMass m) (transverseMassDeriv m x) x := by
  have h1 := ((rapidityCoordinate 1).hasFDerivAt (x := x)).pow 2
  have h2 := ((rapidityCoordinate 2).hasFDerivAt (x := x)).pow 2
  have hn : m ^ 2 + ((x 1) ^ 2 + (x 2) ^ 2) ≠ 0 := by positivity
  have h := ((h1.add h2).const_add (m ^ 2)).sqrt hn
  change HasFDerivAt
    (fun y : EuclideanSpace ℝ (Fin 3) => Real.sqrt (m ^ 2 + (y 1) ^ 2 + (y 2) ^ 2))
    (transverseMassDeriv m x) x
  simpa only [transverseMass, transverseMassDeriv, rapidityCoordinate, PiLp.proj_apply,
    Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, add_assoc, Pi.add_apply] using h

theorem transverseMassDeriv_e₁ (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    transverseMassDeriv m x e₁ = 0 := by
  simp [transverseMassDeriv, rapidityCoordinate, e₁]

/-- Continuous linear map for the rapidity momentum deriv, of type `EuclideanSpace ℝ (Fin 3) →L[ℝ]
EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def rapidityMomentumDeriv (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
    (Real.sinh (x 0) • transverseMassDeriv m x +
      (transverseMass m x * Real.cosh (x 0) - 1) • rapidityCoordinate 0).smulRight e₁

theorem rapidityMomentum_eq_add_smul (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    rapidityMomentum m x = x + (transverseMass m x * Real.sinh (x 0) - x 0) • e₁ := by
  ext i
  fin_cases i <;> simp [rapidityMomentum, e₁]

theorem hasFDerivAt_rapidityMomentum {m : ℝ} (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (rapidityMomentum m) (rapidityMomentumDeriv m x) x := by
  have h0 := (rapidityCoordinate 0).hasFDerivAt (x := x)
  have h := (hasFDerivAt_id x).add
    ((((hasFDerivAt_transverseMass hm x).mul h0.sinh).sub h0).smul_const e₁)
  have he : rapidityMomentum m = fun y : EuclideanSpace ℝ (Fin 3) =>
      y + (transverseMass m y * Real.sinh (y 0) - y 0) • e₁ :=
    funext (rapidityMomentum_eq_add_smul m)
  rw [he]
  refine h.congr_fderiv ?_
  ext v i
  simp only [rapidityMomentumDeriv, _root_.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    _root_.sub_apply, _root_.smul_apply, rapidityCoordinate, PiLp.proj_apply, smul_eq_mul]
  ring_nf

theorem det_rapidityMomentumDeriv (m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    (rapidityMomentumDeriv m x).det = transverseMass m x * Real.cosh (x 0) := by
  rw [rapidityMomentumDeriv, det_id_add_smulRight_e₁]
  simp [transverseMassDeriv, rapidityCoordinate, e₁]


theorem det_rapidityMomentumDeriv_eq_dispersion {m : ℝ} (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (rapidityMomentumDeriv m x).det = dispersion m (rapidityMomentum m x) := by
  rw [det_rapidityMomentumDeriv, dispersion_rapidityMomentum hm]

/-- The constant density of the one-particle measure in rapidity and transverse momentum
coordinates. -/
noncomputable def rapidityDensity : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3))

theorem rapidity_jacobian_weight {m : ℝ} (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ENNReal.ofReal |(rapidityMomentumDeriv m x).det| *
      (oneParticleWeight m (rapidityMomentum m x) : ℝ≥0∞) = rapidityDensity := by
  have hω := dispersion_pos hm.ne' (rapidityMomentum m x)
  have hK : (2 * (2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  have he : |(rapidityMomentumDeriv m x).det| *
      (oneParticleWeight m (rapidityMomentum m x) : ℝ) = 1 / (2 * (2 * Real.pi) ^ 3) := by
    rw [det_rapidityMomentumDeriv_eq_dispersion hm, abs_of_pos hω, oneParticleWeight_coe hm]
    field_simp [hω.ne', hK]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (abs_nonneg _), he]
  rfl

/-- The exact rapidity measure. The physical normalization is retained explicitly. -/
noncomputable def rapidityMeasure : Measure (EuclideanSpace ℝ (Fin 3)) :=
  rapidityDensity • volume

theorem measurePreserving_rapidityMomentum {m : ℝ} (hm : 0 < m) :
    MeasurePreserving (rapidityMomentum m) rapidityMeasure (oneParticleMeasure m) := by
  have hmeas := (continuous_rapidityMomentum m).measurable
  refine ⟨hmeas, ?_⟩
  apply Measure.ext
  intro s hs
  have hpre := hs.preimage hmeas
  rw [Measure.map_apply hmeas hs, oneParticleMeasure, withDensity_apply _ hs]
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre
    (fun x hx => (hasFDerivAt_rapidityMomentum hm x).hasFDerivWithinAt)
    (rapidityHomeomorph hm).injective.injOn
    (fun p => (oneParticleWeight m p : ℝ≥0∞))
  have hsurj : Function.Surjective (rapidityMomentum m) := (rapidityHomeomorph hm).surjective
  rw [Set.image_preimage_eq s hsurj] at hj
  rw [hj]
  simp [rapidityMeasure, rapidity_jacobian_weight hm]

end VacuumBellSeparation

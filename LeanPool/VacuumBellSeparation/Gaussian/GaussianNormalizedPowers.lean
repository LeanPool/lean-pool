/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianPurityTrace
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeThermalPowers
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceScaling

/-!
# Actual normalized powers of a physical Gaussian density

The same constructed symplectic unitary diagonalizes the density and every
positive CFC power. Dividing by the actual positive finite trace changes
each thermal parameter q to q^r and gives the stated physical covariance.
This is an operator equality on the full oscillator space, including pure
factors, rather than a definition of a new state by its target covariance.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem conjStarAlgEquiv_real_smul (e : E ≃ₗᵢ[ℂ] F) (c : ℝ) (A : E →L[ℂ] E) :
    e.conjStarAlgEquiv (c • A) = c • e.conjStarAlgEquiv A := by
  ext x
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, smul_apply]
  exact LinearMapClass.map_smul_of_tower e c _

theorem normalizedPositiveDensity_conjStarAlgEquiv
    (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    normalizedPositiveDensity (e.conjStarAlgEquiv A) =
      e.conjStarAlgEquiv (normalizedPositiveDensity A) := by
  rw [normalizedPositiveDensity, positiveTrace_conjStarAlgEquiv e hA,
    normalizedPositiveDensity, conjStarAlgEquiv_real_smul]

variable {m : ℕ}

theorem normalizedPositiveDensity_matrixDensityPullback_rpow
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : Sᵀ * modeSymplecticForm * S = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : 0 ≤ A) {r : ℝ} (hr : 0 ≤ r) :
    normalizedPositiveDensity (matrixDensityPullback S hS A ^ r) =
      matrixDensityPullback S hS (normalizedPositiveDensity (A ^ r)) := by
  let e : MultiModeOscillatorSpace m ≃ₗᵢ[ℂ] MultiModeOscillatorSpace m :=
    (symplecticWeylImplementer (matrixWeylLabelMap_preservesWeylForm S hS)).symm
  change normalizedPositiveDensity ((e.conjStarAlgEquiv A) ^ r) =
    e.conjStarAlgEquiv (normalizedPositiveDensity (A ^ r))
  calc
    _ = normalizedPositiveDensity (e.conjStarAlgEquiv (A ^ r)) :=
      congrArg normalizedPositiveDensity
        (conjStarAlgEquiv_rpow (E := MultiModeOscillatorSpace m)
          (F := MultiModeOscillatorSpace m) e (A := A) hA (τ := r) hr).symm
    _ = _ := normalizedPositiveDensity_conjStarAlgEquiv e CFC.rpow_nonneg

/-- Powered mode variance defined as `thermalQuadratureVariance (covarianceThermalParameter v ^
r)`. -/
def poweredModeVariance (r v : ℝ) : ℝ :=
  thermalQuadratureVariance (covarianceThermalParameter v ^ r)

theorem poweredModeVariance_half_le {r v : ℝ} (hr : 0 < r) (hv : 1 / 2 ≤ v) :
    1 / 2 ≤ poweredModeVariance r v := by
  unfold poweredModeVariance
  exact half_le_thermalQuadratureVariance
    (Real.rpow_nonneg (covarianceThermalParameter_nonneg hv) _)
    (Real.rpow_lt_one (covarianceThermalParameter_nonneg hv)
      (covarianceThermalParameter_lt_one hv) hr)

theorem normalizedPositiveDensity_covarianceProductDensity_rpow
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) {r : ℝ} (hr : 0 < r) :
    normalizedPositiveDensity (covarianceProductDensity ν ^ r) =
      covarianceProductDensity (fun j => poweredModeVariance r (ν j)) := by
  change normalizedMultiThermalPower (fun j => covarianceThermalParameter (ν j)) r = _
  rw [normalizedMultiThermalPower_eq_density
    (fun j => covarianceThermalParameter_nonneg (hν j))
    (fun j => covarianceThermalParameter_lt_one (hν j)) hr]
  unfold covarianceProductDensity poweredModeVariance
  congr 1
  funext j
  exact (covarianceThermalParameter_variance
    (Real.rpow_nonneg (covarianceThermalParameter_nonneg (hν j)) _)
    (Real.rpow_lt_one (covarianceThermalParameter_nonneg (hν j))
      (covarianceThermalParameter_lt_one (hν j)) hr)).symm

/-- Actual full-space equality after normalization by the actual power trace. -/
theorem normalizedPositiveDensity_physicalWilliamsonDensity_rpow
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) {r : ℝ} (hr : 0 < r) :
    normalizedPositiveDensity (physicalWilliamsonDensity S hS ν ^ r) =
      physicalWilliamsonDensity S hS (fun j => poweredModeVariance r (ν j)) := by
  rw [physicalWilliamsonDensity,
    normalizedPositiveDensity_matrixDensityPullback_rpow _ _
      (covarianceProductDensity_nonneg hν) hr.le,
    normalizedPositiveDensity_covarianceProductDensity_rpow hν hr]
  rfl

theorem normalizedPositiveDensity_gaussianPhysical_rpow_eq
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ))
    {r : ℝ} (hr : 0 < r) :
    normalizedPositiveDensity (A ^ r) =
      physicalWilliamsonDensity S hS (fun j => poweredModeVariance r (ν j)) := by
  rw [gaussianPhysical_eq_physicalWilliamsonDensity hA S hS hν hG]
  exact normalizedPositiveDensity_physicalWilliamsonDensity_rpow S hS hν hr

theorem normalizedPositiveDensity_gaussianPhysical_rpow_characteristic
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ))
    {r : ℝ} (hr : 0 < r) :
    HasGaussianPhysicalCharacteristic (normalizedPositiveDensity (A ^ r))
      (S * modeDiagonal (fun j => poweredModeVariance r (ν j)) * Sᵀ) := by
  rw [normalizedPositiveDensity_gaussianPhysical_rpow_eq hA S hS hν hG hr]
  exact physicalWilliamsonDensity_hasGaussianPhysicalCharacteristic S hS
    (fun j => poweredModeVariance_half_le hr (hν j))

end VacuumBellSeparation.Gaussian

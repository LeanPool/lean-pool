/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteGaussianRealization
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowerNormalization

/-!
# Normalized genuine powers of the finite-mode thermal density

The positive trace is finite and strictly positive before its real inverse
is used. Normalizing the actual CFC power gives the actual product density
with parameters `q_j^τ`, including pure factors and the empty product.
The associated state is tied to this density by its positive sandwich
trace and has the explicitly transformed covariance in fixed labels.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

/-- Multi thermal power trace given by `∏ j, (1 - q j) ^ τ / (1 - q j ^ τ)`. -/
def multiThermalPowerTrace {m : ℕ} (q : Fin m → ℝ) (τ : ℝ) : ℝ :=
  ∏ j, (1 - q j) ^ τ / (1 - q j ^ τ)

theorem multiThermalPowerTrace_pos {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    0 < multiThermalPowerTrace q τ :=
  Finset.prod_pos fun j _ => thermalPowerTrace_pos (hq₀ j) (hq₁ j) hτ

/-- Continuous linear map for the normalized multi thermal power, of type `MultiModeOscillatorSpace
m →L[ℂ] MultiModeOscillatorSpace m`. -/
def normalizedMultiThermalPower {m : ℕ} (q : Fin m → ℝ) (τ : ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  (positiveTrace (multiModeThermalDensity q ^ τ)).toReal⁻¹ • (multiModeThermalDensity q ^ τ)

theorem thermalWeight_power_normalization {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (n : ℕ) :
    ((1 - q) ^ τ / (1 - q ^ τ))⁻¹ * thermalWeight q n ^ τ =
      thermalWeight (q ^ τ) n := by
  have hc : (1 - q) ^ τ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr hq₁) _)
  have hd : 1 - q ^ τ ≠ 0 := ne_of_gt (sub_pos.mpr (Real.rpow_lt_one hq₀ hq₁ hτ))
  rw [thermalWeight_rpow hq₀ hq₁, thermalWeight]
  field_simp [hc, hd]

theorem multiModeThermalWeight_power_normalization {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (k : Fin m → ℕ) :
    (multiThermalPowerTrace q τ)⁻¹ * multiModeThermalWeight q k ^ τ =
      multiModeThermalWeight (fun j => q j ^ τ) k := by
  rw [multiThermalPowerTrace, multiModeThermalWeight_rpow hq₀ hq₁,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, multiModeThermalWeight]
  exact Finset.prod_congr rfl fun j _ => thermalWeight_power_normalization (hq₀ j) (hq₁ j) hτ _

/-- Equality of actual bounded operators on the entire occupation space. -/
theorem normalizedMultiThermalPower_eq_density {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    normalizedMultiThermalPower q τ = multiModeThermalDensity (fun j => q j ^ τ) := by
  unfold normalizedMultiThermalPower
  rw [positiveTrace_multiModeThermalDensity_rpow hq₀ hq₁ hτ]
  change (ENNReal.ofReal (multiThermalPowerTrace q τ)).toReal⁻¹ •
    multiModeThermalDensity q ^ τ = _
  rw [ENNReal.toReal_ofReal (multiThermalPowerTrace_pos hq₀ hq₁ hτ).le]
  apply continuousLinearMap_eq_of_dense_span (multiModeNumberBasis _)
    (multiModeNumberBasis _).dense_span
  intro k
  rw [smul_apply, multiModeThermalDensity_rpow_apply_numberBasis hq₀ hq₁ hτ,
    multiModeThermalDensity_apply_numberBasis (fun j => Real.rpow_nonneg (hq₀ j) _)
      (fun j => Real.rpow_lt_one (hq₀ j) (hq₁ j) hτ), smul_smul]
  exact congrArg (fun r : ℝ => r • multiModeNumberBasis _ k)
    (multiModeThermalWeight_power_normalization hq₀ hq₁ hτ k)

theorem positiveTrace_normalizedMultiThermalPower {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    positiveTrace (normalizedMultiThermalPower q τ) = 1 := by
  rw [normalizedMultiThermalPower_eq_density hq₀ hq₁ hτ]
  exact positiveTrace_multiModeThermalDensity (fun j => Real.rpow_nonneg (hq₀ j) _)
    (fun j => Real.rpow_lt_one (hq₀ j) (hq₁ j) hτ)

/-- Normalized multi thermal state defined as `multiThermalState (fun j => Real.rpow_nonneg (hq₀ j)
_) (fun j => Real.rpow_lt_one (hq₀ j) (hq₁ j) hτ)`. -/
def normalizedMultiThermalState {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    State (MultiModeOscillatorSpace m) :=
  multiThermalState (fun j => Real.rpow_nonneg (hq₀ j) _)
    (fun j => Real.rpow_lt_one (hq₀ j) (hq₁ j) hτ)

theorem positiveTrace_normalizedMultiThermal_sandwich {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    positiveTrace (CFC.sqrt (normalizedMultiThermalPower q τ) * A *
      CFC.sqrt (normalizedMultiThermalPower q τ)) =
        ENNReal.ofReal (normalizedMultiThermalState hq₀ hq₁ hτ A).re := by
  rw [normalizedMultiThermalPower_eq_density hq₀ hq₁ hτ]
  exact positiveTrace_multiThermal_sandwich (fun j => Real.rpow_nonneg (hq₀ j) _)
    (fun j => Real.rpow_lt_one (hq₀ j) (hq₁ j) hτ) hA

/-- Normalized positive powers keep the actual Weyl labels fixed, while
the variances change by `q_j ↦ q_j^τ`. -/
theorem normalizedMultiThermalState_finiteGaussianWeyl
    {ι : Type*} [Fintype ι] {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (S : Matrix ι (Fin m × Fin 2) ℝ) (x : ι → ℝ) :
    normalizedMultiThermalState hq₀ hq₁ hτ (finiteGaussianWeyl S x) =
      Complex.exp ((-(1 / 2) * (x ⬝ᵥ ((S *
        modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) * Sᵀ) *ᵥ x)) : ℝ) : ℂ) := by
  classical
  rw [normalizedMultiThermalState, finiteGaussianWeyl, multiThermalState_quadratureWeyl]
  simp only [modeQuadratureTuple]
  rw [← dotProduct_modeDiagonal, dotProduct_congruence]

end VacuumBellSeparation.Gaussian

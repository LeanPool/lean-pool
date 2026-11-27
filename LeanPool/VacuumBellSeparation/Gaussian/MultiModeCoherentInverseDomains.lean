/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModePowerDomains

/-!
# Coherent vectors in the genuine inverse thermal-power domain

All exponential and normalized coherent vectors belong to the range of
every positive power of a faithful thermal density. The inverse on that
actual range scales the labels by `q_j^(-τ)`. This is a domain statement,
not a bounded-inverse assertion, and is valid for every finite number of
modes, including zero.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

/-- The product of the geometric mode prefactors raised to the same thermal power. -/
def multiModePowerPartition {m : ℕ} (q : Fin m → ℝ) (τ : ℝ) : ℝ :=
  ∏ j, (1 - q j) ^ τ

theorem multiModePowerPartition_pos {m : ℕ} {q : Fin m → ℝ}
    (hq₁ : ∀ j, q j < 1) (τ : ℝ) : 0 < multiModePowerPartition q τ :=
  Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (sub_pos.mpr (hq₁ j)) _

theorem multiModeThermalDensity_rpow_apply_coordinate {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (x : MultiModeOscillatorSpace m) (k : Fin m → ℕ) :
    (multiModeThermalDensity q ^ τ) x k = ((multiModeThermalWeight q k ^ τ : ℝ) : ℂ) * x k := by
  let B := multiModeThermalDensity q ^ τ
  have hB : IsSelfAdjoint B := CFC.rpow_nonneg.isSelfAdjoint
  have h := B.adjoint_inner_left x (multiModeNumberBasis m k)
  rw [hB.adjoint_eq, multiModeThermalDensity_rpow_apply_numberBasis hq₀ hq₁ hτ,
    inner_smul_left_eq_smul, multiModeNumberBasis_inner, multiModeNumberBasis_inner,
    Algebra.smul_def] at h
  simpa only [Complex.coe_algebraMap] using h.symm

theorem multiModeThermalDensity_rpow_apply_exponentialVector {m : ℕ}
    {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (z : Fin m → ℂ) :
    (multiModeThermalDensity q ^ τ) (multiExponentialVector z) =
      multiModePowerPartition q τ •
        multiExponentialVector (fun j => ((q j ^ τ : ℝ) : ℂ) * z j) := by
  ext k
  rw [multiModeThermalDensity_rpow_apply_coordinate hq₀ hq₁ hτ]
  change ((multiModeThermalWeight q k ^ τ : ℝ) : ℂ) * multiCoherentCoefficient z k =
    multiModePowerPartition q τ •
      multiCoherentCoefficient (fun j => ((q j ^ τ : ℝ) : ℂ) * z j) k
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal]
  simp only [multiModeThermalWeight_rpow hq₀ hq₁, multiModePowerPartition,
    multiCoherentCoefficient, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [thermalWeight_rpow (hq₀ j) (hq₁ j)]
  simp only [coherentCoefficient, Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
  ring

/-- Multi mode inverse power label given by `fun j => ((q j ^ (-τ) : ℝ) : ℂ) * z j`. -/
def multiModeInversePowerLabel {m : ℕ} (q : Fin m → ℝ) (τ : ℝ)
    (z : Fin m → ℂ) : Fin m → ℂ := fun j => ((q j ^ (-τ) : ℝ) : ℂ) * z j

theorem multiModePower_inverseLabel {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 < q j) (τ : ℝ) (z : Fin m → ℂ) :
    (fun j => ((q j ^ τ : ℝ) : ℂ) * multiModeInversePowerLabel q τ z j) = z := by
  funext j
  simp only [multiModeInversePowerLabel, ← mul_assoc, ← Complex.ofReal_mul]
  rw [← Real.rpow_add (hq₀ j), add_neg_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]

theorem multiModeThermalPower_inverse_exponentialVector {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (z : Fin m → ℂ) :
    (multiModeThermalDensity q ^ τ)
      ((multiModePowerPartition q τ)⁻¹ •
        multiExponentialVector (multiModeInversePowerLabel q τ z)) = multiExponentialVector z := by
  rw [LinearMapClass.map_smul_of_tower,
    multiModeThermalDensity_rpow_apply_exponentialVector (fun j => (hq₀ j).le) hq₁ hτ,
    multiModePower_inverseLabel hq₀,
    inv_smul_smul₀ (ne_of_gt (multiModePowerPartition_pos hq₁ τ))]

theorem multiExponentialVector_mem_powerDomain {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (z : Fin m → ℂ) :
    multiExponentialVector z ∈ multiThermalPowerDomain q τ :=
  ⟨(multiModePowerPartition q τ)⁻¹ •
    multiExponentialVector (multiModeInversePowerLabel q τ z),
    multiModeThermalPower_inverse_exponentialVector hq₀ hq₁ hτ z⟩

/-- Multi domain exponential vector represented by `multiExponentialVector z`. -/
def multiDomainExponentialVector {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (z : Fin m → ℂ) :
    multiThermalPowerDomain q τ :=
  ⟨multiExponentialVector z, multiExponentialVector_mem_powerDomain hq₀ hq₁ hτ z⟩

theorem multiThermalInversePower_exponentialVector {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (z : Fin m → ℂ) :
    multiThermalInversePower hq₀ hq₁ hτ (multiDomainExponentialVector hq₀ hq₁ hτ z) =
      (multiModePowerPartition q τ)⁻¹ •
        multiExponentialVector (multiModeInversePowerLabel q τ z) := by
  apply multiModeThermalDensity_rpow_injective hq₀ hq₁ hτ
  rw [multiThermalPower_apply_inversePower,
    multiModeThermalPower_inverse_exponentialVector hq₀ hq₁ hτ]
  rfl

theorem multiCoherentVector_mem_powerDomain {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (z : MultiModePhaseSpace m) : multiCoherentVector z ∈ multiThermalPowerDomain q τ :=
  Submodule.smul_mem _ _ (multiExponentialVector_mem_powerDomain hq₀ hq₁ hτ (fun j => z j))

/-- Multi domain coherent vector represented by `multiCoherentVector z`. -/
def multiDomainCoherentVector {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (z : MultiModePhaseSpace m) :
    multiThermalPowerDomain q τ :=
  ⟨multiCoherentVector z, multiCoherentVector_mem_powerDomain hq₀ hq₁ hτ z⟩

theorem multiThermalInversePower_coherentVector {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) (z : MultiModePhaseSpace m) :
    multiThermalInversePower hq₀ hq₁ hτ (multiDomainCoherentVector hq₀ hq₁ hτ z) =
      Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) •
        ((multiModePowerPartition q τ)⁻¹ •
          multiExponentialVector (multiModeInversePowerLabel q τ (fun j => z j))) := by
  have heq : multiDomainCoherentVector hq₀ hq₁ hτ z =
      Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) •
        multiDomainExponentialVector hq₀ hq₁ hτ (fun j => z j) := rfl
  rw [heq, map_smul, multiThermalInversePower_exponentialVector hq₀ hq₁ hτ]

end VacuumBellSeparation.Gaussian

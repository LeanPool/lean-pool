/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCoherentInverseDomains
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeSandwich

/-!
# The actual inverse-domain sandwich Bargmann kernel

The kernel is evaluated on vectors in the true range domain before any
bounded extension is constructed. For an arbitrary bounded A it is the
kernel of A at the rescaled labels, with the literal thermal prefactor
`(∏ (1-q_j))^(-τ)`. Positivity needs only A≥0. Summability is required
only for the later identification with the constructed bounded operator.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped ComplexConjugate ComplexOrder

/-- Multi Bargmann kernel obtained from `inner`. -/
def multiBargmannKernel {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (z w : Fin m → ℂ) : ℂ :=
  inner ℂ (multiExponentialVector z) (A (multiExponentialVector w))

theorem multiModePowerPartition_eq {m : ℕ} {q : Fin m → ℝ}
    (hq₁ : ∀ j, q j < 1) (τ : ℝ) :
    multiModePowerPartition q τ = (∏ j, (1 - q j)) ^ τ := by
  exact (Real.finsetProd_rpow Finset.univ (fun j => 1 - q j)
    (fun j _ => sub_nonneg.mpr (hq₁ j).le) τ)

theorem multiModePowerPartition_half_inverse_sq {m : ℕ} {q : Fin m → ℝ}
    (hq₁ : ∀ j, q j < 1) (τ : ℝ) :
    ((multiModePowerPartition q (τ / 2))⁻¹) ^ 2 = (∏ j, (1 - q j)) ^ (-τ) := by
  have hZ : 0 < ∏ j, (1 - q j) := Finset.prod_pos fun j _ => sub_pos.mpr (hq₁ j)
  rw [multiModePowerPartition_eq hq₁, ← Real.rpow_neg hZ.le,
    pow_two, ← Real.rpow_add hZ]
  congr 1
  ring

/-- This identity holds on the actual inverse domain even when its
positive form has no bounded extension. -/
theorem multiThermalSandwichForm_exponential_kernel {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (z w : Fin m → ℂ) :
    multiThermalSandwichForm hq₀ hq₁ hτ A
      (multiDomainExponentialVector hq₀ hq₁ (half_pos hτ) z)
      (multiDomainExponentialVector hq₀ hq₁ (half_pos hτ) w) =
        (((∏ j, (1 - q j)) ^ (-τ) : ℝ) : ℂ) *
          multiBargmannKernel A (multiModeInversePowerLabel q (τ / 2) z)
            (multiModeInversePowerLabel q (τ / 2) w) := by
  rw [multiThermalSandwichForm,
    multiThermalInversePower_exponentialVector hq₀ hq₁ (half_pos hτ),
    multiThermalInversePower_exponentialVector hq₀ hq₁ (half_pos hτ),
    LinearMapClass.map_smul_of_tower, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  simp only [Algebra.smul_def, Complex.coe_algebraMap]
  rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow,
    multiModePowerPartition_half_inverse_sq hq₁]
  rfl

theorem multiThermalSandwichForm_coherent_diagonal {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (z : MultiModePhaseSpace m) :
    multiThermalSandwichForm hq₀ hq₁ hτ A
      (multiDomainCoherentVector hq₀ hq₁ (half_pos hτ) z)
      (multiDomainCoherentVector hq₀ hq₁ (half_pos hτ) z) =
        Complex.exp ((-‖z‖ ^ 2 : ℝ) : ℂ) * (((∏ j, (1 - q j)) ^ (-τ) : ℝ) : ℂ) *
          multiBargmannKernel A
            (multiModeInversePowerLabel q (τ / 2) (fun j => z j))
            (multiModeInversePowerLabel q (τ / 2) (fun j => z j)) := by
  let a := Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ)
  have hcoh : multiDomainCoherentVector hq₀ hq₁ (half_pos hτ) z =
      a • multiDomainExponentialVector hq₀ hq₁ (half_pos hτ) (fun j => z j) := rfl
  have haa : conj a * a = Complex.exp ((-‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [show conj a = a by
      dsimp only [a]
      rw [← Complex.exp_conj, Complex.conj_ofReal], ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcoh, multiThermalSandwichForm, map_smul, map_smul,
    inner_smul_left, inner_smul_right]
  change conj a * (a * multiThermalSandwichForm hq₀ hq₁ hτ A
    (multiDomainExponentialVector hq₀ hq₁ (half_pos hτ) (fun j => z j))
    (multiDomainExponentialVector hq₀ hq₁ (half_pos hτ) (fun j => z j))) = _
  rw [← mul_assoc, haa, multiThermalSandwichForm_exponential_kernel hq₀ hq₁ hτ]
  ring

theorem multiThermalSandwichForm_nonneg {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (x : multiThermalPowerDomain q (τ / 2)) :
    0 ≤ multiThermalSandwichForm hq₀ hq₁ hτ A x x :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).inner_nonneg_right _

theorem multiThermalSandwichOperator_bargmannKernel {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (hsum : Summable (multiInverseThermalDiagonal q τ A)) (z w : Fin m → ℂ) :
    multiBargmannKernel (multiThermalSandwichOperator hq₀ hq₁ hA hsum) z w =
      (((∏ j, (1 - q j)) ^ (-τ) : ℝ) : ℂ) *
        multiBargmannKernel A (multiModeInversePowerLabel q (τ / 2) z)
          (multiModeInversePowerLabel q (τ / 2) w) := by
  exact (multiThermalSandwichForm_eq_inner hq₀ hq₁ hτ hA hsum
    (multiDomainExponentialVector hq₀ hq₁ (half_pos hτ) z)
    (multiDomainExponentialVector hq₀ hq₁ (half_pos hτ) w)).symm.trans
      (multiThermalSandwichForm_exponential_kernel hq₀ hq₁ hτ A z w)

end VacuumBellSeparation.Gaussian

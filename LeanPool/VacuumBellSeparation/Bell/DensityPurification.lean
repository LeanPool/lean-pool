/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.HilbertAmplification
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveDensityState

/-!
# An actual Hilbert-space purification of a density operator

For a genuine Hilbert basis, the vector with coordinates sqrt(ρ)bᵢ
belongs to the vector-valued Hilbert direct sum. Its vector expectation
under diagonal amplification is exactly the actual density expectation.
No cyclicity or representation-equivalence claim is part of this definition.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped InnerProductSpace ComplexOrder ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (b : HilbertBasis ι ℂ H) {ρ : H →L[ℂ] H} (hρ : IsPositiveTraceClass ρ)

/-- The literal square-root column vector, with actual ℓ² membership proved. -/
noncomputable def densityPurification : lp (fun _ : ι => H) 2 :=
  ⟨fun i => CFC.sqrt ρ (b i), memℓp_gen (by
    simpa using summable_sqrt_basis_norm_sq b hρ)⟩

@[simp] theorem densityPurification_apply (i : ι) :
    densityPurification b hρ i = CFC.sqrt ρ (b i) := rfl

theorem densityPurification_norm_sq :
    ‖densityPurification b hρ‖ ^ 2 = (positiveTrace ρ).toReal := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (densityPurification b hρ)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, densityPurification_apply,
    tsum_sqrt_basis_norm_sq b hρ] using h

theorem densityPurification_norm (htrace : positiveTrace ρ = 1) :
    ‖densityPurification b hρ‖ = 1 := by
  have h := densityPurification_norm_sq b hρ
  rw [htrace, ENNReal.toReal_one] at h
  nlinarith [norm_nonneg (densityPurification b hρ)]

/-- The exact complex vector-state equality for every bounded observable. -/
theorem inner_densityPurification_amplification (A : H →L[ℂ] H) :
    ⟪densityPurification b hρ, hilbertAmplification ι A (densityPurification b hρ)⟫_ℂ =
      densityExpectation b ρ A := rfl

/-- Products are preserved by the actual amplification homomorphism. -/
theorem inner_densityPurification_amplification_product (A B : H →L[ℂ] H) :
    ⟪densityPurification b hρ,
      hilbertAmplification ι A (hilbertAmplification ι B (densityPurification b hρ))⟫_ℂ =
        densityExpectation b ρ (A * B) := rfl

end VacuumBellSeparation

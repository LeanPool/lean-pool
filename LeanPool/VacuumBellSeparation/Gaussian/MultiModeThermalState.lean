/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.IndexedDiagonalState
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCanonicalThermalModel

/-!
# The actual finite-mode thermal state

The state is the absolutely convergent full occupation-basis series of the
actual product density. Positive inputs agree with the extended positive
trace of the square-root sandwich. This gives a genuine complex functional
for Weyl expectations; the positive trace is not applied to `ρ W`.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- Multi thermal state. -/
noncomputable def multiThermalState {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) : State (MultiModeOscillatorSpace m) :=
  indexedDiagonalState (multiModeNumberBasis m) (hasSum_multiModeThermalWeight hq₀ hq₁).summable
    (multiModeThermalWeight_nonneg hq₀ hq₁) (hasSum_multiModeThermalWeight hq₀ hq₁).tsum_eq

theorem multiThermalState_apply {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    multiThermalState hq₀ hq₁ A = ∑' k, (multiModeThermalWeight q k : ℂ) *
      inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k)) := rfl

theorem hasSum_multiThermalState {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    HasSum (fun k => (multiModeThermalWeight q k : ℂ) *
      inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k)))
      (multiThermalState hq₀ hq₁ A) :=
  (summable_indexedDiagonalExpectation_terms (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable A).hasSum

theorem norm_multiThermalState_le {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    ‖multiThermalState hq₀ hq₁ A‖ ≤ ‖A‖ := by
  change ‖indexedDiagonalExpectation (multiModeNumberBasis m) (multiModeThermalWeight q) A‖ ≤ ‖A‖
  have h := norm_indexedDiagonalExpectation_le (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable A
  simpa only [abs_of_nonneg (multiModeThermalWeight_nonneg hq₀ hq₁ _),
    (hasSum_multiModeThermalWeight hq₀ hq₁).tsum_eq, one_mul] using h

theorem positiveTrace_multiThermal_sandwich {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    positiveTrace (CFC.sqrt (multiModeThermalDensity q) * A * CFC.sqrt
      (multiModeThermalDensity q)) =
      ENNReal.ofReal (multiThermalState hq₀ hq₁ A).re :=
  positiveTrace_indexedDiagonal_sandwich (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable (multiModeThermalWeight_nonneg hq₀ hq₁) hA

end VacuumBellSeparation.Gaussian

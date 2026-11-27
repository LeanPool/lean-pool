/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeSandwich
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalSandwichCriterion

/-!
# Exact weighted-diagonal criterion for a noncommuting inverse sandwich

Every bounded factorization has the forced weighted diagonal. Therefore
the existence of a positive trace-class factorization is equivalent to
summability of that diagonal. The arbitrary positive input A need not
commute with the faithful product thermal reference.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}

theorem multiThermal_factorization_diagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hfactor : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) (k : Fin m → ℕ) :
    (inner ℂ (multiModeNumberBasis m k) (Θ (multiModeNumberBasis m k))).re =
      multiInverseThermalDiagonal q τ A k := by
  let b : (Fin m → ℕ) → ℝ := fun k => multiModeThermalWeight q k ^ (τ / 2)
  let B := multiModeThermalDensity q ^ (τ / 2)
  have hB : IsSelfAdjoint B := CFC.rpow_nonneg.isSelfAdjoint
  have heig : B (multiModeNumberBasis m k) = b k • multiModeNumberBasis m k :=
    multiModeThermalDensity_rpow_apply_numberBasis (fun j => (hq₀ j).le) hq₁ (half_pos hτ) k
  have hentry : inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k)) =
      (b k : ℂ) * (b k : ℂ) *
        inner ℂ (multiModeNumberBasis m k) (Θ (multiModeNumberBasis m k)) := by
    rw [← hfactor]
    change inner ℂ (multiModeNumberBasis m k) (B (Θ (B (multiModeNumberBasis m k)))) = _
    have hmove : inner ℂ (multiModeNumberBasis m k) (B (Θ (B (multiModeNumberBasis m k)))) =
        inner ℂ (B (multiModeNumberBasis m k)) (Θ (B (multiModeNumberBasis m k))) := by
      simpa only [hB.adjoint_eq] using
        B.adjoint_inner_right (multiModeNumberBasis m k) (Θ (B (multiModeNumberBasis m k)))
    rw [hmove, heig, LinearMapClass.map_smul_of_tower,
      inner_smul_left_eq_smul, inner_smul_right_eq_smul]
    simp only [Algebra.smul_def, Complex.coe_algebraMap]
    ring
  have hreal : (inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k))).re =
      b k * b k * (inner ℂ (multiModeNumberBasis m k) (Θ (multiModeNumberBasis m k))).re := by
    simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, zero_add, sub_zero] using congrArg Complex.re hentry
  have hpow : b k * b k = multiModeThermalWeight q k ^ τ := by
    dsimp [b]
    rw [← Real.rpow_add (multiModeThermalWeight_pos hq₀ hq₁ k), add_halves]
  have hcancel : multiModeThermalWeight q k ^ (-τ) * multiModeThermalWeight q k ^ τ = 1 := by
    rw [← Real.rpow_add (multiModeThermalWeight_pos hq₀ hq₁ k), neg_add_cancel, Real.rpow_zero]
  rw [multiInverseThermalDiagonal, hreal, hpow, ← mul_assoc, hcancel, one_mul]

theorem multiThermal_factorization_traceClass_implies_summable
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hfactor : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) (htrace : IsPositiveTraceClass Θ) :
    Summable (multiInverseThermalDiagonal q τ A) := by
  simpa only [multiThermal_factorization_diagonal hq₀ hq₁ hτ hfactor] using
    htrace.summable_diagonal (multiModeNumberBasis m)

/-- Exact criterion for an actual positive trace-class inverse sandwich,
prior to any Gaussian evaluation of its diagonal sum. -/
theorem exists_positiveTraceClass_multiThermal_factorization_iff
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    (∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (τ / 2)) * Θ *
        (multiModeThermalDensity q ^ (τ / 2)) = A) ↔
      Summable (multiInverseThermalDiagonal q τ A) := by
  constructor
  · rintro ⟨Θ, htrace, hfactor⟩
    exact multiThermal_factorization_traceClass_implies_summable hq₀ hq₁ hτ hfactor htrace
  · intro hsum
    exact ⟨multiThermalSandwichOperator hq₀ hq₁ hA hsum,
      multiThermalSandwichOperator_isPositiveTraceClass hq₀ hq₁ hA hsum,
      multiThermalSandwichOperator_factorization hq₀ hq₁ hτ hA hsum⟩

end VacuumBellSeparation.Gaussian

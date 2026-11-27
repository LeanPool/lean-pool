/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeightedSandwich
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModePowerDomains

/-!
# Actual noncommuting sandwiches with a faithful thermal reference

An arbitrary positive bounded operator A is sandwiched by inverse powers
of the actual faithful product thermal density. Summability of its exact
weighted diagonal constructs the positive trace-class extension, proves
the actual density factorization, and identifies it with the inverse-power
quadratic form on the actual dense range domain. Uniqueness follows from
injectivity and dense range.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}

/-- Multi inverse thermal scale defined as `multiModeThermalWeight q k ^ (-(τ / 2))`. -/
def multiInverseThermalScale (q : Fin m → ℝ) (τ : ℝ) (k : Fin m → ℕ) : ℝ :=
  multiModeThermalWeight q k ^ (-(τ / 2))

/-- Multi inverse thermal diagonal. -/
def multiInverseThermalDiagonal (q : Fin m → ℝ) (τ : ℝ)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (k : Fin m → ℕ) : ℝ :=
  multiModeThermalWeight q k ^ (-τ) *
    (inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k))).re

theorem multiInverseThermalScale_sq (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (τ : ℝ) (k : Fin m → ℕ) :
    multiInverseThermalScale q τ k ^ 2 = multiModeThermalWeight q k ^ (-τ) := by
  rw [multiInverseThermalScale, pow_two, ← Real.rpow_add (multiModeThermalWeight_pos hq₀ hq₁ k)]
  congr 1
  ring

theorem weightedSandwichDiagonal_multiInverseThermalScale
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (τ : ℝ)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    weightedSandwichDiagonal A (multiInverseThermalScale q τ) = multiInverseThermalDiagonal q τ
      A := by
  funext k
  rw [weightedSandwichDiagonal, multiInverseThermalScale_sq hq₀ hq₁]
  rfl

/-- Continuous linear map for the multi thermal sandwich operator, of type
`MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m`. -/
def multiThermalSandwichOperator (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (hsum : Summable (multiInverseThermalDiagonal q τ A)) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  weightedSandwichOperator hA (multiInverseThermalScale q τ)
    (by rwa [weightedSandwichDiagonal_multiInverseThermalScale hq₀ hq₁])

theorem multiThermalSandwichOperator_isPositiveTraceClass
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (hsum : Summable (multiInverseThermalDiagonal q τ A)) :
    IsPositiveTraceClass (multiThermalSandwichOperator hq₀ hq₁ hA hsum) :=
  weightedSandwichOperator_isPositiveTraceClass _ _ _

theorem positiveTrace_multiThermalSandwichOperator
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (hsum : Summable (multiInverseThermalDiagonal q τ A)) :
    positiveTrace (multiThermalSandwichOperator hq₀ hq₁ hA hsum) =
      ENNReal.ofReal (∑' k, multiInverseThermalDiagonal q τ A k) := by
  rw [multiThermalSandwichOperator, positiveTrace_weightedSandwichOperator,
    weightedSandwichDiagonal_multiInverseThermalScale hq₀ hq₁]

theorem multiThermalSandwichOperator_factorization
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (hsum : Summable (multiInverseThermalDiagonal q τ A)) :
    (multiModeThermalDensity q ^ (τ / 2)) * multiThermalSandwichOperator hq₀ hq₁ hA hsum *
      (multiModeThermalDensity q ^ (τ / 2)) = A := by
  apply weightedSandwichOperator_factorization hA (multiInverseThermalScale q τ) _
    (multiModeThermalDensity q ^ (τ / 2)) CFC.rpow_nonneg.isSelfAdjoint
    (fun k => multiModeThermalWeight q k ^ (τ / 2))
  · intro k
    exact multiModeThermalDensity_rpow_apply_numberBasis (fun j => (hq₀ j).le) hq₁ (half_pos hτ) k
  · intro k
    rw [multiInverseThermalScale, ← Real.rpow_add (multiModeThermalWeight_pos hq₀ hq₁ k),
      add_neg_cancel, Real.rpow_zero]

/-- Multi thermal sandwich form. -/
def multiThermalSandwichForm (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (x y : multiThermalPowerDomain q (τ / 2)) : ℂ :=
  inner ℂ (multiThermalInversePower hq₀ hq₁ (half_pos hτ) x)
    (A (multiThermalInversePower hq₀ hq₁ (half_pos hτ) y))

/-- Equality on the entire actual inverse-power domain, not only on
finitely supported vectors. -/
theorem multiThermalSandwichForm_eq_inner
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (hsum : Summable (multiInverseThermalDiagonal q τ A))
    (x y : multiThermalPowerDomain q (τ / 2)) :
    multiThermalSandwichForm hq₀ hq₁ hτ A x y =
      inner ℂ (x : MultiModeOscillatorSpace m)
        (multiThermalSandwichOperator hq₀ hq₁ hA hsum (y : MultiModeOscillatorSpace m)) := by
  let S := multiModeThermalDensity q ^ (τ / 2)
  let Θ := multiThermalSandwichOperator hq₀ hq₁ hA hsum
  let u := multiThermalInversePower hq₀ hq₁ (half_pos hτ) x
  let v := multiThermalInversePower hq₀ hq₁ (half_pos hτ) y
  have hS : IsSelfAdjoint S := CFC.rpow_nonneg.isSelfAdjoint
  have hx : S u = (x : MultiModeOscillatorSpace m) :=
    multiThermalPower_apply_inversePower hq₀ hq₁ (half_pos hτ) x
  have hy : S v = (y : MultiModeOscillatorSpace m) :=
    multiThermalPower_apply_inversePower hq₀ hq₁ (half_pos hτ) y
  change inner ℂ u (A v) = _
  calc
    _ = inner ℂ u (S (Θ (S v))) := by
      rw [← multiThermalSandwichOperator_factorization hq₀ hq₁ hτ hA hsum]
      rfl
    _ = inner ℂ (S u) (Θ (S v)) := by
      simpa only [hS.adjoint_eq] using S.adjoint_inner_right u (Θ (S v))
    _ = _ := by rw [hx, hy]

theorem multiThermalSandwichOperator_unique
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (hsum : Summable (multiInverseThermalDiagonal q τ A))
    {Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) :
    Θ = multiThermalSandwichOperator hq₀ hq₁ hA hsum := by
  let S := multiModeThermalDensity q ^ (τ / 2)
  have hS : Function.Injective S := multiModeThermalDensity_rpow_injective hq₀ hq₁ (half_pos hτ)
  have heq : S * Θ * S = S * multiThermalSandwichOperator hq₀ hq₁ hA hsum * S :=
    hΘ.trans (multiThermalSandwichOperator_factorization hq₀ hq₁ hτ hA hsum).symm
  have hcomp : (fun z => Θ (S z)) = fun z => multiThermalSandwichOperator hq₀ hq₁ hA hsum
    (S z) := by
    funext z
    apply hS
    simpa only [mul_apply_eq_comp] using DFunLike.congr_fun heq z
  have hfun := (multiModeThermalDensity_rpow_denseRange hq₀ hq₁ (half_pos hτ)).equalizer
    Θ.continuous (multiThermalSandwichOperator hq₀ hq₁ hA hsum).continuous hcomp
  exact DFunLike.coe_injective hfun

end VacuumBellSeparation.Gaussian

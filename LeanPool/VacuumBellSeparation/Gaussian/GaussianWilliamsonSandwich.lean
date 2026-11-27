/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WilliamsonSandwichCovarianceDefs
public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalGaussianTransport
public import LeanPool.VacuumBellSeparation.Gaussian.UnitarySandwich
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianAppendixA

/-!
# Actual Appendix A sandwiches for a general faithful Gaussian reference

The reference is the constructed physical Williamson density on the
original oscillator space. A common actual unitary transports both input
and reference, so noncommuting covariance matrices are retained. The
strict gap and determinant are expressed in the manuscript's Williamson
coordinates; the normalized output covariance is transported back.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ}

theorem physicalWilliamsonDensity_isFaithfulDensity
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 < ν j) :
    IsFaithfulDensity (physicalWilliamsonDensity S hS ν) :=
  matrixDensityPullback_isFaithfulDensity _ _ (covarianceProductDensity_isFaithfulDensity hν)

theorem gaussianPhysical_eq_physicalDensityPullback
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hB : IsPositiveTraceClass B)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hGA : HasGaussianPhysicalCharacteristic A (S * V * Sᵀ))
    (hGB : HasGaussianPhysicalCharacteristic B V) :
    A = physicalDensityPullback S hS B :=
  gaussianPhysical_density_unique hA (physicalDensityPullback_isPositiveTraceClass S hS hB)
    hGA (physicalDensityPullback_hasGaussianPhysicalCharacteristic S hS hB hGB)

theorem gaussian_physical_pullback_sandwich_iff
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 < ν j) {τ : ℝ} (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) :
    HasPositiveTraceClassSandwich (physicalWilliamsonDensity S hS ν)
      (physicalDensityPullback S hS A) τ ↔
      (modeDiagonal (fun j => poweredModeVariance τ (ν j)) - V).PosDef := by
  rw [← physicalDensityPullback_covarianceProductDensity S hS (fun j => (hν j).le)]
  change HasPositiveTraceClassSandwich
    ((physicalCongruenceUnitary S hS).symm.conjStarAlgEquiv (covarianceProductDensity ν))
    ((physicalCongruenceUnitary S hS).symm.conjStarAlgEquiv A) τ ↔ _
  rw [hasPositiveTraceClassSandwich_conjStarAlgEquiv_iff _
    (covarianceProductDensity_nonneg (fun j => (hν j).le)) hτ.le]
  exact exists_gaussian_positiveTraceClass_sandwich_iff
    (fun j => covarianceThermalParameter_pos (hν j))
    (fun j => covarianceThermalParameter_lt_one (hν j).le) hτ hA hG hC

/-- The source formulas in Williamson coordinates, realized by actual
operators and then transported to the original canonical Weyl family. -/
theorem gaussian_physical_pullback_sandwich_appendixA
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 < ν j) {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => poweredModeVariance τ (ν j)) - V).PosDef) :
    ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (physicalWilliamsonDensity S hS ν ^ (τ / 2)) * Θ *
        (physicalWilliamsonDensity S hS ν ^ (τ / 2)) = physicalDensityPullback S hS A ∧
      positiveTrace (normalizedPositiveDensity Θ) = 1 ∧
      HasGaussianPhysicalCharacteristic (normalizedPositiveDensity Θ)
        (S * williamsonSandwichCovariance (fun j => covarianceThermalParameter (ν j)) τ V * Sᵀ) ∧
      (positiveTrace Θ).toReal =
        (positiveTrace (physicalWilliamsonDensity S hS ν ^ (1 - τ))).toReal /
          Real.sqrt (1 - gaussianRelativePerturbation
            (fun j => covarianceThermalParameter (ν j)) τ V).det := by
  let q : Fin m → ℝ := fun j => covarianceThermalParameter (ν j)
  have hq₀ : ∀ j, 0 < q j := fun j => covarianceThermalParameter_pos (hν j)
  have hq₁ : ∀ j, q j < 1 := fun j => covarianceThermalParameter_lt_one (hν j).le
  obtain ⟨Θ₀, htc, hf, hn, hg, ht⟩ :=
    gaussian_sandwich_appendixA hq₀ hq₁ hτ₀ hτ₁ hA hG hC hgap
  let e := (physicalCongruenceUnitary S hS).symm
  have href : physicalWilliamsonDensity S hS ν = e.conjStarAlgEquiv (multiModeThermalDensity q) :=
    (physicalDensityPullback_covarianceProductDensity S hS (fun j => (hν j).le)).symm
  have hσ : 0 ≤ multiModeThermalDensity q := multiModeThermalDensity_nonneg (fun j =>
    (hq₀ j).le) hq₁
  have hnorm : normalizedPositiveDensity (e.conjStarAlgEquiv Θ₀) =
      e.conjStarAlgEquiv (normalizedPositiveDensity Θ₀) :=
    normalizedPositiveDensity_conjStarAlgEquiv e htc.1
  have hntc := normalizedPositiveDensity_isPositiveTraceClass (multiModeNumberBasis m) htc
  refine ⟨e.conjStarAlgEquiv Θ₀, IsPositiveTraceClass.conjStarAlgEquiv e htc, ?_, ?_, ?_, ?_⟩
  · rw [href]
    exact (conjStarAlgEquiv_sandwich
      (E := MultiModeOscillatorSpace m) (F := MultiModeOscillatorSpace m)
      e (σ := multiModeThermalDensity q) hσ (τ := τ) hτ₀.le Θ₀).symm.trans
        (congrArg e.conjStarAlgEquiv hf)
  · rw [hnorm, positiveTrace_conjStarAlgEquiv e hntc.1, hn]
  · rw [hnorm]
    exact physicalDensityPullback_hasGaussianPhysicalCharacteristic S hS hntc hg
  · rw [positiveTrace_conjStarAlgEquiv e htc.1, href]
    have hp : positiveTrace ((e.conjStarAlgEquiv (multiModeThermalDensity q)) ^ (1 - τ)) =
        positiveTrace (multiModeThermalDensity q ^ (1 - τ)) :=
      positiveTrace_conjStarAlgEquiv_rpow
        (E := MultiModeOscillatorSpace m) (F := MultiModeOscillatorSpace m)
        e (A := multiModeThermalDensity q) hσ (τ := 1 - τ) (sub_nonneg.mpr hτ₁.le)
    rw [hp]
    exact ht

end VacuumBellSeparation.Gaussian

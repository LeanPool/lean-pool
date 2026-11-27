/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteObservableCoordinates

/-!
# Faithful Gaussian observable model from the physical source assumptions

This endpoint chooses the actual canonical basis, density, cyclic unitary
and a genuine spectral coordinate. The resulting map acts on every bounded
physical observable, preserves effects and norm bounds, is multiplicative
on the actual finite canonical algebra, and agrees with all its vacuum
expectations. No model-equivalence or extraction premise remains.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped InnerProductSpace

theorem operatorEigenIndex_nonempty_of_faithfulDensity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : H →L[ℂ] H} (hρ : IsFaithfulDensity ρ) : Nonempty (operatorEigenIndex ρ) := by
  classical
  by_contra hn
  have : IsEmpty (operatorEigenIndex ρ) := not_nonempty_iff.mp hn
  have hz : faithfulDensityPurification hρ = 0 := by
    ext i
    exact isEmptyElim i
  have hnorm := faithfulDensityPurification_norm hρ
  simp only [hz, norm_zero, zero_ne_one] at hnorm

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  [FiniteDimensional ℝ S] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H)

/-- Every bounded localized finite canonical source algebra has an actual
faithful oscillator density model of all its observables and products. -/
theorem exists_finite_physical_gaussian_observable_model
    {U₀ : Set (EuclideanSpace ℝ (Fin 3))} (hSU : S ≤ localizedTimeZeroSources U₀)
    (hU₀ : Bornology.IsBounded U₀)
    (hnd : ∀ u ∈ S, (∀ v ∈ S, timeZeroSymplectic u v = 0) → u = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
      (ρ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n)
      (T : (H →L[ℂ] H) → (MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n)),
      IsFaithfulDensity ρ ∧
      finiteSourceSymplecticMatrix hm S b = modeSymplecticForm ∧
      HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hm S b) ∧
      T 1 = 1 ∧
      (∀ A, T (star A) = star (T A)) ∧
      (∀ z, T (finitePhysicalWeyl hm S b V z) = physicalOscillatorWeyl z) ∧
      (∀ R : Set (Fin n × Fin 2 → ℝ), ∀ A ∈ generatedVNA (finitePhysicalWeyl hm S b V '' R),
        T A ∈ generatedVNA (physicalOscillatorWeyl '' R)) ∧
      (∀ A, 0 ≤ A → 0 ≤ T A) ∧
      (∀ A, A ≤ 1 → T A ≤ 1) ∧
      (∀ A, ‖T A‖ ≤ ‖A‖) ∧
      (∀ A ∈ canonicalSourceAlgebra V hm S, ∀ B ∈ canonicalSourceAlgebra V hm S,
        T (A * B) = T A * T B) ∧
      (∀ A ∈ canonicalSourceAlgebra V hm S,
        ⟪V.vacuum, A V.vacuum⟫_ℂ = densityExpectation (multiModeNumberBasis n) ρ (T A)) := by
  classical
  obtain ⟨n, b, ρ, hρ, hσ, hG, U, hUv, hUw⟩ :=
    exists_finite_physical_gaussian_cyclic_model hm S V hSU hU₀ hnd
  obtain ⟨k⟩ := operatorEigenIndex_nonempty_of_faithfulDensity hρ
  refine ⟨n, b, ρ, finiteOscillatorObservable hm S b V U k, hρ, hσ, hG,
    finiteOscillatorObservable_one hm S b V U k,
    finiteOscillatorObservable_star hm S b V U k,
    finiteOscillatorObservable_weyl hm S b V U k hσ hUw,
    fun R A hA => finiteOscillatorObservable_mem_coordinateAlgebra hm S b V U k hσ hUw R hA,
    fun A hA => finiteOscillatorObservable_nonneg hm S b V U k hA,
    fun A hA => finiteOscillatorObservable_le_one hm S b V U k hA,
    norm_finiteOscillatorObservable_le hm S b V U k, ?_, ?_⟩
  · intro A hA B hB
    exact finiteOscillatorObservable_mul hm S b V U k hσ hUw hA hB
  · intro A hA
    exact vacuum_finiteOscillatorObservable hm S b V U k hσ hUw hρ hUv hA

end VacuumBellSeparation

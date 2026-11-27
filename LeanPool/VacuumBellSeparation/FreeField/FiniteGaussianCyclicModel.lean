/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteWeylCyclicity
public import LeanPool.VacuumBellSeparation.Bell.PhysicalPurification
public import LeanPool.VacuumBellSeparation.Gaussian.FixedGaussianExistence
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumModePositivity

/-!
# Actual faithful Gaussian model of each finite physical cyclic subsystem

The source covariance and commutation operator construct a real canonical
basis. Bounded localization proves strict uncertainty. The constructed
faithful oscillator density has the literal source covariance, and the
proved purified cyclicity gives an actual unitary from the original
physical closed vacuum orbit. Neither a representation equivalence nor a
Gaussian density is assumed. The ambient multiplicity theorem and transfer
of arbitrary effects are separate from this cyclic identification.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap
open scoped Matrix

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  [FiniteDimensional ℝ S] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H)

instance finitePhysicalCyclicModelComplete {n : ℕ}
    (b : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S)) :
    CompleteSpace (finitePhysicalCyclicSpace hm S b V) := by
  unfold finitePhysicalCyclicSpace closedCyclicSpan
  infer_instance

/-- The finite physical subsystem has an actual faithful Gaussian cyclic
model, with literal covariance, symplectic sign, vacuum and generators. -/
theorem exists_finite_physical_gaussian_cyclic_model
    {U₀ : Set (EuclideanSpace ℝ (Fin 3))} (hSU : S ≤ localizedTimeZeroSources U₀)
    (hU₀ : Bornology.IsBounded U₀)
    (hnd : ∀ u ∈ S, (∀ v ∈ S, timeZeroSymplectic u v = 0) → u = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
      (ρ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n)
      (hρ : IsFaithfulDensity ρ),
      finiteSourceSymplecticMatrix hm S b = modeSymplecticForm ∧
      HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hm S b) ∧
      ∃ U : finitePhysicalCyclicSpace hm S b V ≃ₗᵢ[ℂ]
          lp (fun _ : operatorEigenIndex ρ => MultiModeOscillatorSpace n) 2,
        U (finitePhysicalCyclicVacuum hm S b V) = faithfulDensityPurification hρ ∧
        ∀ z, U.conjStarAlgEquiv
          (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ
            (finitePhysicalWeyl hm S b V z)) =
              hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl z) := by
  obtain ⟨n, ν, e, hν, he⟩ := finiteSource_exists_skew_basis hm S hnd
  let b := finiteSourceCanonicalBasis hm S ν hν e
  have hσ : finiteSourceSymplecticMatrix hm S b = modeSymplecticForm := by
    ext i j
    exact finiteSourceCanonicalBasis_symplectic hm S ν hν e he i j
  have hcov : finiteSourceCovarianceMatrix hm S b = modeDiagonal (fun i => (ν i)⁻¹) := by
    ext i j
    exact finiteSourceCanonicalBasis_covariance hm S ν hν e i j
  have hv (i : Fin n) : (1 / 2 : ℝ) < (ν i)⁻¹ :=
    reciprocal_finiteSource_frequency_gt_half (hν i)
      (finiteSource_skew_frequency_lt_two hm S hSU hU₀ ν e he i)
  obtain ⟨ρ, hρ, hG⟩ := exists_fixed_faithful_gaussian_physical_density
    (modeDiagonal (fun i => (ν i)⁻¹))
    (modeDiagonal_posDef (fun i => inv_pos.mpr (hν i))) (quantum_mode_posDef hv)
  have hG' : HasGaussianPhysicalCharacteristic ρ (finiteSourceCovarianceMatrix hm S b) := by
    rw [hcov]
    exact hG
  have hmultiply (x y : Fin n × Fin 2 → ℝ) :
      finitePhysicalWeyl hm S b V x * finitePhysicalWeyl hm S b V y =
        Complex.exp (-(Complex.I * ((x ⬝ᵥ (modeSymplecticForm *ᵥ y) / 2 : ℝ) : ℂ))) •
          finitePhysicalWeyl hm S b V (x + y) := by
    rw [finitePhysicalWeyl_mul, hσ]
  obtain ⟨U, hUv, hUw⟩ := exists_physical_gaussian_cyclic_unitary hρ
    (finitePhysicalWeyl hm S b V) V.vacuum hmultiply
    (finitePhysicalWeyl_star_of_canonical hm S V b hσ) hG'
    (vacuum_finitePhysicalWeyl hm S b V)
  refine ⟨n, b, ρ, hρ, hσ, hG', U, ?_, ?_⟩
  · have h0 := hUv 0
    have h1 : hilbertAmplification (operatorEigenIndex ρ)
        (1 : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n) = 1 :=
      (hilbertAmplificationHom (operatorEigenIndex ρ)).map_one
    have hv0 : cyclicSpanVector (fun x => finitePhysicalWeyl hm S b V x V.vacuum) 0 =
        finitePhysicalCyclicVacuum hm S b V := by
      apply Subtype.ext
      exact congrArg (fun A : H →L[ℂ] H => A V.vacuum) (finitePhysicalWeyl_zero hm S b V)
    have hw0 : hilbertAmplification (operatorEigenIndex ρ)
        (physicalOscillatorWeyl (0 : Fin n × Fin 2 → ℝ)) = 1 :=
      (congrArg (hilbertAmplification (operatorEigenIndex ρ))
        (physicalOscillatorWeyl_zero n)).trans h1
    refine (congrArg U hv0).symm.trans (h0.trans ?_)
    exact (congrArg (fun A :
      lp (fun _ : operatorEigenIndex ρ => MultiModeOscillatorSpace n) 2 →L[ℂ]
        lp (fun _ : operatorEigenIndex ρ => MultiModeOscillatorSpace n) 2 =>
          A (faithfulDensityPurification hρ)) hw0).trans (one_apply_eq_self _)
  · intro z
    apply ContinuousLinearMap.ext
    intro y
    have h := congrArg (fun A => A (U.symm y)) (hUw z)
    change U ((compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ
      (finitePhysicalWeyl hm S b V z)) (U.symm y)) = _
    change U ((compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ
      (finitePhysicalWeyl hm S b V z)) (U.symm y)) =
        hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl z)
          (U (U.symm y)) at h
    simpa only [LinearIsometryEquiv.apply_symm_apply] using h

end VacuumBellSeparation

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteObservableExtraction

/-!
# Exact generators and regional algebras under physical observable extraction

Extraction preserves one and adjoints and sends each original physical
Weyl generator to the matching physical oscillator generator. Restricting
the generator labels to any subset also preserves membership in the
corresponding actual generated von Neumann algebra.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian

private theorem compression_unitary_compression_star
    {E F G K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ι : E →ₗᵢ[ℂ] F) (U : E ≃ₗᵢ[ℂ] G) (κ : K →ₗᵢ[ℂ] G) (A : F →L[ℂ] F) :
    compression κ (U.conjStarAlgEquiv (compression ι (star A))) =
      star (compression κ (U.conjStarAlgEquiv (compression ι A))) := by
  rw [compression_star, map_star, compression_star]

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  [FiniteDimensional ℝ S] {n : ℕ}
  (b : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H)
  {ρ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n}
  (U : finitePhysicalCyclicSpace hm S b V ≃ₗᵢ[ℂ]
    lp (fun _ : operatorEigenIndex ρ => MultiModeOscillatorSpace n) 2)
  (k : operatorEigenIndex ρ)

omit [FiniteDimensional ℝ S] in
theorem finiteOscillatorObservable_one : finiteOscillatorObservable hm S b V U k 1 = 1 := by
  rw [finiteOscillatorObservable, compression_one, map_one,
    hilbertAmplificationBlock_diagonal_eq_compression, compression_one]

omit [FiniteDimensional ℝ S] in
theorem finiteOscillatorObservable_star (A : H →L[ℂ] H) :
    finiteOscillatorObservable hm S b V U k (star A) =
      star (finiteOscillatorObservable hm S b V U k A) := by
  simp only [finiteOscillatorObservable,
    hilbertAmplificationBlock_diagonal_eq_compression]
  exact compression_unitary_compression_star
    (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ U
    (hilbertCoordinateIsometry (operatorEigenIndex ρ) k) A

variable (hσ : finiteSourceSymplecticMatrix hm S b = modeSymplecticForm)
  (hUw : ∀ z, U.conjStarAlgEquiv
    (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ (finitePhysicalWeyl hm S b V z)) =
      hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl z))

include hσ hUw in
theorem finiteOscillatorObservable_weyl (z : Fin n × Fin 2 → ℝ) :
    finiteOscillatorObservable hm S b V U k (finitePhysicalWeyl hm S b V z) =
      physicalOscillatorWeyl z := by
  have hA : finitePhysicalWeyl hm S b V z ∈ canonicalSourceAlgebra V hm S := by
    rw [← generatedVNA_finitePhysicalWeyl hm S b V]
    exact subset_generatedVNA _ ⟨z, rfl⟩
  apply hilbertAmplification_injective (operatorEigenIndex ρ) k
  exact (finiteObservableTransport_eq_amplification hm S b V U k hσ hUw hA).symm.trans (hUw z)

include hσ hUw in
/-- Arbitrary selected source-coordinate algebras retain their original
label sets after extraction; no regional tensor decomposition is assumed. -/
theorem finiteOscillatorObservable_mem_coordinateAlgebra
    (R : Set (Fin n × Fin 2 → ℝ)) {A : H →L[ℂ] H}
    (hA : A ∈ generatedVNA (finitePhysicalWeyl hm S b V '' R)) :
    finiteOscillatorObservable hm S b V U k A ∈ generatedVNA (physicalOscillatorWeyl '' R) := by
  have hred (B : H →L[ℂ] H) (hB : B ∈ finitePhysicalWeyl hm S b V '' R) :
      (∀ x ∈ finitePhysicalCyclicSpace hm S b V, B x ∈ finitePhysicalCyclicSpace hm S b V) ∧
      (∀ x ∈ finitePhysicalCyclicSpace hm S b V, star B x ∈ finitePhysicalCyclicSpace hm S b V)
        := by
    obtain ⟨z, hz, rfl⟩ := hB
    exact finitePhysicalCyclicSpace_reducing hm S V b hσ _ ⟨z, rfl⟩
  have hc := compression_subtype_mem_generatedVNA (finitePhysicalCyclicSpace hm S b V)
    (finitePhysicalWeyl hm S b V '' R) hred hA
  have ht : U.conjStarAlgEquiv (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ A) ∈
      generatedVNA (hilbertAmplification (operatorEigenIndex ρ) ''
        (physicalOscillatorWeyl '' R)) := by
    apply (mem_generatedVNA_iff_of_starAlgEquiv U.conjStarAlgEquiv (fun T => ?_) _).mp hc
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hUw]
      exact ⟨physicalOscillatorWeyl z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, he⟩
      exact ⟨finitePhysicalWeyl hm S b V z, ⟨z, hz, rfl⟩,
        U.conjStarAlgEquiv.injective ((hUw z).trans he)⟩
  exact hilbertAmplificationBlock_mem_generatedVNA _ _ k ht

end VacuumBellSeparation

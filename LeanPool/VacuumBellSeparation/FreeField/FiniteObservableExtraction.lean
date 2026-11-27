/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteGaussianCyclicModel
public import LeanPool.VacuumBellSeparation.Bell.HilbertAmplificationFaithful
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalFunctionalCalculus

/-!
# Actual oscillator observables for finite physical algebras

The preceding constructed cyclic model supplies the parameters here. The
observable is defined by compression to the literal physical cyclic space,
unitary transport, then one actual coordinate block. Commutant arguments
prove its exact amplified action. Order, norm, products and all vacuum
expectations are preserved in their stated scopes.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian ContinuousLinearMap
open scoped InnerProductSpace

-- Resolve positivity transport over abstract Hilbert spaces before specializing
-- to the nested cyclic-space and oscillator structures.
private theorem unitaryTransport_nonneg
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : E ≃ₗᵢ[ℂ] F) {T : E →L[ℂ] E} (hT : 0 ≤ T) :
    0 ≤ U.conjStarAlgEquiv T := map_nonneg U.conjStarAlgEquiv hT

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  [FiniteDimensional ℝ S] {n : ℕ}
  (b : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (V : FreeFieldVacuum m H)
  {ρ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n}
  (U : finitePhysicalCyclicSpace hm S b V ≃ₗᵢ[ℂ]
    lp (fun _ : operatorEigenIndex ρ => MultiModeOscillatorSpace n) 2)
  (k : operatorEigenIndex ρ)

/-- Continuous linear map for the finite oscillator observable, of type `MultiModeOscillatorSpace n
→L[ℂ] MultiModeOscillatorSpace n`. -/
noncomputable def finiteOscillatorObservable (A : H →L[ℂ] H) :
    MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n :=
  hilbertAmplificationBlock (operatorEigenIndex ρ)
    (U.conjStarAlgEquiv (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ A)) k k

variable (hσ : finiteSourceSymplecticMatrix hm S b = modeSymplecticForm)
  (hUw : ∀ z, U.conjStarAlgEquiv
    (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ (finitePhysicalWeyl hm S b V z)) =
      hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl z))

include hσ hUw in
theorem finiteObservableTransport_mem_amplifiedVNA
    {A : H →L[ℂ] H} (hA : A ∈ canonicalSourceAlgebra V hm S) :
    U.conjStarAlgEquiv (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ A) ∈
      generatedVNA (hilbertAmplification (operatorEigenIndex ρ) ''
        Set.range (physicalOscillatorWeyl (n := n))) := by
  have ha : A ∈ generatedVNA (Set.range (finitePhysicalWeyl hm S b V)) := by
    rw [generatedVNA_finitePhysicalWeyl]
    exact hA
  have hc := compression_subtype_mem_generatedVNA (finitePhysicalCyclicSpace hm S b V)
    (Set.range (finitePhysicalWeyl hm S b V))
    (finitePhysicalCyclicSpace_reducing hm S V b hσ) ha
  apply (mem_generatedVNA_iff_of_starAlgEquiv U.conjStarAlgEquiv (fun T => ?_) _).mp hc
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    rw [hUw]
    exact ⟨physicalOscillatorWeyl z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, hz⟩
    exact ⟨finitePhysicalWeyl hm S b V z, ⟨z, rfl⟩,
      U.conjStarAlgEquiv.injective ((hUw z).trans hz)⟩

include hσ hUw in
theorem finiteObservableTransport_eq_amplification
    {A : H →L[ℂ] H} (hA : A ∈ canonicalSourceAlgebra V hm S) :
    U.conjStarAlgEquiv (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ A) =
      hilbertAmplification (operatorEigenIndex ρ) (finiteOscillatorObservable hm S b V U k A) :=
  eq_hilbertAmplification_of_mem_generatedVNA _ _ k
    (finiteObservableTransport_mem_amplifiedVNA hm S b V U hσ hUw hA)

omit [FiniteDimensional ℝ S] in
theorem finiteOscillatorObservable_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) :
    0 ≤ finiteOscillatorObservable hm S b V U k A :=
  hilbertAmplificationBlock_nonneg _ (unitaryTransport_nonneg U (compression_nonneg _ hA)) k

omit [FiniteDimensional ℝ S] in
theorem finiteOscillatorObservable_le_one {A : H →L[ℂ] H} (hA : A ≤ 1) :
    finiteOscillatorObservable hm S b V U k A ≤ 1 := by
  apply hilbertAmplificationBlock_le_one
  have h := unitaryTransport_nonneg U
    (compression_nonneg (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ (sub_nonneg.mpr hA))
  simpa only [compression_sub, compression_one, map_sub, map_one, sub_nonneg] using h

omit [FiniteDimensional ℝ S] in
theorem norm_finiteOscillatorObservable_le (A : H →L[ℂ] H) :
    ‖finiteOscillatorObservable hm S b V U k A‖ ≤ ‖A‖ :=
  (norm_hilbertAmplificationBlock_le _ _ k).trans
    ((norm_conjStarAlgEquiv_le U _).trans (norm_compression_le _ A))

include hσ hUw in
theorem finiteOscillatorObservable_mul {A B : H →L[ℂ] H}
    (hA : A ∈ canonicalSourceAlgebra V hm S) (hB : B ∈ canonicalSourceAlgebra V hm S) :
    finiteOscillatorObservable hm S b V U k (A * B) =
      finiteOscillatorObservable hm S b V U k A * finiteOscillatorObservable hm S b V U k B := by
  have hAB := (canonicalSourceAlgebra V hm S).mul_mem hA hB
  have hinv (x : finitePhysicalCyclicSpace hm S b V) :
      B ((finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ x) =
        (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ
          (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ B x) := by
    exact (congrArg Subtype.val (compression_subtype_apply _ B
      (fun x hx => canonicalSourceAlgebra_invariant_cyclic hm S V b hσ hB hx) x)).symm
  apply hilbertAmplification_injective (operatorEigenIndex ρ) k
  calc
    _ = U.conjStarAlgEquiv (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ (A * B)) :=
      (finiteObservableTransport_eq_amplification hm S b V U k hσ hUw hAB).symm
    _ = U.conjStarAlgEquiv (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ A) *
        U.conjStarAlgEquiv (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ B) := by
      rw [compression_mul_of_invariant _ A B hinv, map_mul]
    _ = hilbertAmplification (operatorEigenIndex ρ) (finiteOscillatorObservable hm S b V U k A) *
        hilbertAmplification (operatorEigenIndex ρ) (finiteOscillatorObservable hm S b V U k B)
          := by
      rw [finiteObservableTransport_eq_amplification hm S b V U k hσ hUw hA,
        finiteObservableTransport_eq_amplification hm S b V U k hσ hUw hB]
    _ = _ := ((hilbertAmplificationHom (operatorEigenIndex ρ)).map_mul _ _).symm

include hσ hUw in
theorem vacuum_finiteOscillatorObservable (hρ : IsFaithfulDensity ρ)
    (hUv : U (finitePhysicalCyclicVacuum hm S b V) = faithfulDensityPurification hρ)
    {A : H →L[ℂ] H} (hA : A ∈ canonicalSourceAlgebra V hm S) :
    ⟪V.vacuum, A V.vacuum⟫_ℂ =
      densityExpectation (multiModeNumberBasis n) ρ (finiteOscillatorObservable hm S b V U k A)
        := by
  symm
  calc
    _ = densityExpectation (positiveTraceClassEigenbasis hρ.isPositiveTraceClass) ρ
        (finiteOscillatorObservable hm S b V U k A) :=
      densityExpectation_eq _ _ hρ.isPositiveTraceClass _
    _ = ⟪faithfulDensityPurification hρ, hilbertAmplification (operatorEigenIndex ρ)
        (finiteOscillatorObservable hm S b V U k A) (faithfulDensityPurification hρ)⟫_ℂ := rfl
    _ = ⟪U (finitePhysicalCyclicVacuum hm S b V), U
        (compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ A
          (finitePhysicalCyclicVacuum hm S b V))⟫_ℂ := by
      rw [← finiteObservableTransport_eq_amplification hm S b V U k hσ hUw hA, ← hUv]
      simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_apply_apply]
    _ = ⟪finitePhysicalCyclicVacuum hm S b V,
        compression (finitePhysicalCyclicSpace hm S b V).subtypeₗᵢ A
          (finitePhysicalCyclicVacuum hm S b V)⟫_ℂ := U.inner_map_map _ _
    _ = _ := (finitePhysicalCyclicSpace hm S b
      V).subtypeₗᵢ.toContinuousLinearMap.adjoint_inner_right
      (finitePhysicalCyclicVacuum hm S b V) (A V.vacuum)

end VacuumBellSeparation

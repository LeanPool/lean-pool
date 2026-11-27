/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.PhysicalOscillatorCoordinates
public import LeanPool.VacuumBellSeparation.Bell.PurifiedWeylCyclicity
public import LeanPool.VacuumBellSeparation.Bell.ProjectiveCyclicEquivalence

/-!
# Gaussian purification in the physical Weyl coordinates

The full label equivalence transports the proved oscillator purification
cyclicity. Basis independence identifies its vector characteristic with the
literal physical covariance. Matching source projective data then supplies
an actual unitary on the source cyclic subspace and actual intertwining.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Matrix
open scoped InnerProductSpace

variable {n : ℕ}
  {ρ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n}
  (hρ : IsFaithfulDensity ρ)

theorem faithfulDensityPurification_physicalWeyl_cyclic :
    closedCyclicSpan (fun x => hilbertAmplification (operatorEigenIndex ρ)
      (physicalOscillatorWeyl x) (faithfulDensityPurification hρ)) = ⊤ := by
  have hr := (physicalOscillatorLabel n).surjective.range_comp
    (fun z => hilbertAmplification (operatorEigenIndex ρ)
      (multiOscillatorWeyl z) (faithfulDensityPurification hρ))
  unfold closedCyclicSpan
  change (Submodule.span ℂ (Set.range (fun x => hilbertAmplification (operatorEigenIndex ρ)
    (multiOscillatorWeyl (physicalOscillatorLabel n x))
      (faithfulDensityPurification hρ)))).topologicalClosure = ⊤
  simp only [Function.comp_def] at hr
  rw [hr]
  exact faithfulDensityPurification_weyl_cyclic hρ

theorem faithfulDensityPurification_physical_characteristic
    {V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic ρ V) (x : Fin n × Fin 2 → ℝ) :
    ⟪faithfulDensityPurification hρ, hilbertAmplification (operatorEigenIndex ρ)
      (physicalOscillatorWeyl x) (faithfulDensityPurification hρ)⟫_ℂ =
        ((Real.exp (-(x ⬝ᵥ (V *ᵥ x) / 2)) : ℝ) : ℂ) := by
  change densityExpectation (positiveTraceClassEigenbasis hρ.isPositiveTraceClass)
    ρ (physicalOscillatorWeyl x) = _
  rw [densityExpectation_eq _ (multiModeNumberBasis n) hρ.isPositiveTraceClass,
    gaussianPhysical_physicalOscillatorWeyl hG]

theorem amplifiedPhysicalWeyl_mul (x y : Fin n × Fin 2 → ℝ) :
    hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl x) *
      hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl y) =
        Complex.exp (-(Complex.I * ((x ⬝ᵥ (modeSymplecticForm *ᵥ y) / 2 : ℝ) : ℂ))) •
          hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl (x + y)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext i
  have h := congrArg (fun A : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n =>
    A (u i)) (physicalOscillatorWeyl_mul x y)
  simpa only [mul_apply_eq_comp, smul_apply,
    hilbertAmplification_apply, lp.coeFn_smul, Pi.smul_apply] using h

theorem amplifiedPhysicalWeyl_star (x : Fin n × Fin 2 → ℝ) :
    star (hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl x)) =
      hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl (-x)) := by
  rw [← hilbertAmplification_star, physicalOscillatorWeyl_star]

local instance physicalClosedOrbitComplete {Z H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Z → H →L[ℂ] H) (v : H) :
    CompleteSpace (closedCyclicSpan (fun x => W x v)) := by
  unfold closedCyclicSpan
  infer_instance

/-- An actual cyclic representation equivalence for a faithful physical
Gaussian characteristic. Source Weyl relations are explicit and will be
instantiated by the original finite-source operators. -/
theorem exists_physical_gaussian_cyclic_unitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : (Fin n × Fin 2 → ℝ) → H →L[ℂ] H) (v : H)
    (hmul : ∀ x y, W x * W y =
      Complex.exp (-(Complex.I * ((x ⬝ᵥ (modeSymplecticForm *ᵥ y) / 2 : ℝ) : ℂ))) • W (x + y))
    (hstar : ∀ x, star (W x) = W (-x))
    {V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic ρ V)
    (hchar : ∀ x, ⟪v, W x v⟫_ℂ = ((Real.exp (-(x ⬝ᵥ (V *ᵥ x) / 2)) : ℝ) : ℂ)) :
    ∃ U : closedCyclicSpan (fun x => W x v) ≃ₗᵢ[ℂ]
        lp (fun _ : operatorEigenIndex ρ => MultiModeOscillatorSpace n) 2,
      (∀ x, U (cyclicSpanVector (fun x => W x v) x) =
        hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl x)
          (faithfulDensityPurification hρ)) ∧
      (∀ z, U.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (compression (closedCyclicSpan (fun x => W x v)).subtypeₗᵢ (W z)) =
          (hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl z)).comp
            U.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply exists_projective_cyclic_unitary W
    (fun x => hilbertAmplification (operatorEigenIndex ρ) (physicalOscillatorWeyl x)) _
    hmul (amplifiedPhysicalWeyl_mul (ρ := ρ)) hstar (amplifiedPhysicalWeyl_star (ρ := ρ))
    v (faithfulDensityPurification hρ) (faithfulDensityPurification_physicalWeyl_cyclic hρ)
  intro x
  rw [hchar, faithfulDensityPurification_physical_characteristic hρ hG]

end VacuumBellSeparation

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylCoherentRepresentation
public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryTrace
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers

/-!
# Actual one-mode Weyl action and transported thermal density

The constructed unitary transports the existing Weyl operators to ℓ² and
the actual thermal density back to the existing Weyl Hilbert space. The
Weyl relations, coherent action, density normalization and fractional trace
formula follow through that unitary.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem id_add (z w : ℂ) : (id : ℂ → ℂ) (z + w) = id z + id w := rfl

/-- Actual Weyl displacement on the number-basis Hilbert space. -/
noncomputable def oscillatorWeyl (z : ℂ) : OscillatorSpace →L[ℂ] OscillatorSpace :=
  weylCoherentEquiv.conjStarAlgEquiv (weylCLM (id : ℂ → ℂ) id_add z)

theorem oscillatorWeyl_mem_unitary (z : ℂ) :
    oscillatorWeyl z ∈ unitary (OscillatorSpace →L[ℂ] OscillatorSpace) :=
  Unitary.map_mem weylCoherentEquiv.conjStarAlgEquiv
    (weylCLM_mem_unitary (id : ℂ → ℂ) id_add z)

theorem oscillatorWeyl_mul (z w : ℂ) :
    oscillatorWeyl z * oscillatorWeyl w =
      weylPhase (id : ℂ → ℂ) z w • oscillatorWeyl (z + w) := by
  unfold oscillatorWeyl
  rw [← map_mul, weylCLM_mul]
  exact weylCoherentEquiv.conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.map_smul _ _

theorem oscillatorWeyl_coherentVector (z w : ℂ) :
    oscillatorWeyl z (coherentVector w) =
      weylPhase (id : ℂ → ℂ) z w • coherentVector (z + w) := by
  rw [oscillatorWeyl, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    ← weylCoherentEquiv_weylVec w, weylCoherentEquiv.symm_apply_apply,
    weylCLM_apply, weylOp_weylVec, map_smul, weylCoherentEquiv_weylVec]

theorem norm_coherentVector_zero : ‖coherentVector 0‖ = 1 := by
  rw [← weylCoherentEquiv_weylVec 0, weylCoherentEquiv.norm_map]
  exact norm_weylVec_zero (id : ℂ → ℂ) id_add

theorem oscillatorWeyl_vacuum (z : ℂ) :
    inner ℂ (coherentVector 0) (oscillatorWeyl z (coherentVector 0)) =
      ((Real.exp (-(‖z‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [oscillatorWeyl_coherentVector, weylPhase_zero_right (id : ℂ → ℂ) id_add,
    one_smul, add_zero, ← weylCoherentEquiv_weylVec 0,
    ← weylCoherentEquiv_weylVec z, weylCoherentEquiv.inner_map_map]
  exact inner_weylVec_zero_left (id : ℂ → ℂ) id_add z

/-- The actual thermal density on the existing one-mode Weyl Hilbert space. -/
noncomputable def weylThermalDensity (q : ℝ) :
    WeylSpace (id : ℂ → ℂ) →L[ℂ] WeylSpace (id : ℂ → ℂ) :=
  weylCoherentEquiv.symm.conjStarAlgEquiv (thermalDensity q)

theorem weylThermalDensity_isFaithfulDensity {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    IsFaithfulDensity (weylThermalDensity q) :=
  IsFaithfulDensity.conjStarAlgEquiv weylCoherentEquiv.symm
    (thermalDensity_isFaithfulDensity hq₀ hq₁)

theorem positiveTrace_weylThermalDensity {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    positiveTrace (weylThermalDensity q) = 1 := by
  rw [weylThermalDensity,
    positiveTrace_conjStarAlgEquiv weylCoherentEquiv.symm (thermalDensity_nonneg hq₀ hq₁),
    positiveTrace_thermalDensity hq₀ hq₁]

theorem positiveTrace_weylThermalDensity_rpow {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    positiveTrace (weylThermalDensity q ^ τ) =
      ENNReal.ofReal ((1 - q) ^ τ / (1 - q ^ τ)) := by
  rw [weylThermalDensity,
    positiveTrace_conjStarAlgEquiv_rpow weylCoherentEquiv.symm
      (thermalDensity_nonneg hq₀ hq₁) hτ.le]
  exact positiveTrace_thermalDensity_rpow hq₀ hq₁ hτ

end VacuumBellSeparation.Gaussian

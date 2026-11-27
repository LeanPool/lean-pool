/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeWeylRepresentation
public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryTrace

/-!
# Actual finite-mode Weyl action and transported thermal density

The constructed unitary realizes the existing Weyl action on the full
occupation Hilbert space. Actual product densities and their CFC powers
transport back to the existing Weyl representation with their trace and
faithfulness properties.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem multi_id_add {m : ℕ} (z w : MultiModePhaseSpace m) :
    (id : MultiModePhaseSpace m → MultiModePhaseSpace m) (z + w) = id z + id w := rfl

/-- Continuous linear map for the multi oscillator Weyl, of type `MultiModeOscillatorSpace m →L[ℂ]
MultiModeOscillatorSpace m`. -/
noncomputable def multiOscillatorWeyl {m : ℕ} (z : MultiModePhaseSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  (multiWeylCoherentEquiv m).conjStarAlgEquiv
    (weylCLM (id : MultiModePhaseSpace m → MultiModePhaseSpace m) multi_id_add z)

theorem multiOscillatorWeyl_mem_unitary {m : ℕ} (z : MultiModePhaseSpace m) :
    multiOscillatorWeyl z ∈ unitary (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  Unitary.map_mem
    (R := WeylSpace (id : MultiModePhaseSpace m → MultiModePhaseSpace m) →L[ℂ]
      WeylSpace (id : MultiModePhaseSpace m → MultiModePhaseSpace m))
    (S := MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (multiWeylCoherentEquiv m).conjStarAlgEquiv.toStarAlgHom
    (weylCLM_mem_unitary (id : MultiModePhaseSpace m → MultiModePhaseSpace m) multi_id_add z)

theorem multiOscillatorWeyl_mul {m : ℕ} (z w : MultiModePhaseSpace m) :
    multiOscillatorWeyl z * multiOscillatorWeyl w =
      weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z w •
        multiOscillatorWeyl (z + w) := by
  unfold multiOscillatorWeyl
  rw [← map_mul, weylCLM_mul]
  exact (multiWeylCoherentEquiv m).conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.map_smul _ _

theorem multiOscillatorWeyl_coherentVector {m : ℕ} (z w : MultiModePhaseSpace m) :
    multiOscillatorWeyl z (multiCoherentVector w) =
      weylPhase (id : MultiModePhaseSpace m → MultiModePhaseSpace m) z w •
        multiCoherentVector (z + w) := by
  rw [multiOscillatorWeyl, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    ← multiWeylCoherentEquiv_weylVec w, (multiWeylCoherentEquiv m).symm_apply_apply,
    weylCLM_apply, weylOp_weylVec, map_smul, multiWeylCoherentEquiv_weylVec]

theorem multiOscillatorWeyl_vacuum {m : ℕ} (z : MultiModePhaseSpace m) :
    inner ℂ (multiCoherentVector (0 : MultiModePhaseSpace m))
      (multiOscillatorWeyl z (multiCoherentVector 0)) =
      ((Real.exp (-(‖z‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  rw [multiOscillatorWeyl_coherentVector,
    weylPhase_zero_right (id : MultiModePhaseSpace m → MultiModePhaseSpace m) multi_id_add,
    one_smul, add_zero, ← multiWeylCoherentEquiv_weylVec (0 : MultiModePhaseSpace m),
    ← multiWeylCoherentEquiv_weylVec z, (multiWeylCoherentEquiv m).inner_map_map]
  exact inner_weylVec_zero_left (id : MultiModePhaseSpace m → MultiModePhaseSpace m) multi_id_add z

/-- Multi Weyl thermal density. -/
noncomputable def multiWeylThermalDensity {m : ℕ} (q : Fin m → ℝ) :
    WeylSpace (id : MultiModePhaseSpace m → MultiModePhaseSpace m) →L[ℂ]
      WeylSpace (id : MultiModePhaseSpace m → MultiModePhaseSpace m) :=
  (multiWeylCoherentEquiv m).symm.conjStarAlgEquiv (multiModeThermalDensity q)

theorem multiWeylThermalDensity_isFaithfulDensity {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) :
    IsFaithfulDensity (multiWeylThermalDensity q) :=
  IsFaithfulDensity.conjStarAlgEquiv (multiWeylCoherentEquiv m).symm
    (multiModeThermalDensity_isFaithfulDensity hq₀ hq₁)

theorem positiveTrace_multiWeylThermalDensity {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    positiveTrace (multiWeylThermalDensity q) = 1 := by
  rw [multiWeylThermalDensity,
    positiveTrace_conjStarAlgEquiv (multiWeylCoherentEquiv m).symm
      (multiModeThermalDensity_nonneg hq₀ hq₁),
    positiveTrace_multiModeThermalDensity hq₀ hq₁]

theorem positiveTrace_multiWeylThermalDensity_rpow {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    positiveTrace (multiWeylThermalDensity q ^ τ) =
      ENNReal.ofReal (∏ j, (1 - q j) ^ τ / (1 - q j ^ τ)) := by
  rw [multiWeylThermalDensity,
    positiveTrace_conjStarAlgEquiv_rpow (multiWeylCoherentEquiv m).symm
      (multiModeThermalDensity_nonneg hq₀ hq₁) hτ.le]
  exact positiveTrace_multiModeThermalDensity_rpow hq₀ hq₁ hτ

end VacuumBellSeparation.Gaussian

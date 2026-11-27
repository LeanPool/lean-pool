/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylIrreducibility
public import LeanPool.VacuumBellSeparation.FreeField.Isotony
public import LeanPool.VacuumBellSeparation.Bell.AmbientWeakStarBellSequence

/-!
# The actual oscillator Weyl commutant

Commutation with every Weyl operator implies commutation with the genuine
Gaussian vector integral, hence with the vacuum rank-one projection.
The vacuum is therefore an eigenvector; its total coherent orbit forces
the operator to be scalar. The actual Weyl double commutant is all bounded
operators. This concerns the constructed oscillator representation only.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

variable {n : ℕ}

theorem commutes_weylVacuumIntegral
    (A : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n)
    (hA : ∀ z : MultiModePhaseSpace n, A * multiOscillatorWeyl z = multiOscillatorWeyl z * A) :
    A * weylVacuumIntegral n = weylVacuumIntegral n * A := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, weylVacuumIntegral_apply]
  rw [← A.integral_comp_comm (integrable_weylVacuumOrbit x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change A (weylVacuumWeight n z • multiOscillatorWeyl (WithLp.toLp 2 z) x) =
      weylVacuumWeight n z • multiOscillatorWeyl (WithLp.toLp 2 z) (A x)
    rw [map_smul]
    congr 1
    exact congrArg (fun T => T x) (hA (WithLp.toLp 2 z))

/-- The actual canonical oscillator Weyl commutant consists of scalar operators. -/
theorem oscillatorWeyl_commutant_scalar
    (A : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n)
    (hA : ∀ z : MultiModePhaseSpace n, A * multiOscillatorWeyl z = multiOscillatorWeyl z * A) :
    ∃ c : ℂ, A = c • 1 := by
  let v := multiExponentialVector (0 : Fin n → ℂ)
  have hv : ⟪v, v⟫_ℂ = 1 := by
    dsimp only [v]
    rw [inner_multiExponentialVector]
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, Complex.exp_zero]
  have hp : (Real.pi : ℂ) ^ n ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hP := commutes_weylVacuumIntegral A hA
  rw [weylVacuumIntegral_eq_rankOne] at hP
  have hP' := congrArg (fun T : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n =>
    ((Real.pi : ℂ) ^ n)⁻¹ • T) hP
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hp, one_smul] at hP'
  have hAv : A v = ⟪v, A v⟫_ℂ • v := by
    have he := congrArg
      (fun T : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n => T v) hP'
    change A (⟪v, v⟫_ℂ • v) = ⟪v, A v⟫_ℂ • v at he
    simpa only [hv, one_smul] using he
  refine ⟨⟪v, A v⟫_ℂ, ?_⟩
  apply continuousLinearMap_eq_of_dense_span (multiCoherentVector (m := n))
    (multiCoherentVector_dense_span n)
  intro z
  rw [← multiOscillatorWeyl_exponential_zero z]
  change A (multiOscillatorWeyl z v) = ⟪v, A v⟫_ℂ • multiOscillatorWeyl z v
  calc
    A (multiOscillatorWeyl z v) = multiOscillatorWeyl z (A v) := by
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n => T v) (hA z)
    _ = multiOscillatorWeyl z (⟪v, A v⟫_ℂ • v) := congrArg (multiOscillatorWeyl z) hAv
    _ = ⟪v, A v⟫_ℂ • multiOscillatorWeyl z v := map_smul _ _ _

/-- The genuine canonical Weyl family generates every bounded oscillator operator. -/
theorem generatedVNA_oscillatorWeyl_eq_top (n : ℕ) :
    generatedVNA (Set.range (multiOscillatorWeyl (m := n))) =
      Bipartite.fullOperatorAlgebra (MultiModeOscillatorSpace n) := by
  apply SetLike.ext
  intro T
  constructor
  · intro _
    trivial
  intro _
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro A hA
  have hc : ∀ z : MultiModePhaseSpace n,
      A * multiOscillatorWeyl z = multiOscillatorWeyl z * A := by
    intro z
    exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hA) _ ⟨z, rfl⟩).1.symm
  obtain ⟨c, rfl⟩ := oscillatorWeyl_commutant_scalar A hc
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end VacuumBellSeparation

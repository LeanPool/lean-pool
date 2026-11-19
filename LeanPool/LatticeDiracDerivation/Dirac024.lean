/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac024.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac023

/-!
# DIRAC-024: projective zitter cycle and the cubical spinor sign

DIRAC-017 derives the spatial spinor law from the cube incidence algebra:
a `2*pi` rotation multiplies every amplitude by `-1`, while `4*pi` returns it.
DIRAC-021/022 independently derive the coherent positive/negative-energy
beat and its zitterbewegung observable from the action-selected rest frequency.

This stage proves their exact projective relation.  After one complete
observable zitter period, the density, current and position have returned,
but the coherent four-component state has acquired a common minus sign.
After two periods the state itself returns.  On either native cube copy,
one zitter period therefore has exactly the same endpoint action as a `2*pi`
cube rotation, and two periods have the same endpoint action as `4*pi`.

The theorem does not identify time evolution with spatial rotation.  It
retains their independently derived generators and proves that the rest
Hamiltonian distinguishes the two energy branches while the selected spatial
spin generator acts equally on them.  What coincides is the projective cycle,
not the generator.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-- The oscillation period `2 * π / nativeZitterAngularFrequency`. -/
def nativeZitterPeriod : ℝ :=
  2 * Real.pi / nativeZitterAngularFrequency

/-- Half of the oscillation period `nativeZitterPeriod`. -/
def nativeZitterHalfPeriod : ℝ :=
  nativeZitterPeriod / 2

theorem native_zitter_period_eq_branch_beat_period :
    nativeZitterPeriod = nativeBranchBeatPeriod := by
  rw [nativeZitterPeriod, nativeZitterAngularFrequency,
    nativeBranchBeatAngularFrequency, nativeBranchBeatPeriod]
  have hfrequency : nativeRestAngularFrequency ≠ 0 := by
    rw [native_rest_angular_frequency_eq_nineteen]
    norm_num
  field_simp [hfrequency]

theorem rest_frequency_times_zitter_period :
    nativeRestAngularFrequency * nativeZitterPeriod = Real.pi := by
  rw [native_zitter_period_eq_branch_beat_period,
    nativeBranchBeatPeriod]
  have hfrequency : nativeRestAngularFrequency ≠ 0 := by
    rw [native_rest_angular_frequency_eq_nineteen]
    norm_num
  field_simp [hfrequency]

theorem action_mass_times_zitter_period :
    chi0 * nativeZitterPeriod = Real.pi := by
  rw [← continuum_rest_frequency_is_chi0]
  exact rest_frequency_times_zitter_period

theorem coherent_rest_state_one_zitter_cycle
    (time : ℝ) :
    coherentRestState (time + nativeZitterPeriod) =
      fun component => -coherentRestState time component := by
  have hshift :
      chi0 * (time + nativeZitterPeriod) =
        chi0 * time + Real.pi := by
    rw [mul_add, action_mass_times_zitter_period]
  funext component
  fin_cases component <;>
    apply Complex.ext <;>
    simp [coherentRestState, hshift, Real.cos_add, Real.sin_add]

theorem coherent_rest_state_two_zitter_cycles
    (time : ℝ) :
    coherentRestState (time + 2 * nativeZitterPeriod) =
      coherentRestState time := by
  have htime :
      time + 2 * nativeZitterPeriod =
        (time + nativeZitterPeriod) + nativeZitterPeriod := by ring
  rw [htime, coherent_rest_state_one_zitter_cycle,
    coherent_rest_state_one_zitter_cycle]
  funext component
  simp

theorem zitter_velocity_one_cycle_periodic (time : ℝ) :
    restZitterVelocity (time + nativeZitterPeriod) =
      restZitterVelocity time := by
  have hshift :
      2 * chi0 * (time + nativeZitterPeriod) =
        2 * chi0 * time + 2 * Real.pi := by
    rw [mul_add]
    have hperiod := action_mass_times_zitter_period
    nlinarith
  rw [coherent_rest_velocity_cross_term,
    coherent_rest_velocity_cross_term, hshift]
  simp [Real.cos_add]

theorem zitter_position_one_cycle_periodic (time : ℝ) :
    nativeZitterPosition (time + nativeZitterPeriod) =
      nativeZitterPosition time := by
  have hfrequencyPeriod :
      nativeZitterAngularFrequency * nativeZitterPeriod =
        2 * Real.pi := by
    rw [nativeZitterPeriod]
    have hfrequency : nativeZitterAngularFrequency ≠ 0 := by
      rw [native_zitter_angular_frequency_eq_thirty_eight]
      norm_num
    field_simp [hfrequency]
  have hshift :
      nativeZitterAngularFrequency * (time + nativeZitterPeriod) =
        nativeZitterAngularFrequency * time + 2 * Real.pi := by
    rw [mul_add, hfrequencyPeriod]
  rw [nativeZitterPosition, nativeZitterPosition, hshift]
  simp [Real.sin_add]

theorem coherent_density_one_zitter_cycle_periodic (time : ℝ) :
    cell4Density (coherentRestState (time + nativeZitterPeriod)) =
      cell4Density (coherentRestState time) := by
  rw [coherent_rest_state_density_one, coherent_rest_state_density_one]

theorem zitter_velocity_at_zero :
    restZitterVelocity 0 = c19ContinuumSpeed := by
  rw [coherent_rest_velocity_cross_term]
  simp

theorem zitter_velocity_at_half_period :
    restZitterVelocity nativeZitterHalfPeriod =
      -c19ContinuumSpeed := by
  have hhalf :
      2 * chi0 * nativeZitterHalfPeriod = Real.pi := by
    rw [nativeZitterHalfPeriod]
    calc
      2 * chi0 * (nativeZitterPeriod / 2) =
          chi0 * nativeZitterPeriod := by ring
      _ = Real.pi := action_mass_times_zitter_period
  rw [coherent_rest_velocity_cross_term, hhalf]
  simp

theorem half_zitter_period_is_not_a_return :
    restZitterVelocity nativeZitterHalfPeriod ≠ restZitterVelocity 0 := by
  rw [zitter_velocity_at_half_period, zitter_velocity_at_zero]
  have hspeed : 0 < c19ContinuumSpeed := by
    unfold c19ContinuumSpeed
    positivity
  linarith

theorem minus_copy_two_pi_rotation_is_one_zitter_cycle
    (axis : Fin 3) (time : ℝ) :
    cubeContinuousTurn (2 * Real.pi) axis
        (cubeDiracEmbedMinus (coherentRestState time)) =
      cubeDiracEmbedMinus
        (coherentRestState (time + nativeZitterPeriod)) := by
  rw [cube_continuous_turn_two_pi,
    coherent_rest_state_one_zitter_cycle]
  simpa using
    (cube_dirac_embed_minus_scale (-1) (coherentRestState time))

theorem plus_copy_two_pi_rotation_is_one_zitter_cycle
    (axis : Fin 3) (time : ℝ) :
    cubeContinuousTurn (2 * Real.pi) axis
        (cubeDiracEmbedPlus (coherentRestState time)) =
      cubeDiracEmbedPlus
        (coherentRestState (time + nativeZitterPeriod)) := by
  rw [cube_continuous_turn_two_pi,
    coherent_rest_state_one_zitter_cycle]
  simpa using
    (cube_dirac_embed_plus_scale (-1) (coherentRestState time))

theorem minus_copy_four_pi_rotation_is_two_zitter_cycles
    (axis : Fin 3) (time : ℝ) :
    cubeContinuousTurn (4 * Real.pi) axis
        (cubeDiracEmbedMinus (coherentRestState time)) =
      cubeDiracEmbedMinus
        (coherentRestState (time + 2 * nativeZitterPeriod)) := by
  rw [cube_continuous_turn_four_pi,
    coherent_rest_state_two_zitter_cycles]

theorem plus_copy_four_pi_rotation_is_two_zitter_cycles
    (axis : Fin 3) (time : ℝ) :
    cubeContinuousTurn (4 * Real.pi) axis
        (cubeDiracEmbedPlus (coherentRestState time)) =
      cubeDiracEmbedPlus
        (coherentRestState (time + 2 * nativeZitterPeriod)) := by
  rw [cube_continuous_turn_four_pi,
    coherent_rest_state_two_zitter_cycles]

theorem rest_generator_distinguishes_zitter_branches :
    (standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis0 =
        fun component => (chi0 : ℂ) * cell4Basis0 component) ∧
      (standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis2 =
        fun component => -(chi0 : ℂ) * cell4Basis2 component) :=
  ⟨positive_rest_state_has_native_energy,
    negative_rest_state_has_native_energy⟩

theorem spatial_spin0_acts_equally_on_zitter_branches :
    (standardCubeSpin 0 cell4Basis0 =
        fun component => (-1 / 2 : ℂ) * cell4Basis0 component) ∧
      (standardCubeSpin 0 cell4Basis2 =
        fun component => (-1 / 2 : ℂ) * cell4Basis2 component) := by
  constructor <;>
    funext component <;>
    fin_cases component <;>
    simp [standardCubeSpin, standardCubePlaneBivector,
      standardCubeGamma, standardDiracAlphaX, standardDiracAlphaY,
      cell4Basis0, cell4Basis2] <;>
    ring_nf

/-- The collected results on the oscillation period: after one period `coherentRestState` changes
sign while its velocity, position and density return, after two periods it returns, and on both
cube embeddings one and two periods match the cube rotations by `2 * π` and `4 * π`. -/
structure Dirac024ProjectiveZitterSpinCertificate : Prop where
  previousGate : Dirac023PhaseHarmonyCertificate
  zitterPeriodIsDerivedBeatPeriod :
    nativeZitterPeriod = nativeBranchBeatPeriod
  oneCycleIsSpinorAntiperiod : ∀ time,
    coherentRestState (time + nativeZitterPeriod) =
      fun component => -coherentRestState time component
  twoCyclesReturnSpinor : ∀ time,
    coherentRestState (time + 2 * nativeZitterPeriod) =
      coherentRestState time
  observablesReturnAfterOneCycle : ∀ time,
    restZitterVelocity (time + nativeZitterPeriod) =
        restZitterVelocity time ∧
      nativeZitterPosition (time + nativeZitterPeriod) =
        nativeZitterPosition time ∧
      cell4Density (coherentRestState (time + nativeZitterPeriod)) =
        cell4Density (coherentRestState time)
  halfCycleControl :
    restZitterVelocity nativeZitterHalfPeriod ≠ restZitterVelocity 0
  twoPiBridgeOnBothCopies :
    (∀ axis time,
      cubeContinuousTurn (2 * Real.pi) axis
          (cubeDiracEmbedMinus (coherentRestState time)) =
        cubeDiracEmbedMinus
          (coherentRestState (time + nativeZitterPeriod))) ∧
    (∀ axis time,
      cubeContinuousTurn (2 * Real.pi) axis
          (cubeDiracEmbedPlus (coherentRestState time)) =
        cubeDiracEmbedPlus
          (coherentRestState (time + nativeZitterPeriod)))
  fourPiBridgeOnBothCopies :
    (∀ axis time,
      cubeContinuousTurn (4 * Real.pi) axis
          (cubeDiracEmbedMinus (coherentRestState time)) =
        cubeDiracEmbedMinus
          (coherentRestState (time + 2 * nativeZitterPeriod))) ∧
    (∀ axis time,
      cubeContinuousTurn (4 * Real.pi) axis
          (cubeDiracEmbedPlus (coherentRestState time)) =
        cubeDiracEmbedPlus
          (coherentRestState (time + 2 * nativeZitterPeriod)))
  generatorsRemainDistinct :
    ((standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis0 =
        fun component => (chi0 : ℂ) * cell4Basis0 component) ∧
      (standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis2 =
        fun component => -(chi0 : ℂ) * cell4Basis2 component)) ∧
    ((standardCubeSpin 0 cell4Basis0 =
        fun component => (-1 / 2 : ℂ) * cell4Basis0 component) ∧
      (standardCubeSpin 0 cell4Basis2 =
        fun component => (-1 / 2 : ℂ) * cell4Basis2 component))

theorem dirac024_projective_zitter_spin_cycle :
    Dirac024ProjectiveZitterSpinCertificate where
  previousGate := dirac023_phase_harmony_and_time_dilation
  zitterPeriodIsDerivedBeatPeriod :=
    native_zitter_period_eq_branch_beat_period
  oneCycleIsSpinorAntiperiod := coherent_rest_state_one_zitter_cycle
  twoCyclesReturnSpinor := coherent_rest_state_two_zitter_cycles
  observablesReturnAfterOneCycle := fun time =>
    ⟨zitter_velocity_one_cycle_periodic time,
      zitter_position_one_cycle_periodic time,
      coherent_density_one_zitter_cycle_periodic time⟩
  halfCycleControl := half_zitter_period_is_not_a_return
  twoPiBridgeOnBothCopies :=
    ⟨minus_copy_two_pi_rotation_is_one_zitter_cycle,
      plus_copy_two_pi_rotation_is_one_zitter_cycle⟩
  fourPiBridgeOnBothCopies :=
    ⟨minus_copy_four_pi_rotation_is_two_zitter_cycles,
      plus_copy_four_pi_rotation_is_two_zitter_cycles⟩
  generatorsRemainDistinct :=
    ⟨rest_generator_distinguishes_zitter_branches,
      spatial_spin0_acts_equally_on_zitter_branches⟩

end
end LeanDirac

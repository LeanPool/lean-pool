/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac025.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac024

/-!
# DIRAC-025: longitudinal velocity variance and the moving clock

The three velocity operators were derived in DIRAC-013 as momentum responses
of the same Hamiltonian.  DIRAC-019 derived their positive-energy current,
and DIRAC-023 independently derived the moving phase-clock ratio.

This stage combines those results without defining the desired answer.  For
every nonzero momentum it constructs the unit momentum direction, builds the
corresponding longitudinal velocity operator from the three native Hamiltonian
responses, proves that operator squares to `c_eff ^ 2`, and evaluates its first
and second moments in the same positive-frequency state.  The resulting rms
velocity fluctuation, divided by `c_eff`, is exactly the moving-clock rate
divided by the rest-clock rate.

No classical hidden light-speed path is asserted.  This is an operator
expectation identity in the previously derived continuum sector.
-/

@[expose] public section


namespace LeanDirac

noncomputable section
open Complex

def continuumMomentumMagnitudeSq (momentum : LatticeMomentum) : ℝ :=
  ∑ axis, momentum axis ^ 2

def continuumMomentumMagnitude (momentum : LatticeMomentum) : ℝ :=
  Real.sqrt (continuumMomentumMagnitudeSq momentum)

def continuumMomentumDirection
    (momentum : LatticeMomentum) (axis : Fin 3) : ℝ :=
  momentum axis / continuumMomentumMagnitude momentum

theorem continuum_momentum_magnitude_square
    (momentum : LatticeMomentum) :
    continuumMomentumMagnitude momentum ^ 2 =
      continuumMomentumMagnitudeSq momentum := by
  unfold continuumMomentumMagnitude
  rw [Real.sq_sqrt]
  unfold continuumMomentumMagnitudeSq
  positivity

theorem continuum_momentum_magnitude_positive
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0) :
    0 < continuumMomentumMagnitude momentum := by
  unfold continuumMomentumMagnitude
  apply Real.sqrt_pos.2
  unfold continuumMomentumMagnitudeSq
  simp [Fin.sum_univ_succ]
  by_contra hnonpositive
  have hzero0 : momentum 0 = 0 := by
    nlinarith [sq_nonneg (momentum 0), sq_nonneg (momentum 1),
      sq_nonneg (momentum 2)]
  have hzero1 : momentum 1 = 0 := by
    nlinarith [sq_nonneg (momentum 0), sq_nonneg (momentum 1),
      sq_nonneg (momentum 2)]
  have hzero2 : momentum 2 = 0 := by
    nlinarith [sq_nonneg (momentum 0), sq_nonneg (momentum 1),
      sq_nonneg (momentum 2)]
  apply hmomentum
  funext axis
  fin_cases axis <;> simp [hzero0, hzero1, hzero2]

theorem continuum_momentum_direction_unit
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0) :
    ∑ axis, continuumMomentumDirection momentum axis ^ 2 = 1 := by
  have hmagnitude : continuumMomentumMagnitude momentum ≠ 0 :=
    ne_of_gt (continuum_momentum_magnitude_positive momentum hmomentum)
  have hsquare := continuum_momentum_magnitude_square momentum
  unfold continuumMomentumDirection continuumMomentumMagnitudeSq at *
  simp [Fin.sum_univ_succ] at *
  field_simp [hmagnitude]
  nlinarith

def standardC19LongitudinalVelocityOperator
    (momentum : LatticeMomentum) (z : Cell4) : Cell4 :=
  fun component =>
    ∑ axis,
      (continuumMomentumDirection momentum axis : ℂ) *
        standardC19VelocityOperator axis z component

def standardC19LongitudinalCurrent
    (momentum : LatticeMomentum) (z : Cell4) : ℝ :=
  ∑ axis,
    continuumMomentumDirection momentum axis *
      standardC19DiracCurrent axis z

theorem longitudinal_current_is_operator_expectation
    (momentum : LatticeMomentum) (z : Cell4) :
    standardC19LongitudinalCurrent momentum z =
      cell4RealPair z (standardC19LongitudinalVelocityOperator momentum z) := by
  simp [standardC19LongitudinalCurrent,
    standardC19LongitudinalVelocityOperator,
    standardC19DiracCurrent, cell4RealPair, scalarRealPair,
    Complex.mul_re, Fin.sum_univ_succ]
  ring

theorem longitudinal_velocity_operator_square
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0) (z : Cell4) :
    standardC19LongitudinalVelocityOperator momentum
        (standardC19LongitudinalVelocityOperator momentum z) =
      fun component => ((c19ContinuumSpeed ^ 2 : ℝ) : ℂ) * z component := by
  have hunit := continuum_momentum_direction_unit momentum hmomentum
  simp [Fin.sum_univ_succ] at hunit
  have hunitC :
      (continuumMomentumDirection momentum 0 : ℂ) ^ 2 +
          ((continuumMomentumDirection momentum 1 : ℂ) ^ 2 +
          (continuumMomentumDirection momentum 2 : ℂ) ^ 2) = 1 := by
    exact_mod_cast hunit
  funext component
  fin_cases component
  · simp [standardC19LongitudinalVelocityOperator,
      standardC19VelocityOperator, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ,
      Fin.sum_univ_succ]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination
      ((c19ContinuumSpeed : ℂ) ^ 2 * z 0) * hunitC
  · simp [standardC19LongitudinalVelocityOperator,
      standardC19VelocityOperator, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ,
      Fin.sum_univ_succ]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination
      ((c19ContinuumSpeed : ℂ) ^ 2 * z 1) * hunitC
  · simp [standardC19LongitudinalVelocityOperator,
      standardC19VelocityOperator, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ,
      Fin.sum_univ_succ]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination
      ((c19ContinuumSpeed : ℂ) ^ 2 * z 2) * hunitC
  · simp [standardC19LongitudinalVelocityOperator,
      standardC19VelocityOperator, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ,
      Fin.sum_univ_succ]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination
      ((c19ContinuumSpeed : ℂ) ^ 2 * z 3) * hunitC

theorem longitudinal_current_on_positive_frequency_mode
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0)
    (z : Cell4)
    (heigen : standardC19Hamiltonian (chi0 : ℂ) momentum z =
      fun component => (continuumModeFrequency momentum : ℂ) * z component) :
    continuumModeFrequency momentum *
        standardC19LongitudinalCurrent momentum z =
      c19ContinuumSpeed ^ 2 * continuumMomentumMagnitude momentum *
        cell4Density z := by
  have h0 := positive_frequency_dirac_current_relation
    chi0 (continuumModeFrequency momentum) momentum 0 z heigen
  have h1 := positive_frequency_dirac_current_relation
    chi0 (continuumModeFrequency momentum) momentum 1 z heigen
  have h2 := positive_frequency_dirac_current_relation
    chi0 (continuumModeFrequency momentum) momentum 2 z heigen
  have hmagnitude : continuumMomentumMagnitude momentum ≠ 0 :=
    ne_of_gt (continuum_momentum_magnitude_positive momentum hmomentum)
  have hsquare := continuum_momentum_magnitude_square momentum
  unfold standardC19LongitudinalCurrent continuumMomentumDirection
  simp [Fin.sum_univ_succ]
  unfold continuumMomentumMagnitudeSq at hsquare
  simp [Fin.sum_univ_succ] at hsquare
  calc
    continuumModeFrequency momentum *
        (momentum 0 / continuumMomentumMagnitude momentum *
            standardC19DiracCurrent 0 z +
          (momentum 1 / continuumMomentumMagnitude momentum *
              standardC19DiracCurrent 1 z +
            momentum 2 / continuumMomentumMagnitude momentum *
              standardC19DiracCurrent 2 z)) =
        (momentum 0 *
              (continuumModeFrequency momentum *
                standardC19DiracCurrent 0 z) +
          (momentum 1 *
                (continuumModeFrequency momentum *
                  standardC19DiracCurrent 1 z) +
            momentum 2 *
                (continuumModeFrequency momentum *
                  standardC19DiracCurrent 2 z))) /
          continuumMomentumMagnitude momentum := by ring
    _ = (momentum 0 *
              (c19ContinuumSpeed ^ 2 * momentum 0 * cell4Density z) +
          (momentum 1 *
                (c19ContinuumSpeed ^ 2 * momentum 1 * cell4Density z) +
            momentum 2 *
                (c19ContinuumSpeed ^ 2 * momentum 2 * cell4Density z))) /
          continuumMomentumMagnitude momentum := by rw [h0, h1, h2]
    _ = c19ContinuumSpeed ^ 2 * continuumMomentumMagnitude momentum *
          cell4Density z := by
      field_simp [hmagnitude]
      rw [← hsquare]

def longitudinalVelocityMean
    (momentum : LatticeMomentum) (z : Cell4) : ℝ :=
  standardC19LongitudinalCurrent momentum z / cell4Density z

def longitudinalVelocitySecondMoment
    (momentum : LatticeMomentum) (z : Cell4) : ℝ :=
  cell4RealPair z
      (standardC19LongitudinalVelocityOperator momentum
        (standardC19LongitudinalVelocityOperator momentum z)) /
    cell4Density z

def longitudinalVelocityVariance
    (momentum : LatticeMomentum) (z : Cell4) : ℝ :=
  longitudinalVelocitySecondMoment momentum z -
    longitudinalVelocityMean momentum z ^ 2

def normalizedLongitudinalVelocityRms
    (momentum : LatticeMomentum) (z : Cell4) : ℝ :=
  Real.sqrt (longitudinalVelocityVariance momentum z) /
    c19ContinuumSpeed

theorem longitudinal_velocity_mean_on_positive_frequency_mode
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0)
    (z : Cell4) (hdensity : cell4Density z ≠ 0)
    (heigen : standardC19Hamiltonian (chi0 : ℂ) momentum z =
      fun component => (continuumModeFrequency momentum : ℂ) * z component) :
    longitudinalVelocityMean momentum z =
      c19ContinuumSpeed ^ 2 * continuumMomentumMagnitude momentum /
        continuumModeFrequency momentum := by
  have hcurrent := longitudinal_current_on_positive_frequency_mode
    momentum hmomentum z heigen
  have hfrequency : continuumModeFrequency momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  unfold longitudinalVelocityMean
  field_simp [hdensity, hfrequency]
  nlinarith

theorem longitudinal_velocity_second_moment_is_light_speed_square
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0)
    (z : Cell4) (hdensity : cell4Density z ≠ 0) :
    longitudinalVelocitySecondMoment momentum z =
      c19ContinuumSpeed ^ 2 := by
  rw [longitudinalVelocitySecondMoment,
    longitudinal_velocity_operator_square momentum hmomentum]
  rw [cell4_real_pair_real_scale_right,
    cell4_density_is_real_pair_self]
  field_simp [hdensity]

theorem longitudinal_velocity_variance_is_clock_square
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0)
    (z : Cell4) (hdensity : cell4Density z ≠ 0)
    (heigen : standardC19Hamiltonian (chi0 : ℂ) momentum z =
      fun component => (continuumModeFrequency momentum : ℂ) * z component) :
    longitudinalVelocityVariance momentum z =
      c19ContinuumSpeed ^ 2 * continuumTransportClockRatio momentum ^ 2 := by
  rw [longitudinalVelocityVariance,
    longitudinal_velocity_second_moment_is_light_speed_square
      momentum hmomentum z hdensity,
    longitudinal_velocity_mean_on_positive_frequency_mode
      momentum hmomentum z hdensity heigen,
    continuum_transport_clock_ratio_is_mass_over_energy]
  have hfrequency : continuumModeFrequency momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  have hfrequencySq := continuum_mode_frequency_square momentum
  have hmagnitudeSq := continuum_momentum_magnitude_square momentum
  rw [c19_continuum_speed_square]
  unfold continuumModeSquare c19QuadraticSymbol at hfrequencySq
  unfold continuumMomentumMagnitudeSq at hmagnitudeSq
  simp [Fin.sum_univ_succ] at hmagnitudeSq
  field_simp [hfrequency]
  norm_num [chi0] at hfrequencySq ⊢
  nlinarith

theorem normalized_longitudinal_velocity_rms_is_clock_ratio
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0)
    (z : Cell4) (hdensity : cell4Density z ≠ 0)
    (heigen : standardC19Hamiltonian (chi0 : ℂ) momentum z =
      fun component => (continuumModeFrequency momentum : ℂ) * z component) :
    normalizedLongitudinalVelocityRms momentum z =
      continuumTransportClockRatio momentum := by
  rw [normalizedLongitudinalVelocityRms,
    longitudinal_velocity_variance_is_clock_square
      momentum hmomentum z hdensity heigen]
  have hspeed : 0 < c19ContinuumSpeed := by
    unfold c19ContinuumSpeed
    positivity
  have hclock : 0 < continuumTransportClockRatio momentum :=
    continuum_transport_clock_ratio_positive momentum
  rw [show c19ContinuumSpeed ^ 2 *
      continuumTransportClockRatio momentum ^ 2 =
        (c19ContinuumSpeed *
          continuumTransportClockRatio momentum) ^ 2 by ring]
  rw [Real.sqrt_sq (le_of_lt (mul_pos hspeed hclock))]
  field_simp [ne_of_gt hspeed]

theorem normalized_longitudinal_velocity_rms_is_relativistic_factor
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0)
    (z : Cell4) (hdensity : cell4Density z ≠ 0)
    (heigen : standardC19Hamiltonian (chi0 : ℂ) momentum z =
      fun component => (continuumModeFrequency momentum : ℂ) * z component) :
    normalizedLongitudinalVelocityRms momentum z =
      Real.sqrt
        (1 - continuumTransportSpeedSq momentum /
          c19ContinuumSpeed ^ 2) := by
  rw [normalized_longitudinal_velocity_rms_is_clock_ratio
    momentum hmomentum z hdensity heigen]
  exact continuum_clock_ratio_is_sqrt_speed_factor momentum

theorem velocity_clock_pythagorean_identity
    (momentum : LatticeMomentum) (hmomentum : momentum ≠ 0)
    (z : Cell4) (hdensity : cell4Density z ≠ 0)
    (heigen : standardC19Hamiltonian (chi0 : ℂ) momentum z =
      fun component => (continuumModeFrequency momentum : ℂ) * z component) :
    normalizedLongitudinalVelocityRms momentum z ^ 2 +
        continuumTransportSpeedSq momentum / c19ContinuumSpeed ^ 2 = 1 := by
  rw [normalized_longitudinal_velocity_rms_is_clock_ratio
    momentum hmomentum z hdensity heigen]
  have hclock := continuum_clock_ratio_square_is_speed_factor momentum
  linarith

theorem three_four_five_clock_control
    (momentum : LatticeMomentum)
    (hspeed : continuumTransportSpeedSq momentum /
        c19ContinuumSpeed ^ 2 = (9 : ℝ) / 25) :
    continuumTransportClockRatio momentum = (4 : ℝ) / 5 := by
  rw [continuum_clock_ratio_is_sqrt_speed_factor, hspeed]
  norm_num

structure Dirac025VelocityClockCertificate : Prop where
  previousGate : Dirac024ProjectiveZitterSpinCertificate
  longitudinalOperatorIsHamiltonianDerived :
    ∀ (mass : ℝ) momentum axis delta z,
      standardC19Hamiltonian (mass : ℂ)
          (shiftLatticeMomentum axis delta momentum) z =
        fun component =>
          standardC19Hamiltonian (mass : ℂ) momentum z component +
            (delta : ℂ) * standardC19VelocityOperator axis z component
  longitudinalOperatorSquaresToLightSpeed :
    ∀ momentum, momentum ≠ 0 → ∀ z,
      standardC19LongitudinalVelocityOperator momentum
          (standardC19LongitudinalVelocityOperator momentum z) =
        fun component => ((c19ContinuumSpeed ^ 2 : ℝ) : ℂ) * z component
  longitudinalCurrentIsSameStateExpectation :
    ∀ momentum z,
      standardC19LongitudinalCurrent momentum z =
        cell4RealPair z
          (standardC19LongitudinalVelocityOperator momentum z)
  sameStateMeanAndVariance :
    ∀ momentum, momentum ≠ 0 → ∀ z, cell4Density z ≠ 0 →
      standardC19Hamiltonian (chi0 : ℂ) momentum z =
          (fun component =>
            (continuumModeFrequency momentum : ℂ) * z component) →
      longitudinalVelocityMean momentum z =
          c19ContinuumSpeed ^ 2 * continuumMomentumMagnitude momentum /
            continuumModeFrequency momentum ∧
        longitudinalVelocityVariance momentum z =
          c19ContinuumSpeed ^ 2 * continuumTransportClockRatio momentum ^ 2
  normalizedRmsIsMovingClock :
    ∀ momentum, momentum ≠ 0 → ∀ z, cell4Density z ≠ 0 →
      standardC19Hamiltonian (chi0 : ℂ) momentum z =
          (fun component =>
            (continuumModeFrequency momentum : ℂ) * z component) →
      normalizedLongitudinalVelocityRms momentum z =
        continuumTransportClockRatio momentum
  velocityClockPythagoreanIdentity :
    ∀ momentum, momentum ≠ 0 → ∀ z, cell4Density z ≠ 0 →
      standardC19Hamiltonian (chi0 : ℂ) momentum z =
          (fun component =>
            (continuumModeFrequency momentum : ℂ) * z component) →
      normalizedLongitudinalVelocityRms momentum z ^ 2 +
          continuumTransportSpeedSq momentum / c19ContinuumSpeed ^ 2 = 1
  knownThreeFourFiveControl :
    ∀ momentum,
      continuumTransportSpeedSq momentum / c19ContinuumSpeed ^ 2 =
          (9 : ℝ) / 25 →
        continuumTransportClockRatio momentum = (4 : ℝ) / 5

theorem dirac025_velocity_variance_clock_identity :
    Dirac025VelocityClockCertificate where
  previousGate := dirac024_projective_zitter_spin_cycle
  longitudinalOperatorIsHamiltonianDerived :=
    standard_c19_velocity_is_hamiltonian_momentum_response
  longitudinalOperatorSquaresToLightSpeed :=
    longitudinal_velocity_operator_square
  longitudinalCurrentIsSameStateExpectation :=
    longitudinal_current_is_operator_expectation
  sameStateMeanAndVariance := fun momentum hmomentum z hdensity heigen =>
    ⟨longitudinal_velocity_mean_on_positive_frequency_mode
        momentum hmomentum z hdensity heigen,
      longitudinal_velocity_variance_is_clock_square
        momentum hmomentum z hdensity heigen⟩
  normalizedRmsIsMovingClock :=
    normalized_longitudinal_velocity_rms_is_clock_ratio
  velocityClockPythagoreanIdentity :=
    velocity_clock_pythagorean_identity
  knownThreeFourFiveControl := three_four_five_clock_control

end
end LeanDirac

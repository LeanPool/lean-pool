/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac022.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac021

/-!
# DIRAC-022: action-derived free zitterbewegung observable

This gate uses only the Hamiltonian, rest branches, phases, and velocity
operator proved upstream.  At zero momentum the existing velocity operator
couples `cell4Basis0` to `cell4Basis2`.  A normalized coherent superposition
of those proved energy branches therefore has a velocity cross term whose
phase is their already-derived relative phase.  The oscillation frequency is
`2 * chi0`; it is not supplied as a new clock or force.

The theorem is a free-continuum expectation-value result.  It does not claim
that a localized nonlinear native lattice electron has been constructed or
observed to tremble, and it introduces no action term, field, coefficient,
position rule, or electromagnetic coupling.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

def zitterNormalization : ℝ :=
  1 / Real.sqrt 2

def coherentRestPhaseSuperposition (time : ℝ) : Cell4 :=
  fun component =>
    (zitterNormalization : ℂ) *
      (positiveRestEvolution (time : ℂ) component +
        negativeRestEvolution (time : ℂ) component)

def coherentRestState (time : ℝ) : Cell4
  | 0 => ⟨zitterNormalization * Real.cos (chi0 * time),
      -(zitterNormalization * Real.sin (chi0 * time))⟩
  | 1 => 0
  | 2 => ⟨zitterNormalization * Real.cos (chi0 * time),
      zitterNormalization * Real.sin (chi0 * time)⟩
  | _ => 0

def restZitterVelocity (time : ℝ) : ℝ :=
  standardC19DiracCurrent 0 (coherentRestState time)

def nativeZitterAngularFrequency : ℝ :=
  nativeBranchBeatAngularFrequency

def nativeZitterAmplitude : ℝ :=
  c19ContinuumSpeed / (2 * nativeRestAngularFrequency)

def nativeZitterPosition (time : ℝ) : ℝ :=
  nativeZitterAmplitude * Real.sin (nativeZitterAngularFrequency * time)

def nativeZitterPeakToPeak : ℝ :=
  2 * nativeZitterAmplitude

theorem zitter_normalization_square :
    zitterNormalization ^ 2 = (1 : ℝ) / 2 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  rw [zitterNormalization, div_pow, one_pow, hsquare]

theorem positive_rest_phase_on_real_time (time : ℝ) :
    positiveRestPhase (time : ℂ) =
      (Real.cos (chi0 * time) : ℂ) -
        Complex.I * (Real.sin (chi0 * time) : ℂ) := by
  rw [positiveRestPhase]
  have hexponent :
      -Complex.I * (chi0 : ℂ) * (time : ℂ) =
        (((-(chi0 * time) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexponent, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

theorem negative_rest_phase_on_real_time (time : ℝ) :
    negativeRestPhase (time : ℂ) =
      (Real.cos (chi0 * time) : ℂ) +
        Complex.I * (Real.sin (chi0 * time) : ℂ) := by
  rw [negativeRestPhase]
  have hexponent :
      Complex.I * (chi0 : ℂ) * (time : ℂ) =
        (((chi0 * time : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexponent, Complex.exp_ofReal_mul_I]
  ring

theorem coherent_rest_state_is_proved_phase_superposition (time : ℝ) :
    coherentRestState time = coherentRestPhaseSuperposition time := by
  funext component
  fin_cases component <;>
    simp [coherentRestState, coherentRestPhaseSuperposition,
      positiveRestEvolution, negativeRestEvolution,
      cell4Basis0, cell4Basis2,
      positive_rest_phase_on_real_time,
      negative_rest_phase_on_real_time,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;>
    simp only [← Complex.ofReal_mul, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im] <;>
    simp

theorem coherent_rest_state_density_one (time : ℝ) :
    cell4Density (coherentRestState time) = 1 := by
  simp [cell4Density, coherentRestState, Complex.normSq,
    Fin.sum_univ_succ]
  nlinarith [zitter_normalization_square,
    Real.sin_sq_add_cos_sq (chi0 * time)]

theorem positive_rest_branch_current_zero (time : ℝ) :
    standardC19DiracCurrent 0 (positiveRestEvolution (time : ℂ)) = 0 := by
  simp [standardC19DiracCurrent, cell4RealPair, scalarRealPair,
    standardC19VelocityOperator, standardDiracAlphaZ,
    positiveRestEvolution, cell4Basis0, Complex.mul_re,
    Fin.sum_univ_succ]

theorem negative_rest_branch_current_zero (time : ℝ) :
    standardC19DiracCurrent 0 (negativeRestEvolution (time : ℂ)) = 0 := by
  simp [standardC19DiracCurrent, cell4RealPair, scalarRealPair,
    standardC19VelocityOperator, standardDiracAlphaZ,
    negativeRestEvolution, cell4Basis2, Complex.mul_re,
    Fin.sum_univ_succ]

theorem coherent_rest_velocity_cross_term (time : ℝ) :
    restZitterVelocity time =
      c19ContinuumSpeed * Real.cos (2 * chi0 * time) := by
  simp only [restZitterVelocity, standardC19DiracCurrent, cell4RealPair, scalarRealPair,
      coherentRestState, RCLike.star_def, standardC19VelocityOperator, Fin.isValue,
      standardDiracAlphaZ, neg_zero, mul_re, conj_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      conj_im, mul_im, add_zero, neg_mul, sub_neg_eq_add, Fin.sum_univ_succ, Fin.succ_ne_zero,
      imp_self, Fin.succ_zero_eq_one, zero_re, mul_zero, zero_im, Fin.succ_one_eq_two, mul_neg,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.reduceSucc, zero_add]
  rw [show 2 * chi0 * time = 2 * (chi0 * time) by ring,
    Real.cos_two_mul]
  ring_nf
  rw [zitter_normalization_square]
  have htrig : Real.sin (chi0 * time) ^ 2 =
      1 - Real.cos (chi0 * time) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (chi0 * time)]
  rw [htrig]
  ring

theorem native_zitter_angular_frequency_eq_thirty_eight :
    nativeZitterAngularFrequency = 38 := by
  exact native_branch_beat_angular_frequency_eq_thirty_eight

theorem native_zitter_frequency_is_twice_action_mass :
    nativeZitterAngularFrequency = 2 * chi0 := by
  rw [nativeZitterAngularFrequency, nativeBranchBeatAngularFrequency,
    nativeRestAngularFrequency, continuum_rest_frequency_is_chi0]

theorem native_zitter_amplitude_eq_sqrt_twelve_over_thirty_eight :
    nativeZitterAmplitude = Real.sqrt 12 / 38 := by
  rw [nativeZitterAmplitude, native_rest_angular_frequency_eq_nineteen]
  norm_num [c19ContinuumSpeed]

theorem native_zitter_amplitude_is_half_reduced_compton_length :
    nativeZitterAmplitude = nativeReducedComptonLength / 2 := by
  rw [nativeZitterAmplitude, nativeReducedComptonLength]
  have hfreq : nativeRestAngularFrequency ≠ 0 := by
    rw [native_rest_angular_frequency_eq_nineteen]
    norm_num
  field_simp [hfreq]

theorem native_zitter_peak_to_peak_is_reduced_compton_length :
    nativeZitterPeakToPeak = nativeReducedComptonLength := by
  rw [nativeZitterPeakToPeak,
    native_zitter_amplitude_is_half_reduced_compton_length]
  ring

theorem native_zitter_amplitude_nonnegative :
    0 ≤ nativeZitterAmplitude := by
  rw [native_zitter_amplitude_eq_sqrt_twelve_over_thirty_eight]
  positivity

theorem native_zitter_position_bound (time : ℝ) :
    |nativeZitterPosition time| ≤ nativeZitterAmplitude := by
  rw [nativeZitterPosition, abs_mul,
    abs_of_nonneg native_zitter_amplitude_nonnegative]
  exact mul_le_of_le_one_right native_zitter_amplitude_nonnegative
    (Real.abs_sin_le_one _)

theorem native_zitter_amplitude_times_frequency :
    nativeZitterAmplitude * nativeZitterAngularFrequency =
      c19ContinuumSpeed := by
  rw [nativeZitterAmplitude, native_zitter_frequency_is_twice_action_mass,
    nativeRestAngularFrequency, continuum_rest_frequency_is_chi0]
  norm_num [chi0]

theorem native_zitter_position_has_velocity_derivative (time : ℝ) :
    HasDerivAt nativeZitterPosition (restZitterVelocity time) time := by
  unfold nativeZitterPosition
  rw [coherent_rest_velocity_cross_term]
  have hderiv := ((hasDerivAt_const_mul
    (x := time) nativeZitterAngularFrequency).sin).const_mul
      nativeZitterAmplitude
  apply hderiv.congr_deriv
  calc
    nativeZitterAmplitude *
          (Real.cos (nativeZitterAngularFrequency * time) *
            nativeZitterAngularFrequency) =
        (nativeZitterAmplitude * nativeZitterAngularFrequency) *
          Real.cos (nativeZitterAngularFrequency * time) := by ring
    _ = c19ContinuumSpeed *
          Real.cos (nativeZitterAngularFrequency * time) := by
      rw [native_zitter_amplitude_times_frequency]
    _ = c19ContinuumSpeed * Real.cos (2 * chi0 * time) := by
      rw [native_zitter_frequency_is_twice_action_mass]

def cell4Basis1 : Cell4
  | 1 => 1
  | _ => 0

theorem second_positive_rest_state_has_native_energy :
    standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis1 =
      fun component => (chi0 : ℂ) * cell4Basis1 component := by
  funext component
  fin_cases component <;>
    simp [standardC19Hamiltonian, zeroLatticeMomentum,
      standardDiracHamiltonian, standardDiracSpatial, standardDiracBeta,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ,
      cell4Basis1]

def sameSignPositiveRestState (time : ℝ) : Cell4 :=
  fun component =>
    (zitterNormalization : ℂ) * positiveRestPhase (time : ℂ) *
      (cell4Basis0 component + cell4Basis1 component)

theorem same_sign_rest_control_has_zero_current (time : ℝ) :
    standardC19DiracCurrent 0 (sameSignPositiveRestState time) = 0 := by
  simp [sameSignPositiveRestState, standardC19DiracCurrent,
    cell4RealPair, scalarRealPair, standardC19VelocityOperator,
    standardDiracAlphaZ, cell4Basis0, cell4Basis1,
    Complex.mul_re, Complex.mul_im, Fin.sum_univ_succ]

def incoherentRestMixtureCurrent (time : ℝ) : ℝ :=
  (standardC19DiracCurrent 0 (positiveRestEvolution (time : ℂ)) +
    standardC19DiracCurrent 0 (negativeRestEvolution (time : ℂ))) / 2

theorem incoherent_rest_mixture_has_zero_current (time : ℝ) :
    incoherentRestMixtureCurrent time = 0 := by
  rw [incoherentRestMixtureCurrent,
    positive_rest_branch_current_zero,
    negative_rest_branch_current_zero]
  norm_num

def parametricCoherentRestState (testMass time : ℝ) : Cell4
  | 0 => ⟨zitterNormalization * Real.cos (testMass * time),
      -(zitterNormalization * Real.sin (testMass * time))⟩
  | 1 => 0
  | 2 => ⟨zitterNormalization * Real.cos (testMass * time),
      zitterNormalization * Real.sin (testMass * time)⟩
  | _ => 0

def parametricRestVelocity (testMass time : ℝ) : ℝ :=
  standardC19DiracCurrent 0 (parametricCoherentRestState testMass time)

theorem parametric_rest_velocity_tracks_supplied_mass
    (testMass time : ℝ) :
    parametricRestVelocity testMass time =
      c19ContinuumSpeed * Real.cos (2 * testMass * time) := by
  simp only [parametricRestVelocity, standardC19DiracCurrent, cell4RealPair, scalarRealPair,
      parametricCoherentRestState, RCLike.star_def, standardC19VelocityOperator, Fin.isValue,
      standardDiracAlphaZ, neg_zero, mul_re, conj_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      conj_im, mul_im, add_zero, neg_mul, sub_neg_eq_add, Fin.sum_univ_succ, Fin.succ_ne_zero,
      imp_self, Fin.succ_zero_eq_one, zero_re, mul_zero, zero_im, Fin.succ_one_eq_two, mul_neg,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.reduceSucc,
      zero_add]
  rw [show 2 * testMass * time = 2 * (testMass * time) by ring,
    Real.cos_two_mul]
  ring_nf
  rw [zitter_normalization_square]
  have htrig : Real.sin (testMass * time) ^ 2 =
      1 - Real.cos (testMass * time) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (testMass * time)]
  rw [htrig]
  ring

theorem axis_zero_velocity_swaps_positive_rest_basis :
    standardC19VelocityOperator 0 cell4Basis0 =
      fun component =>
        (c19ContinuumSpeed : ℂ) * cell4Basis2 component := by
  funext component
  fin_cases component <;>
    simp [standardC19VelocityOperator, standardDiracAlphaZ,
      cell4Basis0, cell4Basis2]

theorem axis_zero_velocity_swaps_negative_rest_basis :
    standardC19VelocityOperator 0 cell4Basis2 =
      fun component =>
        (c19ContinuumSpeed : ℂ) * cell4Basis0 component := by
  funext component
  fin_cases component <;>
    simp [standardC19VelocityOperator, standardDiracAlphaZ,
      cell4Basis0, cell4Basis2]

theorem rest_velocity_is_existing_hamiltonian_momentum_response
    (delta : ℝ) (z : Cell4) :
    standardC19Hamiltonian (chi0 : ℂ)
        (shiftLatticeMomentum 0 delta zeroLatticeMomentum) z =
      fun component =>
        standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum z component +
          (delta : ℂ) * standardC19VelocityOperator 0 z component := by
  exact standard_c19_velocity_is_hamiltonian_momentum_response
    chi0 zeroLatticeMomentum 0 delta z

theorem rest_hamiltonian_velocity_anticommute (z : Cell4) :
    (fun component =>
      standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
          (standardC19VelocityOperator 0 z) component +
        standardC19VelocityOperator 0
          (standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum z)
          component) = (fun _ => 0) := by
  simpa [zeroLatticeMomentum] using
    (standard_c19_hamiltonian_velocity_anticommutator
      chi0 zeroLatticeMomentum 0 z)

structure Dirac022ZitterbewegungCertificate : Prop where
  previousGate : Dirac021RestClockCertificate
  phaseConstruction : ∀ time,
    coherentRestState time = coherentRestPhaseSuperposition time
  normalized : ∀ time, cell4Density (coherentRestState time) = 1
  velocityFromHamiltonian : ∀ delta z,
    standardC19Hamiltonian (chi0 : ℂ)
        (shiftLatticeMomentum 0 delta zeroLatticeMomentum) z =
      fun component =>
        standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum z component +
          (delta : ℂ) * standardC19VelocityOperator 0 z component
  branchCoupling :
    standardC19VelocityOperator 0 cell4Basis0 =
        (fun component =>
          (c19ContinuumSpeed : ℂ) * cell4Basis2 component) ∧
      standardC19VelocityOperator 0 cell4Basis2 =
        fun component =>
          (c19ContinuumSpeed : ℂ) * cell4Basis0 component
  pureBranchControl : ∀ time : ℝ,
    standardC19DiracCurrent 0 (positiveRestEvolution (time : ℂ)) = 0 ∧
      standardC19DiracCurrent 0 (negativeRestEvolution (time : ℂ)) = 0
  coherentVelocity : ∀ time,
    restZitterVelocity time =
      c19ContinuumSpeed * Real.cos (2 * chi0 * time)
  exactFrequency :
    nativeZitterAngularFrequency = 2 * chi0 ∧
      nativeZitterAngularFrequency = 38
  positionLaw : ∀ time,
    HasDerivAt nativeZitterPosition (restZitterVelocity time) time
  amplitudeBound : ∀ time,
    |nativeZitterPosition time| ≤ nativeZitterAmplitude
  nativeLengthScales :
    nativeZitterAmplitude = Real.sqrt 12 / 38 ∧
      nativeZitterAmplitude = nativeReducedComptonLength / 2 ∧
      nativeZitterPeakToPeak = nativeReducedComptonLength
  sameSignControl : ∀ time,
    standardC19DiracCurrent 0 (sameSignPositiveRestState time) = 0
  incoherentControl : ∀ time, incoherentRestMixtureCurrent time = 0
  wrongMassControl : ∀ testMass time,
    parametricRestVelocity testMass time =
      c19ContinuumSpeed * Real.cos (2 * testMass * time)
  restAnticommutation : ∀ z, (fun component =>
      standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
          (standardC19VelocityOperator 0 z) component +
        standardC19VelocityOperator 0
          (standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum z)
          component) = (fun _ => 0)

theorem dirac022_action_derived_zitterbewegung :
    Dirac022ZitterbewegungCertificate where
  previousGate := dirac021_action_derived_rest_clock
  phaseConstruction := coherent_rest_state_is_proved_phase_superposition
  normalized := coherent_rest_state_density_one
  velocityFromHamiltonian :=
    rest_velocity_is_existing_hamiltonian_momentum_response
  branchCoupling :=
    ⟨axis_zero_velocity_swaps_positive_rest_basis,
      axis_zero_velocity_swaps_negative_rest_basis⟩
  pureBranchControl := fun time =>
    ⟨positive_rest_branch_current_zero time,
      negative_rest_branch_current_zero time⟩
  coherentVelocity := coherent_rest_velocity_cross_term
  exactFrequency :=
    ⟨native_zitter_frequency_is_twice_action_mass,
      native_zitter_angular_frequency_eq_thirty_eight⟩
  positionLaw := native_zitter_position_has_velocity_derivative
  amplitudeBound := native_zitter_position_bound
  nativeLengthScales :=
    ⟨native_zitter_amplitude_eq_sqrt_twelve_over_thirty_eight,
      native_zitter_amplitude_is_half_reduced_compton_length,
      native_zitter_peak_to_peak_is_reduced_compton_length⟩
  sameSignControl := same_sign_rest_control_has_zero_current
  incoherentControl := incoherent_rest_mixture_has_zero_current
  wrongMassControl := parametric_rest_velocity_tracks_supplied_mass
  restAnticommutation := rest_hamiltonian_velocity_anticommute

end
end LeanDirac

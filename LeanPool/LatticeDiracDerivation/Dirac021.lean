/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac021.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac020

/-!
# DIRAC-021: action-derived rest clock and branch coherence

DIRAC-011 already proves that the prepared native running family selects the
unique nonnegative rest coefficient `chi0`.  This gate follows that same
coefficient through the four-component Hamiltonian instead of introducing a
new mass scale.

At zero momentum the two mass-grading sectors have energies `+chi0` and
`-chi0`.  Their exact continuum time evolutions therefore rotate with opposite
phase.  Lean proves the componentwise first-order equations, the exact
single-branch period, and the doubled relative-phase frequency of a coherent
positive/negative branch pair.

The result is in native lattice units.  A pure energy eigenstate's global
phase is not by itself an observable clock, and this theorem does not convert
`chi0 = 19` into an SI electron mass.  The doubled branch-coherence frequency
is available only when both energy signs occur coherently.  No action term,
field, coefficient, electromagnetic coupling, or particle rule is added.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-- The standard basis vector of `Cell4` with a `1` in position `2` and `0` elsewhere. -/
def cell4Basis2 : Cell4
  | 2 => 1
  | _ => 0

theorem continuum_rest_frequency_is_chi0 :
    continuumModeFrequency zeroLatticeMomentum = chi0 := by
  unfold continuumModeFrequency continuumModeSquare c19QuadraticSymbol
    zeroLatticeMomentum chi0
  norm_num

theorem continuum_rest_frequency_eq_nineteen :
    continuumModeFrequency zeroLatticeMomentum = 19 := by
  simpa [chi0] using continuum_rest_frequency_is_chi0

theorem positive_rest_state_has_native_energy :
    standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis0 =
      fun component => (chi0 : ℂ) * cell4Basis0 component := by
  funext component
  fin_cases component <;>
    simp [standardC19Hamiltonian, zeroLatticeMomentum,
      standardDiracHamiltonian, standardDiracSpatial, standardDiracBeta,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ,
      cell4Basis0]

theorem negative_rest_state_has_native_energy :
    standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis2 =
      fun component => -(chi0 : ℂ) * cell4Basis2 component := by
  funext component
  fin_cases component <;>
    simp [standardC19Hamiltonian, zeroLatticeMomentum,
      standardDiracHamiltonian, standardDiracSpatial, standardDiracBeta,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ,
      cell4Basis2]

/-- The phase factor `exp (-i chi0 t)` at time `t`, with `chi0 = 19`. -/
def positiveRestPhase (time : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (chi0 : ℂ) * time)

/-- The phase factor `exp (i chi0 t)` at time `t`, with `chi0 = 19`. -/
def negativeRestPhase (time : ℂ) : ℂ :=
  Complex.exp (Complex.I * (chi0 : ℂ) * time)

theorem positive_rest_phase_has_deriv_at (time : ℂ) :
    HasDerivAt positiveRestPhase
      ((-Complex.I * (chi0 : ℂ)) * positiveRestPhase time) time := by
  have hlinear : HasDerivAt
      (fun tau : ℂ => (-Complex.I * (chi0 : ℂ)) * tau)
      (-Complex.I * (chi0 : ℂ)) time := by
    simpa using (hasDerivAt_id time).const_mul
      (-Complex.I * (chi0 : ℂ))
  change HasDerivAt
    (fun tau : ℂ => Complex.exp
      ((-Complex.I * (chi0 : ℂ)) * tau))
    ((-Complex.I * (chi0 : ℂ)) *
      Complex.exp ((-Complex.I * (chi0 : ℂ)) * time)) time
  simpa only [mul_comm] using hlinear.cexp

theorem negative_rest_phase_has_deriv_at (time : ℂ) :
    HasDerivAt negativeRestPhase
      ((Complex.I * (chi0 : ℂ)) * negativeRestPhase time) time := by
  have hlinear : HasDerivAt
      (fun tau : ℂ => (Complex.I * (chi0 : ℂ)) * tau)
      (Complex.I * (chi0 : ℂ)) time := by
    simpa using (hasDerivAt_id time).const_mul
      (Complex.I * (chi0 : ℂ))
  change HasDerivAt
    (fun tau : ℂ => Complex.exp
      ((Complex.I * (chi0 : ℂ)) * tau))
    ((Complex.I * (chi0 : ℂ)) *
      Complex.exp ((Complex.I * (chi0 : ℂ)) * time)) time
  simpa only [mul_comm] using hlinear.cexp

/-- The four-component vector `positiveRestPhase t • cell4Basis0` at time `t`. -/
def positiveRestEvolution (time : ℂ) : Cell4 :=
  fun component => positiveRestPhase time * cell4Basis0 component

/-- The four-component vector `negativeRestPhase t • cell4Basis2` at time `t`. -/
def negativeRestEvolution (time : ℂ) : Cell4 :=
  fun component => negativeRestPhase time * cell4Basis2 component

theorem positive_rest_evolution_has_deriv_at
    (time : ℂ) (component : Fin 4) :
    HasDerivAt (fun tau => positiveRestEvolution tau component)
      ((-Complex.I * (chi0 : ℂ)) *
        positiveRestEvolution time component) time := by
  simpa [positiveRestEvolution, mul_assoc] using
    (positive_rest_phase_has_deriv_at time).mul_const
      (cell4Basis0 component)

theorem negative_rest_evolution_has_deriv_at
    (time : ℂ) (component : Fin 4) :
    HasDerivAt (fun tau => negativeRestEvolution tau component)
      ((Complex.I * (chi0 : ℂ)) *
        negativeRestEvolution time component) time := by
  simpa [negativeRestEvolution, mul_assoc] using
    (negative_rest_phase_has_deriv_at time).mul_const
      (cell4Basis2 component)

theorem positive_rest_evolution_satisfies_dirac (time : ℂ) :
    (fun component => Complex.I *
        ((-Complex.I * (chi0 : ℂ)) *
          positiveRestEvolution time component)) =
      standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
        (positiveRestEvolution time) := by
  rw [show positiveRestEvolution time =
      fun component => positiveRestPhase time * cell4Basis0 component by rfl]
  rw [standard_c19_hamiltonian_complex_scale,
    positive_rest_state_has_native_energy]
  funext component
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  rw [show Complex.I * (-Complex.I * (chi0 : ℂ) *
      (positiveRestPhase time * cell4Basis0 component)) =
      (Complex.I * (-Complex.I)) * (chi0 : ℂ) *
        (positiveRestPhase time * cell4Basis0 component) by ring,
    hI]
  ring

theorem negative_rest_evolution_satisfies_dirac (time : ℂ) :
    (fun component => Complex.I *
        ((Complex.I * (chi0 : ℂ)) *
          negativeRestEvolution time component)) =
      standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
        (negativeRestEvolution time) := by
  rw [show negativeRestEvolution time =
      fun component => negativeRestPhase time * cell4Basis2 component by rfl]
  rw [standard_c19_hamiltonian_complex_scale,
    negative_rest_state_has_native_energy]
  funext component
  rw [show Complex.I * (Complex.I * (chi0 : ℂ) *
      (negativeRestPhase time * cell4Basis2 component)) =
      (Complex.I * Complex.I) * (chi0 : ℂ) *
        (negativeRestPhase time * cell4Basis2 component) by ring,
    Complex.I_mul_I]
  ring

/-- The ratio `positiveRestPhase t / negativeRestPhase t`, which equals `exp (-2 i chi0 t)`. -/
def restBranchRelativePhase (time : ℂ) : ℂ :=
  positiveRestPhase time / negativeRestPhase time

theorem rest_branch_relative_phase_is_doubled (time : ℂ) :
    restBranchRelativePhase time =
      Complex.exp (-Complex.I * ((2 * chi0 : ℝ) : ℂ) * time) := by
  unfold restBranchRelativePhase positiveRestPhase negativeRestPhase
  rw [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The continuum frequency `continuumModeFrequency` at zero momentum, which equals `19`. -/
def nativeRestAngularFrequency : ℝ :=
  continuumModeFrequency zeroLatticeMomentum

/-- Twice the zero-momentum frequency `nativeRestAngularFrequency`, which equals `38`. -/
def nativeBranchBeatAngularFrequency : ℝ :=
  2 * nativeRestAngularFrequency

/-- The period `2π / nativeRestAngularFrequency`, which equals `2π / 19`. -/
def nativeRestClockPeriod : ℝ :=
  2 * Real.pi / nativeRestAngularFrequency

/-- The period `π / nativeRestAngularFrequency`, which equals `π / 19`. -/
def nativeBranchBeatPeriod : ℝ :=
  Real.pi / nativeRestAngularFrequency

/-- The reciprocal `1 / nativeRestAngularFrequency`, which equals `1 / 19`. -/
def nativeInverseMassScale : ℝ :=
  1 / nativeRestAngularFrequency

/-- The ratio `c19ContinuumSpeed / nativeRestAngularFrequency`, which equals `√12 / 19`. -/
def nativeReducedComptonLength : ℝ :=
  c19ContinuumSpeed / nativeRestAngularFrequency

theorem native_rest_angular_frequency_eq_nineteen :
    nativeRestAngularFrequency = 19 := by
  exact continuum_rest_frequency_eq_nineteen

theorem native_branch_beat_angular_frequency_eq_thirty_eight :
    nativeBranchBeatAngularFrequency = 38 := by
  norm_num [nativeBranchBeatAngularFrequency,
    nativeRestAngularFrequency, continuum_rest_frequency_is_chi0, chi0]

theorem native_branch_beat_frequency_is_twice_rest :
    nativeBranchBeatAngularFrequency = 2 * nativeRestAngularFrequency := by
  rfl

theorem native_rest_clock_period_eq_two_pi_over_nineteen :
    nativeRestClockPeriod = 2 * Real.pi / 19 := by
  rw [nativeRestClockPeriod, native_rest_angular_frequency_eq_nineteen]

theorem native_branch_beat_period_eq_pi_over_nineteen :
    nativeBranchBeatPeriod = Real.pi / 19 := by
  rw [nativeBranchBeatPeriod, native_rest_angular_frequency_eq_nineteen]

theorem native_branch_beat_period_is_half_rest_clock :
    nativeBranchBeatPeriod = nativeRestClockPeriod / 2 := by
  rw [nativeBranchBeatPeriod, nativeRestClockPeriod]
  field_simp [show nativeRestAngularFrequency ≠ 0 by
    rw [native_rest_angular_frequency_eq_nineteen]
    norm_num]

theorem native_inverse_mass_scale_eq_one_over_nineteen :
    nativeInverseMassScale = 1 / 19 := by
  rw [nativeInverseMassScale, native_rest_angular_frequency_eq_nineteen]

theorem native_reduced_compton_length_eq_sqrt_twelve_over_nineteen :
    nativeReducedComptonLength = Real.sqrt 12 / 19 := by
  rw [nativeReducedComptonLength, native_rest_angular_frequency_eq_nineteen]
  rfl

theorem positive_rest_phase_returns_after_native_clock :
    positiveRestPhase (nativeRestClockPeriod : ℂ) = 1 := by
  have hexponent :
      -Complex.I * (chi0 : ℂ) * (nativeRestClockPeriod : ℂ) =
        -(2 * (Real.pi : ℂ) * Complex.I) := by
    rw [nativeRestClockPeriod, nativeRestAngularFrequency,
      continuum_rest_frequency_is_chi0]
    norm_num [chi0]
    ring
  rw [positiveRestPhase, hexponent, Complex.exp_neg,
    Complex.exp_two_pi_mul_I]
  simp

theorem negative_rest_phase_returns_after_native_clock :
    negativeRestPhase (nativeRestClockPeriod : ℂ) = 1 := by
  have hexponent :
      Complex.I * (chi0 : ℂ) * (nativeRestClockPeriod : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I := by
    rw [nativeRestClockPeriod, nativeRestAngularFrequency,
      continuum_rest_frequency_is_chi0]
    norm_num [chi0]
    ring
  rw [negativeRestPhase, hexponent, Complex.exp_two_pi_mul_I]

theorem rest_branch_coherence_returns_after_native_beat_period :
    restBranchRelativePhase (nativeBranchBeatPeriod : ℂ) = 1 := by
  rw [rest_branch_relative_phase_is_doubled]
  have hexponent :
      -Complex.I * ((2 * chi0 : ℝ) : ℂ) *
          (nativeBranchBeatPeriod : ℂ) =
        -(2 * (Real.pi : ℂ) * Complex.I) := by
    rw [nativeBranchBeatPeriod, nativeRestAngularFrequency,
      continuum_rest_frequency_is_chi0]
    norm_num [chi0]
    ring
  rw [hexponent, Complex.exp_neg, Complex.exp_two_pi_mul_I]
  simp

/-- The bundle of results of this file: the zero-momentum frequency is `chi0`; `cell4Basis0` and
`cell4Basis2` are eigenvectors of `standardC19Hamiltonian chi0 zeroLatticeMomentum` with
eigenvalues `chi0` and `-chi0`; the two phase evolutions solve the corresponding first-order
equations; and the frequencies `19` and `38`, the periods and the scales take the stated values. -/
structure Dirac021RestClockCertificate : Prop where
  previousGate : Dirac020CoherentSpatialTransportCertificate
  nativeRestFrequency : continuumModeFrequency zeroLatticeMomentum = chi0
  positiveRestEnergy :
    standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis0 =
      fun component => (chi0 : ℂ) * cell4Basis0 component
  negativeRestEnergy :
    standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum cell4Basis2 =
      fun component => -(chi0 : ℂ) * cell4Basis2 component
  positiveRestEquation : ∀ time,
    (fun component => Complex.I *
        ((-Complex.I * (chi0 : ℂ)) *
          positiveRestEvolution time component)) =
      standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
        (positiveRestEvolution time)
  negativeRestEquation : ∀ time,
    (fun component => Complex.I *
        ((Complex.I * (chi0 : ℂ)) *
          negativeRestEvolution time component)) =
      standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
        (negativeRestEvolution time)
  relativePhase : ∀ time,
    restBranchRelativePhase time =
      Complex.exp (-Complex.I * ((2 * chi0 : ℝ) : ℂ) * time)
  exactNativeFrequencies :
    nativeRestAngularFrequency = 19 ∧
      nativeBranchBeatAngularFrequency = 38
  exactPeriods :
    positiveRestPhase (nativeRestClockPeriod : ℂ) = 1 ∧
      negativeRestPhase (nativeRestClockPeriod : ℂ) = 1 ∧
      restBranchRelativePhase (nativeBranchBeatPeriod : ℂ) = 1
  nativeScales :
    nativeInverseMassScale = 1 / 19 ∧
      nativeReducedComptonLength = Real.sqrt 12 / 19

theorem dirac021_action_derived_rest_clock :
    Dirac021RestClockCertificate where
  previousGate := dirac020_coherent_spatial_transport
  nativeRestFrequency := continuum_rest_frequency_is_chi0
  positiveRestEnergy := positive_rest_state_has_native_energy
  negativeRestEnergy := negative_rest_state_has_native_energy
  positiveRestEquation := positive_rest_evolution_satisfies_dirac
  negativeRestEquation := negative_rest_evolution_satisfies_dirac
  relativePhase := rest_branch_relative_phase_is_doubled
  exactNativeFrequencies :=
    ⟨native_rest_angular_frequency_eq_nineteen,
      native_branch_beat_angular_frequency_eq_thirty_eight⟩
  exactPeriods :=
    ⟨positive_rest_phase_returns_after_native_clock,
      negative_rest_phase_returns_after_native_clock,
      rest_branch_coherence_returns_after_native_beat_period⟩
  nativeScales :=
    ⟨native_inverse_mass_scale_eq_one_over_nineteen,
      native_reduced_compton_length_eq_sqrt_twelve_over_nineteen⟩

end
end LeanDirac

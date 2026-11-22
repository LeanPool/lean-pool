/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CanonicalSpectralReadout
public import LeanPool.LatticeDiracDerivation.V2.FinitePeriodicSector
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumVerletTime
public import LeanPool.LatticeDiracDerivation.V2.PositionSpaceFreeDirac

/-!
# One spectral readout through the exact native chain

This file composes the canonical positive/negative-frequency readout with the
finite-C19 action generator, the actual centered two-layer update, and finite
Fourier fields.  No new native operator is introduced.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Mode : Type*}

open Complex BigOperators Filter Topology
noncomputable section

/-- Spectral spinor coordinates with the momentum scaled by the C19 continuum speed. -/
def canonicalSpectralMomentumReadout
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  canonicalSpectralReadout mass energy
    (c19ContinuumSpeed * momentum 0)
    (c19ContinuumSpeed * momentum 1)
    (c19ContinuumSpeed * momentum 2) phase

theorem canonical_spectral_readout_additive
    (mass energy px py pz : ℝ)
    (first second : UniformTwoChannelPhase) :
    canonicalSpectralReadout mass energy px py pz
        (fun component => first.1 component + second.1 component,
         fun component => first.2 component + second.2 component) =
      fun component =>
        canonicalSpectralReadout mass energy px py pz first component +
          canonicalSpectralReadout mass energy px py pz second component := by
  funext component
  fin_cases component <;>
    simp [canonicalSpectralReadout, nativePositiveAmplitude,
      nativeNegativeAmplitude, normalizedPositiveFrequencyEmbedding,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial] <;>
    ring

theorem canonical_spectral_readout_scale
    (mass energy px py pz : ℝ) (scalar : ℂ)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralReadout mass energy px py pz
        (uniformTwoChannelScale scalar phase) =
      fun component => scalar *
        canonicalSpectralReadout mass energy px py pz phase component := by
  funext component
  fin_cases component <;>
    simp [canonicalSpectralReadout, nativePositiveAmplitude,
      nativeNegativeAmplitude, uniformTwoChannelScale,
      normalizedPositiveFrequencyEmbedding,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial] <;>
    ring

theorem canonical_spectral_momentum_readout_additive
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (first second : UniformTwoChannelPhase) :
    canonicalSpectralMomentumReadout mass energy momentum
        (fun component => first.1 component + second.1 component,
         fun component => first.2 component + second.2 component) =
      fun component =>
        canonicalSpectralMomentumReadout mass energy momentum first component +
          canonicalSpectralMomentumReadout mass energy momentum second component := by
  unfold canonicalSpectralMomentumReadout
  exact canonical_spectral_readout_additive _ _ _ _ _ first second

theorem canonical_spectral_continuum_generator_exact
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (henergy : energy ≠ 0) (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum 0) ^ 2 +
      (c19ContinuumSpeed * momentum 1) ^ 2 +
      (c19ContinuumSpeed * momentum 2) ^ 2)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralMomentumReadout mass energy momentum
        (uniformVacuumContinuumGenerator mass momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (canonicalSpectralMomentumReadout mass energy momentum phase)
          component := by
  unfold canonicalSpectralMomentumReadout
  rw [uniform_continuum_generator_is_kg]
  exact canonical_spectral_readout_intertwines mass energy
    (c19ContinuumSpeed * momentum 0)
    (c19ContinuumSpeed * momentum 1)
    (c19ContinuumSpeed * momentum 2) henergy hdenom hshell phase

/-- The exact finite-C19 generator, not its continuum replacement, passes
through the same canonical spectral map. -/
theorem canonical_spectral_native_generator_exact
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (henergy : energy ≠ 0) (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum 0) ^ 2 +
      (c19ContinuumSpeed * momentum 1) ^ 2 +
      (c19ContinuumSpeed * momentum 2) ^ 2)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralMomentumReadout mass energy momentum
        (uniformVacuumNativeGenerator mass momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (canonicalSpectralMomentumReadout mass energy momentum phase)
          component +
        canonicalSpectralMomentumReadout mass energy momentum
          (uniformNativeSpatialDefectPhase momentum phase) component := by
  rw [uniform_native_generator_exact_defect]
  rw [canonical_spectral_momentum_readout_additive]
  rw [canonical_spectral_continuum_generator_exact
    mass energy momentum henergy hdenom hshell]

/-- The finite periodic action sector and the spectral Dirac diagram use the
same native phase.  The first equality has the full state/velocity action
provenance; the second is its four-component image. -/
theorem periodic_full_native_action_to_canonical_spectral
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (mass energy : ℝ) (hmass : mass ≠ 0)
    (henergy : energy ≠ 0) (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum 0) ^ 2 +
      (c19ContinuumSpeed * momentum 1) ^ 2 +
      (c19ContinuumSpeed * momentum 2) ^ 2)
    (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) :
    periodicNativeTransverseTangentGenerator mass
        (periodicFullNativeTangentEmbed mode phase) =
      periodicFullNativeTangentEmbed mode
        (uniformVacuumNativeGenerator mass momentum phase) ∧
    canonicalSpectralMomentumReadout mass energy momentum
        (uniformVacuumNativeGenerator mass momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (canonicalSpectralMomentumReadout mass energy momentum phase)
          component +
        canonicalSpectralMomentumReadout mass energy momentum
          (uniformNativeSpatialDefectPhase momentum phase) component := by
  have haction := periodic_full_native_action_generator_intertwines
    mass hmass mode phase
  exact ⟨haction.1,
    canonical_spectral_native_generator_exact
      mass energy momentum henergy hdenom hshell phase⟩

/-- The exact centered difference quotient is the spectral Dirac flow plus
the displayed joint time/C19 defect under the same readout. -/
theorem canonical_spectral_centered_update_exact
    (mass energy dt : ℝ) (momentum : LatticeMomentum)
    (henergy : energy ≠ 0) (hdenom : energy + mass ≠ 0)
    (hdt : dt ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum 0) ^ 2 +
      (c19ContinuumSpeed * momentum 1) ^ 2 +
      (c19ContinuumSpeed * momentum 2) ^ 2)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralMomentumReadout mass energy momentum
        (uniformCenteredDifferenceQuotient mass dt momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (canonicalSpectralMomentumReadout mass energy momentum phase)
          component +
        canonicalSpectralMomentumReadout mass energy momentum
          (uniformCenteredDiracDefect mass dt momentum phase) component := by
  rw [uniform_centered_difference_quotient_splits mass dt hdt]
  rw [canonical_spectral_momentum_readout_additive]
  rw [canonical_spectral_continuum_generator_exact
    mass energy momentum henergy hdenom hshell]

/-- The actual velocity-Verlet phase step passes through the same spectral
map.  Its only local discrepancy from the native second-order Taylor step is
the already-derived cubic defect. -/
theorem canonical_spectral_verlet_step_exact
    (mass energy dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralMomentumReadout mass energy momentum
        (uniformVerletPhaseStep mass dt momentum phase) =
      fun component =>
        canonicalSpectralMomentumReadout mass energy momentum
            (uniformNativeTaylor2 mass dt momentum phase) component +
          canonicalSpectralMomentumReadout mass energy momentum
            (uniformVerletLocalDefect mass dt momentum phase) component := by
  rw [uniform_verlet_step_is_second_order]
  unfold canonicalSpectralMomentumReadout
  exact canonical_spectral_readout_additive _ _ _ _ _ _ _

theorem canonical_spectral_verlet_local_defect_scale
    (mass energy dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralMomentumReadout mass energy momentum
        (uniformVerletLocalDefect mass dt momentum phase) =
      fun component => ((dt ^ 3 : ℝ) : ℂ) *
        canonicalSpectralMomentumReadout mass energy momentum
          (uniformVerletLocalDefect mass 1 momentum phase) component := by
  funext component
  fin_cases component <;>
    simp [canonicalSpectralMomentumReadout, canonicalSpectralReadout,
      nativePositiveAmplitude, nativeNegativeAmplitude,
      normalizedPositiveFrequencyEmbedding,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial,
      uniformVerletLocalDefect] <;>
    ring

theorem canonical_spectral_verlet_local_defect_is_little_o_dt_sq
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) (component : Fin 4) :
    Tendsto
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          canonicalSpectralMomentumReadout mass energy momentum
              (uniformVerletLocalDefect mass dt momentum phase) component /
            ((dt ^ 2 : ℝ) : ℂ))
      (nhds 0) (nhds 0) := by
  have hfun :
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          canonicalSpectralMomentumReadout mass energy momentum
              (uniformVerletLocalDefect mass dt momentum phase) component /
            ((dt ^ 2 : ℝ) : ℂ)) =
      (fun dt : ℝ => (dt : ℂ) *
        canonicalSpectralMomentumReadout mass energy momentum
          (uniformVerletLocalDefect mass 1 momentum phase) component) := by
    funext dt
    by_cases hdt : dt = 0
    · subst dt
      simp
    · rw [ite_eq_right hdt,
        congrFun (canonical_spectral_verlet_local_defect_scale
          mass energy dt momentum phase) component]
      push_cast
      field_simp [hdt]
  rw [hfun]
  simpa using ((Complex.continuous_ofReal.tendsto 0).mul
    tendsto_const_nhds)

/-- Synthesize the spinor field from finitely many canonical spectral modes. -/
def finiteSpectralDiracField [Fintype Mode]
    (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      canonicalSpectralMomentumReadout mass (energy mode)
        (momentum mode) (phase mode) component

/-- Apply the free Dirac generator to each mode before synthesis. -/
def finiteSpectralDiracTimeDerivative [Fintype Mode]
    (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      canonicalSpectralMomentumReadout mass (energy mode) (momentum mode)
        (uniformVacuumContinuumGenerator mass
          (momentum mode) (phase mode)) component

/-- Synthesize the native lattice time generator in the same spinor coordinates. -/
def finiteSpectralNativeTimeDerivative [Fintype Mode]
    (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      canonicalSpectralMomentumReadout mass (energy mode) (momentum mode)
        (uniformVacuumNativeGenerator mass
          (momentum mode) (phase mode)) component

/-- Synthesize the exact spatial defect after the canonical change of coordinates. -/
def finiteSpectralMappedC19Remainder [Fintype Mode]
    (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      canonicalSpectralMomentumReadout mass (energy mode) (momentum mode)
        (uniformNativeSpatialDefectPhase
          (momentum mode) (phase mode)) component

/-- Differentiate the finite spinor Fourier sum in the specified coordinate direction. -/
def finiteSpectralDiracSpatialDerivative [Fintype Mode]
    (axis : Fin 3) (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    I * ((momentum mode axis : ℝ) : ℂ) *
      cubicLatticeCharacter (momentum mode) site *
        canonicalSpectralMomentumReadout mass (energy mode)
          (momentum mode) (phase mode) component

theorem finite_spectral_tangent_obeys_position_space_dirac [Fintype Mode]
    (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (henergy : ∀ mode, energy mode ≠ 0)
    (hdenom : ∀ mode, energy mode + mass ≠ 0)
    (hshell : ∀ mode, (energy mode) ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum mode 0) ^ 2 +
      (c19ContinuumSpeed * momentum mode 1) ^ 2 +
      (c19ContinuumSpeed * momentum mode 2) ^ 2)
    (site : InfiniteCubicSite) :
    finiteSpectralDiracTimeDerivative mass energy momentum phase site =
      cubicalDiracTimeDerivative mass
        (finiteSpectralDiracField mass energy momentum phase site)
        (fun axis =>
          finiteSpectralDiracSpatialDerivative axis mass energy
            momentum phase site) := by
  rw [show finiteSpectralDiracTimeDerivative
      mass energy momentum phase site =
      fun component => ∑ mode,
        cubicLatticeCharacter (momentum mode) site *
          cubicalDiracTimeDerivative mass
            (canonicalSpectralMomentumReadout mass (energy mode)
              (momentum mode) (phase mode))
            (uniformPlaneWaveSpatialDerivative (momentum mode)
              (canonicalSpectralMomentumReadout mass (energy mode)
                (momentum mode) (phase mode))) component by
    funext component
    unfold finiteSpectralDiracTimeDerivative
    apply Finset.sum_congr rfl
    intro mode _
    have hgenerator := canonical_spectral_continuum_generator_exact
      mass (energy mode) (momentum mode)
      (henergy mode) (hdenom mode) (hshell mode) (phase mode)
    have hposition := cubical_standard_hamiltonian_is_position_dirac
      mass (momentum mode)
        (canonicalSpectralMomentumReadout mass (energy mode)
          (momentum mode) (phase mode))
    calc
      cubicLatticeCharacter (momentum mode) site *
          canonicalSpectralMomentumReadout mass (energy mode)
            (momentum mode)
            (uniformVacuumContinuumGenerator mass
              (momentum mode) (phase mode)) component =
        cubicLatticeCharacter (momentum mode) site *
          (-I * cubicalStandardHamiltonian (mass : ℂ)
            (uniformContinuumPx (momentum mode))
            (uniformContinuumPy (momentum mode))
            (uniformContinuumPz (momentum mode))
            (canonicalSpectralMomentumReadout mass (energy mode)
              (momentum mode) (phase mode)) component) := by rw [hgenerator]
      _ = cubicLatticeCharacter (momentum mode) site *
          cubicalDiracTimeDerivative mass
            (canonicalSpectralMomentumReadout mass (energy mode)
              (momentum mode) (phase mode))
            (uniformPlaneWaveSpatialDerivative (momentum mode)
              (canonicalSpectralMomentumReadout mass (energy mode)
                (momentum mode) (phase mode))) component := by
                  exact congrArg
                    (fun value =>
                      cubicLatticeCharacter (momentum mode) site * value)
                    (congrFun hposition component)]
  rw [show finiteSpectralDiracField mass energy momentum phase site =
      fun component => ∑ mode,
        (fun component =>
          cubicLatticeCharacter (momentum mode) site *
            canonicalSpectralMomentumReadout mass (energy mode)
              (momentum mode) (phase mode) component) component by rfl]
  rw [show (fun axis => finiteSpectralDiracSpatialDerivative axis mass
      energy momentum phase site) =
      fun axis component => ∑ mode,
        cubicLatticeCharacter (momentum mode) site *
          uniformPlaneWaveSpatialDerivative (momentum mode)
            (canonicalSpectralMomentumReadout mass (energy mode)
              (momentum mode) (phase mode)) axis component by
    funext axis component
    unfold finiteSpectralDiracSpatialDerivative
      uniformPlaneWaveSpatialDerivative
    apply Finset.sum_congr rfl
    intro mode _
    ring]
  rw [cubical_dirac_time_derivative_sum]
  funext component
  apply Finset.sum_congr rfl
  intro mode _
  exact (congrFun (cubical_dirac_time_derivative_mul _ _ _ _) component).symm

theorem finite_spectral_native_time_derivative_splits [Fintype Mode]
    (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    finiteSpectralNativeTimeDerivative mass energy momentum phase site =
      fun component =>
        finiteSpectralDiracTimeDerivative mass energy momentum phase site
            component +
          finiteSpectralMappedC19Remainder mass energy momentum phase site
            component := by
  funext component
  unfold finiteSpectralNativeTimeDerivative
    finiteSpectralDiracTimeDerivative finiteSpectralMappedC19Remainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mode _
  rw [uniform_native_generator_exact_defect]
  rw [canonical_spectral_momentum_readout_additive]
  ring

theorem finite_spectral_native_c19_obeys_position_dirac_with_remainder
    [Fintype Mode]
    (mass : ℝ) (energy : Mode → ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (henergy : ∀ mode, energy mode ≠ 0)
    (hdenom : ∀ mode, energy mode + mass ≠ 0)
    (hshell : ∀ mode, (energy mode) ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum mode 0) ^ 2 +
      (c19ContinuumSpeed * momentum mode 1) ^ 2 +
      (c19ContinuumSpeed * momentum mode 2) ^ 2)
    (site : InfiniteCubicSite) :
    finiteSpectralNativeTimeDerivative mass energy momentum phase site =
      fun component =>
        cubicalDiracTimeDerivative mass
          (finiteSpectralDiracField mass energy momentum phase site)
          (fun axis =>
            finiteSpectralDiracSpatialDerivative axis mass energy
              momentum phase site) component +
        finiteSpectralMappedC19Remainder mass energy momentum phase site
          component := by
  rw [finite_spectral_native_time_derivative_splits]
  rw [finite_spectral_tangent_obeys_position_space_dirac
    mass energy momentum phase henergy hdenom hshell]

end
end LeanDirac.V2

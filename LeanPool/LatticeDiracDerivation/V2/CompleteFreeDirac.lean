/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumVerletDispersion
public import LeanPool.LatticeDiracDerivation.V2.CanonicalSpectralExactChain
public import LeanPool.LatticeDiracDerivation.V2.PositiveFrequencyPacketBridge
public import LeanPool.LatticeDiracDerivation.V2.ReadoutCharacterization
public import LeanPool.LatticeDiracDerivation.V2.FlavorClassification
public import LeanPool.LatticeDiracDerivation.V2.NativeCubicalCompression
public import LeanPool.LatticeDiracDerivation.V2.CovariantFreeDirac

/-!
# Complete scoped free-Dirac theorem

This theorem is entirely mathematical.  It is a tangent/continuum theorem
about the native action at one of its uniform zero-energy vacua.  It is not a
claim that a particular nonlinear localized packet is an electron.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Site : Type} {Mode : Type*}

open Complex Filter Topology
noncomputable section

/-- The nonnegative square root of the native vacuum Hessian is fixed by
the action scale, not fitted to the target equation. -/
theorem canonical_uniform_vacuum_mass_unique
    (mass : ℝ) (hmass : 0 ≤ mass) (hmatch : mass ^ 2 = chi0 ^ 2) :
    mass = chi0 := by
  exact (sq_eq_sq₀ hmass (by norm_num [chi0])).mp hmatch

/-- The canonical native tangent obeys the full four-component free Dirac
equation in momentum space after the single lossless phase-space change of
coordinates derived above. -/
theorem canonical_native_tangent_is_free_dirac
    (momentum : LatticeMomentum) (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac chi0 momentum
        (uniformVacuumContinuumGenerator chi0 momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (chi0 : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac chi0 momentum phase) component := by
  exact uniform_action_tangent_intertwines_cubical_dirac
    chi0 (by norm_num [chi0]) momentum phase

/-- A single spectral normalization maps the complete positive- and
negative-frequency native phase space to the cubical Dirac generator.  This
is the normalization used below for the same-state density/current bridge. -/
theorem canonical_spectral_native_tangent_is_free_dirac
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralReadout mass energy px py pz
        (uniformTwoChannelKleinGordonVector (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ)
          (canonicalSpectralReadout mass energy px py pz phase) component := by
  exact canonical_spectral_readout_intertwines
    mass energy px py pz henergy hdenom hshell phase

/-- Direct, non-metadata theorem joining the actual finite periodic native
action to the covariant free-Dirac equation.  The exact finite-C19 departure
from the covariant equation is displayed and bounded rather than hidden. -/
theorem lfm_periodic_action_mode_to_free_dirac
    {L : ℕ} [NeZero L] (momentum : LatticeMomentum)
    (B : ℝ) (mode : PeriodicC19FourierMode L momentum)
    (phase : UniformTwoChannelPhase) (direction : UniformCell2)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (hsmall : 2 * radius ≤ 1) :
    Function.Injective (periodicFullNativeTangentEmbed mode) ∧
    periodicNativeTransverseTangentGenerator chi0
        (periodicFullNativeTangentEmbed mode phase) =
      periodicFullNativeTangentEmbed mode
        (uniformVacuumNativeGenerator chi0 momentum phase) ∧
    (∀ candidate : UniformTwoChannelPhase → CubicalCell4,
      (∀ nativePhase,
        cubicalStandardPosition (candidate nativePhase) = nativePhase.1) →
      (∀ nativePhase,
        candidate (uniformTwoChannelKleinGordonVector (chi0 : ℂ)
            (uniformContinuumPx momentum)
            (uniformContinuumPy momentum)
            (uniformContinuumPz momentum) nativePhase) =
          fun component =>
            -I * cubicalStandardHamiltonian (chi0 : ℂ)
              (uniformContinuumPx momentum)
              (uniformContinuumPy momentum)
              (uniformContinuumPz momentum)
              (candidate nativePhase) component) →
      candidate = cubicalPhaseReadout (chi0 : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum)) ∧
    (∀ eps longitudinal,
      potentialFirstVariation chi0
        (uniformTransverseState chi0 eps
          (periodicModeField mode (phase.1 0))
          (periodicModeField mode (phase.1 1)))
        (periodicLongitudinalPsiDirection longitudinal)
        (c19Bond (periodicC19Geometry L)) = 0) ∧
    (∀ chiDirection,
      AnalyticHasDerivAt
        (fun eps : ℝ =>
          potentialFirstVariation chi0
            (uniformTransverseState chi0 eps
              (periodicModeField mode (phase.1 0))
              (periodicModeField mode (phase.1 1)))
            (pureChiDirection chiDirection)
            (c19Bond (periodicC19Geometry L))) 0 0) ∧
    periodicTransverseGenerator chi0 (periodicModePhaseEmbed mode phase) =
      periodicModePhaseEmbed mode
        (uniformVacuumNativeGenerator chi0 momentum phase) ∧
    ((∀ (component : Fin 2) (site : PeriodicCubicSite L)
        (testAmplitude : ℂ),
      AnalyticHasDerivAt
        (fun eps : ℝ =>
          potentialFirstVariation chi0
            (periodicTransverseComponentState chi0 eps component
              (periodicModeField mode (phase.1 component)))
            (periodicTransverseComponentDirection component
              (periodicSingleSiteScalarDirection site testAmplitude))
            (c19Bond (periodicC19Geometry L)))
        (-uniformScalarRealPair
          (periodicModeField mode
            ((uniformVacuumModalAcceleration
              chi0 momentum phase.1) component) site)
          testAmplitude) 0) ∧
      Tendsto
          (fun eps : ℝ =>
            periodicC19LagrangianTangentQuotient
              chi0 B eps mode phase.1 phase.2)
          (nhds 0)
          (nhds (2 * periodicSiteCount L *
            uniformVacuumModalLagrangian
              chi0 momentum phase.1 phase.2)) ∧
      (uniformCell2RealPair
          (uniformVacuumModalAcceleration chi0 momentum phase.1) direction +
        uniformVacuumModalPotentialVariation
          chi0 momentum phase.1 direction = 0)) ∧
    (uniformVacuumNativeGenerator chi0 momentum phase =
      (fun component =>
        (uniformVacuumContinuumGenerator chi0 momentum phase).1 component +
          (uniformNativeSpatialDefectPhase momentum phase).1 component,
       fun component =>
        (uniformVacuumContinuumGenerator chi0 momentum phase).2 component +
          (uniformNativeSpatialDefectPhase momentum phase).2 component)) ∧
    |c19SpatialRemainder momentum| ≤ 40 * radius ^ 4 ∧
    cubicalCovariantDiracResidual chi0
        (uniformActionToStandardDirac chi0 momentum phase)
        (uniformActionToStandardDirac chi0 momentum
          (uniformVacuumContinuumGenerator chi0 momentum phase))
        (uniformPlaneWaveSpatialDerivative momentum
          (uniformActionToStandardDirac chi0 momentum phase)) =
      fun _ => 0 := by
  rcases periodic_full_native_tangent_sector_is_action_invariant
      chi0 (by norm_num [chi0]) mode phase with
    ⟨hinjective, hforce, hlongitudinal, hchi, hinvariant⟩
  refine ⟨hinjective,
    periodic_full_native_tangent_generator_intertwines chi0 mode phase,
    fun candidate hposition hintertwines =>
      cubical_phase_readout_unique_from_intertwining
        (chi0 : ℂ) (uniformContinuumPx momentum)
        (uniformContinuumPy momentum) (uniformContinuumPz momentum)
        (by norm_num [chi0]) candidate hposition hintertwines,
    hlongitudinal, hchi, hinvariant, ⟨hforce,
      periodic_c19_lagrangian_tangent_tends_to_modal
        chi0 B (by norm_num [chi0]) mode phase.1 phase.2,
      uniform_modal_euler_lagrange
        chi0 momentum phase.1 direction⟩,
    uniform_native_generator_exact_defect chi0 momentum phase,
    c19_spatial_remainder_bound momentum radius hradius hmomentum hsmall,
    ?_⟩
  exact (cubical_hamiltonian_iff_covariant_dirac chi0
    (uniformActionToStandardDirac chi0 momentum phase)
    (uniformActionToStandardDirac chi0 momentum
      (uniformVacuumContinuumGenerator chi0 momentum phase))
    (uniformPlaneWaveSpatialDerivative momentum
      (uniformActionToStandardDirac chi0 momentum phase))).mp
      (uniform_readout_tangent_is_position_dirac
        chi0 (by norm_num [chi0]) momentum phase)

theorem canonical_native_phase_readout_bijective
    (momentum : LatticeMomentum) :
    Function.Bijective
      (fun phase : UniformTwoChannelPhase =>
        uniformActionToStandardDirac chi0 momentum phase) := by
  exact uniform_action_to_standard_bijective
    chi0 (by norm_num [chi0]) momentum

/-- Every finite periodic momentum label used by the theorem has a concrete
native C19 character; nonzero modes are not postulated as extra data. -/
def canonicalPeriodicQuantizedMode
    (L : ℕ) [NeZero L] (label : PeriodicCubicMomentum L) :
    PeriodicC19FourierMode L (periodicQuantizedMomentum L label) :=
  periodicC19QuantizedMode L label

/-- Canonical mass is not fitted: the action Hessian supplies `chi0 ^ 2`, and
the positive-frequency convention uniquely selects `chi0`. -/
theorem canonical_native_mass_is_chi0 :
    (0 : ℝ) ≤ chi0 ∧ chi0 ^ 2 = chi0 ^ 2 ∧
      ∀ mass : ℝ, 0 ≤ mass → mass ^ 2 = chi0 ^ 2 → mass = chi0 := by
  exact ⟨by norm_num [chi0], rfl, canonical_uniform_vacuum_mass_unique⟩

/-- The exact finite C19 generator differs from the continuum Dirac square
only by the explicit fourth-order spatial remainder. -/
theorem canonical_native_c19_defect_bound
    (momentum : LatticeMomentum) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (hsmall : 2 * radius ≤ 1) :
    |c19SpatialRemainder momentum| ≤ 40 * radius ^ 4 :=
  c19_spatial_remainder_bound momentum radius hradius hmomentum hsmall

/-- The actual stable two-layer recurrence has an exact all-update modal
solution, and its accumulated angular frequency converges to the frequency
selected by the native action Hessian. -/
theorem lfm_verlet_modal_frequency_converges
    (r : ℝ) (momentum : LatticeMomentum) :
    Tendsto (fun dt : ℝ => uniformVerletAngularFrequency r dt momentum)
        (nhds 0) (nhds (uniformVacuumModalFrequency r momentum)) ∧
    ∀ dt, uniformVerletStable r dt momentum →
      Real.cos (dt * uniformVerletAngularFrequency r dt momentum) =
        1 - uniformVerletStabilityParameter r dt momentum / 2 := by
  exact ⟨uniform_verlet_angular_frequency_tends_to_native r momentum,
    fun dt hstable =>
      uniform_verlet_exact_dispersion r dt momentum hstable⟩

/-- The temporal part of the actual centered native update vanishes through
the same phase-space readout used by the Dirac intertwining. The finite-C19
spatial remainder is controlled separately above. -/
theorem canonical_centered_temporal_defect_tends_to_zero
    (momentum : LatticeMomentum) (phase : UniformTwoChannelPhase)
    (component : Fin 4) :
    Tendsto
      (fun dt : ℝ =>
        uniformActionToStandardDirac chi0 momentum
          (uniformCenteredTemporalDefect chi0 dt momentum phase) component)
      (nhds 0) (nhds 0) :=
  uniform_centered_temporal_defect_readout_tends_to_zero
    chi0 momentum phase component

/-- Using the acceleration-corrected velocity reconstructed from the same two
committed layers, the unchanged centered recurrence has a cubic one-step
defect.  Hence its phase-space evolution is second-order in time. -/
theorem canonical_verlet_local_defect_is_little_o_dt_sq
    (momentum : LatticeMomentum) (phase : UniformTwoChannelPhase)
    (component : Fin 4) :
    Tendsto
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          uniformActionToStandardDirac chi0 momentum
              (uniformVerletLocalDefect chi0 dt momentum phase) component /
            ((dt ^ 2 : ℝ) : ℂ))
      (nhds 0) (nhds 0) :=
  uniform_verlet_local_defect_is_little_o_dt_sq
    chi0 momentum phase component

/-- The same phase-space coordinates carry a positive density and the
momentum-response current, and they obey continuity on the native
action-derived tangent flow. -/
theorem canonical_phase_space_density_current_continuity
    (momentum : LatticeMomentum) (phase : UniformTwoChannelPhase) :
    cubicalCell4DensityDerivative
        (uniformActionToStandardDirac chi0 momentum phase)
        (uniformActionToStandardDirac chi0 momentum
          (uniformVacuumContinuumGenerator chi0 momentum phase)) +
      cubicalCurrentDivergence
        (uniformActionToStandardDirac chi0 momentum phase)
        (uniformPlaneWaveSpatialDerivative momentum
          (uniformActionToStandardDirac chi0 momentum phase)) = 0 := by
  exact uniform_action_readout_local_continuity
    chi0 (by norm_num [chi0]) momentum phase

/-- The mode theorem reconstructs the displayed position-space Dirac PDE for
every finite Fourier field. -/
theorem canonical_finite_fields_obey_position_space_dirac [Fintype Mode]
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    finiteDiracTimeDerivative chi0 momentum phase site =
      cubicalDiracTimeDerivative chi0
        (finiteDiracField chi0 momentum phase site)
        (fun axis =>
          finiteDiracSpatialDerivative axis chi0 momentum phase site) := by
  exact finite_native_tangent_obeys_position_space_dirac
    chi0 (by norm_num [chi0]) momentum phase site

/-- The same finite Fourier fields satisfy the covariant equation
`(i gamma^mu partial_mu - chi0) psi = 0`, with every gamma operator derived
from the cubical incidence root. -/
theorem canonical_finite_fields_obey_covariant_dirac [Fintype Mode]
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    cubicalCovariantDiracResidual chi0
        (finiteDiracField chi0 momentum phase site)
        (finiteDiracTimeDerivative chi0 momentum phase site)
        (fun axis =>
          finiteDiracSpatialDerivative axis chi0 momentum phase site) =
      fun _ => 0 := by
  exact (cubical_hamiltonian_iff_covariant_dirac chi0
    (finiteDiracField chi0 momentum phase site)
    (finiteDiracTimeDerivative chi0 momentum phase site)
    (fun axis =>
      finiteDiracSpatialDerivative axis chi0 momentum phase site)).mp
        (canonical_finite_fields_obey_position_space_dirac
          momentum phase site)

/-- Before the spatial limit is taken, the exact native C19 field equation is
the same position-space Dirac equation plus the displayed C19 remainder. -/
theorem canonical_finite_c19_fields_obey_dirac_with_remainder [Fintype Mode]
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    finiteNativeDiracTimeDerivative chi0 momentum phase site =
      fun component =>
        cubicalDiracTimeDerivative chi0
          (finiteDiracField chi0 momentum phase site)
          (fun axis =>
            finiteDiracSpatialDerivative axis chi0 momentum phase site)
          component +
        finiteMappedC19Remainder chi0 momentum phase site component := by
  exact finite_native_c19_obeys_position_dirac_with_remainder
    chi0 (by norm_num [chi0]) momentum phase site

/-- The stronger identification of the positive Dirac density with the
second-order U(1) Noether charge for arbitrary mixed-frequency data is false.
The theorem records the exact counterexample rather than hiding the scope. -/
theorem canonical_noether_scope_is_positive_frequency_only :
    uniformNativePhaseDensity uniformNoetherMismatchPhase.1
        uniformNoetherMismatchPhase.2 = 0 ∧
      uniformPhaseSpaceDensity 1 (fun _ => 0)
        uniformNoetherMismatchPhase = 2 :=
  uniform_native_noether_is_not_arbitrary_dirac_density

/-- On the native positive-frequency phase `(q,-iE q)`, the same canonical
spectral readout used by the evolution theorem is exactly the normalized
positive-energy spinor.  Its density and all three currents therefore refer
to the same native state, rather than to a separately normalized auxiliary
coordinate. -/
theorem lfm_canonical_spectral_positive_mode_has_density_current
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    let nativePhase :=
      nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)
    canonicalSpectralReadout mass energy px py pz nativePhase =
        normalizedPositiveFrequencyEmbedding mass energy px py pz q ∧
      cubicalCell4Density
          (canonicalSpectralReadout mass energy px py pz nativePhase) =
        -uniformNativePhaseDensity nativePhase.1 nativePhase.2 ∧
      ∀ axis,
        cubicalDiracCurrent axis
            (canonicalSpectralReadout mass energy px py pz nativePhase) =
          c19ContinuumSpeed *
            (fun axis : Fin 3 =>
              if axis = 0 then px else if axis = 1 then py else pz) axis *
            uniformCell2Density q := by
  dsimp only
  have hread := canonical_spectral_readout_positive_phase
    mass energy px py pz henergy q
  refine ⟨hread, ?_, ?_⟩
  · rw [hread]
    simpa [nativePhaseOfFrequencyAmplitudes] using
      (normalized_density_is_positive_native_u1
        mass energy px py pz hpositive hshell q)
  · intro axis
    rw [hread]
    exact normalized_positive_frequency_current
      mass energy px py pz hpositive hshell q axis

/-- Legacy componentwise bridge for moving positive-frequency data.

The existential preimage in the first conjunct uses the older cubical phase
readout, while the density/current conjuncts use the explicit native phase
`(q, -i E q)`.  The statements are individually useful, but this theorem is
not the canonical same-state linkage.  That stronger linkage is supplied by
`lfm_canonical_spectral_positive_mode_has_density_current`, where one
bijective spectral readout carries evolution, density, and current together.
-/
theorem lfm_positive_frequency_mode_has_dirac_density_current
    (mass energy px py pz : ℝ)
    (hmass : mass ≠ 0)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    (∃ nativePhase : UniformTwoChannelPhase,
      cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
          nativePhase =
        normalizedPositiveFrequencyEmbedding mass energy px py pz q ∧
      uniformTwoChannelKleinGordonVector
          (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) nativePhase =
        uniformTwoChannelScale (-I * (energy : ℂ)) nativePhase) ∧
    cubicalStandardHamiltonian (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      (fun component => (energy : ℂ) *
        normalizedPositiveFrequencyEmbedding mass energy px py pz q component) ∧
    cubicalCell4Density
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      -uniformNativePhaseDensity q
        (fun component => -I * (energy : ℂ) * q component) ∧
    ∀ axis,
      cubicalDiracCurrent axis
          (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
        c19ContinuumSpeed *
          (fun axis : Fin 3 =>
            if axis = 0 then px else if axis = 1 then py else pz) axis *
          uniformCell2Density q := by
  exact ⟨normalized_embedding_has_action_positive_preimage
      mass energy px py pz hmass (ne_of_gt hpositive) hshell q,
    normalized_positive_frequency_is_energy_eigenstate
      mass energy px py pz (ne_of_gt hpositive) hshell q,
    normalized_density_is_positive_native_u1
      mass energy px py pz hpositive hshell q,
    fun axis => normalized_positive_frequency_current
      mass energy px py pz hpositive hshell q axis⟩

/-- Literal native-current bridge at finite C19 spacing.  The current on the
left is the oriented sum of the action-derived bond current; the right is the
positive-energy Dirac current of the same polar sector coordinate plus the
explicit sine-versus-momentum lattice remainder. -/
theorem lfm_positive_frequency_c19_flux_is_dirac_current
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 +
      c19ScaledMomentum momentum 0 ^ 2 +
      c19ScaledMomentum momentum 1 ^ 2 +
      c19ScaledMomentum momentum 2 ^ 2)
    (axis : Fin 3) (q : UniformCell2) :
    uniformNativePositiveAxisFlux momentum axis q =
      cubicalDiracCurrent axis
        (normalizedPositiveFrequencyEmbedding mass energy
          (c19ScaledMomentum momentum 0)
          (c19ScaledMomentum momentum 1)
          (c19ScaledMomentum momentum 2) q) +
        finiteC19CurrentRemainder momentum axis q :=
  native_plane_wave_flux_is_dirac_current_plus_remainder
    mass energy momentum hpositive hshell axis q

/-- The finite-spacing native bond flux is the Dirac current obtained through
the very same canonical spectral readout as the operator theorem, plus the
explicit C19 sine remainder. -/
theorem lfm_canonical_spectral_positive_c19_flux_is_dirac_current
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (henergy : energy ≠ 0)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 +
      c19ScaledMomentum momentum 0 ^ 2 +
      c19ScaledMomentum momentum 1 ^ 2 +
      c19ScaledMomentum momentum 2 ^ 2)
    (axis : Fin 3) (q : UniformCell2) :
    let nativePhase :=
      nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)
    uniformNativePositiveAxisFlux momentum axis q =
      cubicalDiracCurrent axis
        (canonicalSpectralReadout mass energy
          (c19ScaledMomentum momentum 0)
          (c19ScaledMomentum momentum 1)
          (c19ScaledMomentum momentum 2) nativePhase) +
        finiteC19CurrentRemainder momentum axis q := by
  dsimp only
  rw [canonical_spectral_readout_positive_phase
    mass energy
    (c19ScaledMomentum momentum 0)
    (c19ScaledMomentum momentum 1)
    (c19ScaledMomentum momentum 2) henergy q]
  exact native_plane_wave_flux_is_dirac_current_plus_remainder
    mass energy momentum hpositive hshell axis q

/-- The statements connecting the reciprocal action to free Dirac dynamics and its explicit
defects. -/
structure CompleteFreeDiracCertificate : Prop where
  everyQuantizedPeriodicModeExists : ∀ (L : ℕ) [NeZero L]
      (label : PeriodicCubicMomentum L),
    Nonempty (PeriodicC19FourierMode L (periodicQuantizedMomentum L label))
  quantizedPeriodicModesAreComplete : ∀ (L : ℕ) [NeZero L],
    Function.Bijective (periodicQuantizedAddChar L)
  nativeVacuumCritical : ∀ (Site Edge : Type)
      [Fintype Site] [Fintype Edge]
      (direction : State Site) (bond : Edge → Bond Site),
    potentialFirstVariation chi0 (uniformAxialVacuum chi0)
      direction bond = 0
  nativeVacuumMinimum : ∀ (Site Edge : Type)
      [Fintype Site] [Fintype Edge]
      (bond : Edge → Bond Site),
      (∀ edge, 0 ≤ (bond edge).weight) → ∀ state,
      potential chi0 (uniformAxialVacuum chi0) bond ≤
        potential chi0 state bond
  vacuumOrientationDegeneracy : ∀ (Site Edge : Type)
      [Fintype Site] [Fintype Edge]
      (chiField : Site → C3),
    (∀ site, density (chiField site) = chi0 ^ 2) →
      ∀ bond : Edge → Bond Site,
      potential chi0 (zeroPsiVacuumTexture chiField) bond = 0
  noLinearPsiChiCrossSource : ∀ (Site Edge : Type)
      [Fintype Site] [Fintype Edge]
      (chiField psiField : Site → C3) (bond : Edge → Bond Site),
    potentialFirstVariation chi0 (zeroPsiState chiField)
      (purePsiDirection psiField) bond = 0
  reciprocalChiSourceIsQuadratic : ∀ (Site Edge : Type)
      [Fintype Site] [Fintype Edge]
      (eps : ℝ) (f g : Site → ℂ) (chiField : Site → C3)
      (bond : Edge → Bond Site),
    potentialFirstVariation chi0
        (uniformTransverseState chi0 eps f g)
        (pureChiDirection chiField) bond =
      eps ^ 2 * potentialFirstVariation chi0
        (uniformTransverseState chi0 1 f g)
        (pureChiDirection chiField) bond
  longitudinalPsiBondDecouples : ∀ (Site : Type)
      (eps eta : ℝ) (f g h : Site → ℂ) (edge : Bond Site),
    exteriorAreaBond chi0
        (uniformTransverseLongitudinalState chi0 eps eta f g h) edge =
      exteriorAreaBond chi0
        (uniformTransverseState chi0 eps f g) edge
  longitudinalPsiHasNoQuadraticMixing : ∀ (Site : Type)
      (eps eta : ℝ) (f g h : Site → ℂ) (site : Site),
    sitePotential chi0
        (uniformTransverseLongitudinalState chi0 eps eta f g h) site =
      chi0 ^ 2 / 2 *
          (eps ^ 2 * (Complex.normSq (f site) + Complex.normSq (g site)) +
            eta ^ 2 * Complex.normSq (h site)) +
        (eps ^ 2 * (Complex.normSq (f site) + Complex.normSq (g site)) +
          eta ^ 2 * Complex.normSq (h site)) ^ 2 / 4
  nativeActionToDirac : FirstPrinciplesFreeDiracCertificate
  readoutCharacterizedWithoutExtraChoice :
    CubicalReadoutCharacterizationCertificate
  twoFourComponentSectorsAreExhaustive :
    CubicalFlavorClassificationCertificate
  fullNativePeriodicSectorInjective : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum)
      (mode : PeriodicC19FourierMode L momentum),
    Function.Injective (periodicFullNativeTangentEmbed mode)
  fullNativePhaseGeneratorIntertwines : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum) (r : ℝ)
      (mode : PeriodicC19FourierMode L momentum) phase,
    periodicNativeTransverseTangentGenerator r
        (periodicFullNativeTangentEmbed mode phase) =
      periodicFullNativeTangentEmbed mode
        (uniformVacuumNativeGenerator r momentum phase)
  fullNativePeriodicActionForce : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum) (r : ℝ), r ≠ 0 →
      ∀ (mode : PeriodicC19FourierMode L momentum)
        (position : UniformCell2) component site testAmplitude,
      AnalyticHasDerivAt
        (fun eps : ℝ =>
          potentialFirstVariation r
            (periodicTransverseComponentState r eps component
              (periodicModeField mode (position component)))
            (periodicTransverseComponentDirection component
              (periodicSingleSiteScalarDirection site testAmplitude))
            (c19Bond (periodicC19Geometry L)))
        (-uniformScalarRealPair
          (periodicModeField mode
            ((uniformVacuumModalAcceleration r momentum position)
              component) site)
          testAmplitude) 0
  fullNativeLongitudinalLeakageZero : ∀ (L : ℕ) [NeZero L]
      (r eps : ℝ)
      (longitudinal first second : PeriodicCubicSite L → ℂ),
    potentialFirstVariation r
        (uniformTransverseState r eps first second)
        (periodicLongitudinalPsiDirection longitudinal)
        (c19Bond (periodicC19Geometry L)) = 0
  fullNativeChiLeakageZero : ∀ (L : ℕ) [NeZero L]
      (r : ℝ) (first second : PeriodicCubicSite L → ℂ)
      (chiDirection : PeriodicCubicSite L → C3),
    AnalyticHasDerivAt
      (fun eps : ℝ =>
        potentialFirstVariation r
          (uniformTransverseState r eps first second)
          (pureChiDirection chiDirection)
          (c19Bond (periodicC19Geometry L))) 0 0
  fullNativePeriodicModeInvariant : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum) (r : ℝ)
      (mode : PeriodicC19FourierMode L momentum) phase,
    periodicTransverseGenerator r (periodicModePhaseEmbed mode phase) =
      periodicModePhaseEmbed mode
        (uniformVacuumNativeGenerator r momentum phase)
  covariantCliffordAndEquation : CovariantFreeDiracCertificate
  canonicalEquation : ∀ momentum phase,
    uniformActionToStandardDirac chi0 momentum
        (uniformVacuumContinuumGenerator chi0 momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (chi0 : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac chi0 momentum phase) component
  exactNativeCubicalCompressionMinus : ∀ momentum phase,
    nativeCubicalPhaseEmbedMinus chi0 momentum
        (uniformVacuumNativeGenerator chi0 momentum phase) =
      fun corner =>
        -I * cubicalNativeHamiltonian (chi0 : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (nativeCubicalPhaseEmbedMinus chi0 momentum phase) corner +
        nativeCubicalSpatialDefectMinus chi0 momentum phase corner
  exactNativeCubicalCompressionPlus : ∀ momentum phase,
    nativeCubicalPhaseEmbedPlus chi0 momentum
        (uniformVacuumNativeGenerator chi0 momentum phase) =
      fun corner =>
        -I * cubicalNativeHamiltonian (chi0 : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (nativeCubicalPhaseEmbedPlus chi0 momentum phase) corner +
        nativeCubicalSpatialDefectPlus chi0 momentum phase corner
  losslessCoordinates : ∀ momentum,
    Function.Bijective
      (fun phase : UniformTwoChannelPhase =>
        uniformActionToStandardDirac chi0 momentum phase)
  canonicalSpectralCoordinates : ∀ mass energy px py pz,
    energy ≠ 0 → 0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    Function.Bijective
      (canonicalSpectralReadout mass energy px py pz)
  canonicalSpectralGenerator : ∀ mass energy px py pz,
    energy ≠ 0 → energy + mass ≠ 0 →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    ∀ phase,
    canonicalSpectralReadout mass energy px py pz
        (uniformTwoChannelKleinGordonVector (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ)
          (canonicalSpectralReadout mass energy px py pz phase) component
  canonicalSpectralActionC19 : ∀ (L : ℕ) [NeZero L]
      (momentum : LatticeMomentum) (mass energy : ℝ),
    mass ≠ 0 → energy ≠ 0 → energy + mass ≠ 0 →
    energy ^ 2 = mass ^ 2 +
      c19ScaledMomentum momentum 0 ^ 2 +
      c19ScaledMomentum momentum 1 ^ 2 +
      c19ScaledMomentum momentum 2 ^ 2 →
    ∀ (mode : PeriodicC19FourierMode L momentum) phase,
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
          (uniformNativeSpatialDefectPhase momentum phase) component
  canonicalSpectralCenteredUpdate : ∀ mass energy dt momentum,
    energy ≠ 0 → energy + mass ≠ 0 → dt ≠ 0 →
    energy ^ 2 = mass ^ 2 +
      c19ScaledMomentum momentum 0 ^ 2 +
      c19ScaledMomentum momentum 1 ^ 2 +
      c19ScaledMomentum momentum 2 ^ 2 →
    ∀ phase,
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
          (uniformCenteredDiracDefect mass dt momentum phase) component
  canonicalSpectralVerletDefectLimit : ∀ mass energy momentum phase component,
    Tendsto
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          canonicalSpectralMomentumReadout mass energy momentum
              (uniformVerletLocalDefect mass dt momentum phase) component /
            ((dt ^ 2 : ℝ) : ℂ))
      (nhds 0) (nhds 0)
  massFromNativeVacuum :
    ∀ mass : ℝ, 0 ≤ mass → mass ^ 2 = chi0 ^ 2 → mass = chi0
  spatialErrorBound : ∀ momentum radius,
    0 ≤ radius →
    (∀ axis, |momentum axis| ≤ radius) →
    2 * radius ≤ 1 →
    |c19SpatialRemainder momentum| ≤ 40 * radius ^ 4
  sameReadoutCenteredUpdate : ∀ (r dt : ℝ), r ≠ 0 → dt ≠ 0 →
      ∀ momentum phase,
    uniformActionToStandardDirac r momentum
        (uniformCenteredDifferenceQuotient r dt momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase) component +
        uniformActionToStandardDirac r momentum
          (uniformCenteredDiracDefect r dt momentum phase) component
  centeredTemporalDefectLimit : ∀ momentum phase component,
    Tendsto
      (fun dt : ℝ =>
        uniformActionToStandardDirac chi0 momentum
          (uniformCenteredTemporalDefect chi0 dt momentum phase) component)
      (nhds 0) (nhds 0)
  centeredPositionIsVerlet : ∀ dt momentum phase,
    uniformVerletNext chi0 dt momentum phase = fun component =>
      2 * phase.1 component -
        uniformVerletPrevious chi0 dt momentum phase component -
        (dt ^ 2 * uniformVacuumModalSquare chi0 momentum : ℝ) *
          phase.1 component
  centeredPhaseStepSecondOrder : ∀ dt momentum phase,
    uniformVerletPhaseStep chi0 dt momentum phase =
      (fun component =>
          (uniformNativeTaylor2 chi0 dt momentum phase).1 component +
            (uniformVerletLocalDefect chi0 dt momentum phase).1 component,
        fun component =>
          (uniformNativeTaylor2 chi0 dt momentum phase).2 component +
            (uniformVerletLocalDefect chi0 dt momentum phase).2 component)
  centeredLocalDefectLittleO : ∀ momentum phase component,
    Tendsto
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          uniformActionToStandardDirac chi0 momentum
              (uniformVerletLocalDefect chi0 dt momentum phase) component /
            ((dt ^ 2 : ℝ) : ℂ))
      (nhds 0) (nhds 0)
  centeredUpdateStableEnergy : ∀ r dt momentum phase,
    uniformVerletModifiedEnergy r dt momentum
        (uniformVerletPhaseStep r dt momentum phase) =
      uniformVerletModifiedEnergy r dt momentum phase
  centeredUpdateStableEveryIteration : ∀ r dt momentum n phase,
    uniformVerletModifiedEnergy r dt momentum
        (uniformVerletIterate r dt momentum n phase) =
      uniformVerletModifiedEnergy r dt momentum phase
  verletModalFrequencyLimit : ∀ r momentum,
    Tendsto (fun dt : ℝ => uniformVerletAngularFrequency r dt momentum)
      (nhds 0) (nhds (uniformVacuumModalFrequency r momentum))
  verletExactStableDispersion : ∀ r dt momentum,
    uniformVerletStable r dt momentum →
    Real.cos (dt * uniformVerletAngularFrequency r dt momentum) =
      1 - uniformVerletStabilityParameter r dt momentum / 2
  verletExactAllIterationMode : ∀ r dt momentum,
    uniformVerletStable r dt momentum → ∀ amplitude n,
    uniformVerletCharacteristicRoot r dt momentum ^ (n + 2) * amplitude =
      (2 - uniformVerletStabilityParameter r dt momentum : ℝ) *
          (uniformVerletCharacteristicRoot r dt momentum ^ (n + 1) *
            amplitude) -
        uniformVerletCharacteristicRoot r dt momentum ^ n * amplitude
  sameReadoutNativeContinuity : ∀ momentum phase,
    cubicalCell4DensityDerivative
        (uniformActionToStandardDirac chi0 momentum phase)
        (uniformActionToStandardDirac chi0 momentum
          (uniformVacuumContinuumGenerator chi0 momentum phase)) +
      cubicalCurrentDivergence
        (uniformActionToStandardDirac chi0 momentum phase)
        (uniformPlaneWaveSpatialDerivative momentum
          (uniformActionToStandardDirac chi0 momentum phase)) = 0
  positionSpaceEquation : ∀ (Mode : Type) [Fintype Mode]
      (momentum : Mode → LatticeMomentum)
      (phase : Mode → UniformTwoChannelPhase)
      (site : InfiniteCubicSite),
    finiteDiracTimeDerivative chi0 momentum phase site =
      cubicalDiracTimeDerivative chi0
        (finiteDiracField chi0 momentum phase site)
        (fun axis =>
          finiteDiracSpatialDerivative axis chi0 momentum phase site)
  covariantPositionSpaceEquation : ∀ (Mode : Type) [Fintype Mode]
      (momentum : Mode → LatticeMomentum)
      (phase : Mode → UniformTwoChannelPhase)
      (site : InfiniteCubicSite),
    cubicalCovariantDiracResidual chi0
        (finiteDiracField chi0 momentum phase site)
        (finiteDiracTimeDerivative chi0 momentum phase site)
        (fun axis =>
          finiteDiracSpatialDerivative axis chi0 momentum phase site) =
      fun _ => 0
  exactC19PositionSpaceEquation : ∀ (Mode : Type) [Fintype Mode]
      (momentum : Mode → LatticeMomentum)
      (phase : Mode → UniformTwoChannelPhase)
      (site : InfiniteCubicSite),
    finiteNativeDiracTimeDerivative chi0 momentum phase site =
      fun component =>
        cubicalDiracTimeDerivative chi0
          (finiteDiracField chi0 momentum phase site)
          (fun axis =>
            finiteDiracSpatialDerivative axis chi0 momentum phase site)
          component +
        finiteMappedC19Remainder chi0 momentum phase site component
  canonicalSpectralPositionSpaceEquation : ∀ (Mode : Type) [Fintype Mode]
      (mass : ℝ) (energy : Mode → ℝ)
      (momentum : Mode → LatticeMomentum)
      (phase : Mode → UniformTwoChannelPhase),
    (∀ mode, energy mode ≠ 0) →
    (∀ mode, energy mode + mass ≠ 0) →
    (∀ mode, (energy mode) ^ 2 = mass ^ 2 +
      c19ScaledMomentum (momentum mode) 0 ^ 2 +
      c19ScaledMomentum (momentum mode) 1 ^ 2 +
      c19ScaledMomentum (momentum mode) 2 ^ 2) →
    ∀ site,
    finiteSpectralNativeTimeDerivative mass energy momentum phase site =
      fun component =>
        cubicalDiracTimeDerivative mass
          (finiteSpectralDiracField mass energy momentum phase site)
          (fun axis =>
            finiteSpectralDiracSpatialDerivative axis mass energy
              momentum phase site) component +
        finiteSpectralMappedC19Remainder mass energy momentum phase site
          component
  nativeU1Continuity : ∀ (Site : Type) [Fintype Site]
      (massSq : ℝ) (geometry : C19Lattice Site)
      (position velocity : Site → ℂ) (site : Site),
    uniformNativePhaseDensityDerivative
        (position site) (velocity site)
        (uniformScalarTangentAcceleration massSq geometry position site) +
      uniformNativeOutwardCurrentDivergence geometry position site = 0
  positiveRestDensityNoetherBridge : ∀ r, r ≠ 0 → ∀ position,
    r * uniformPhaseSpaceDensity r (fun _ => 0)
        (uniformRestPositivePhase r position) =
      -4 * uniformNativePhaseDensity
        (uniformRestPositivePhase r position).1
        (uniformRestPositivePhase r position).2
  positiveRestCurrentZero : ∀ axis r, r ≠ 0 → ∀ position,
    uniformPhaseSpaceCurrent axis r (fun _ => 0)
      (uniformRestPositivePhase r position) = 0
  positiveFrequencyActionPreimage : ∀ (mass energy px py pz : ℝ),
    mass ≠ 0 → energy + mass ≠ 0 →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    ∀ q,
    ∃ phase : UniformTwoChannelPhase,
      cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) phase =
          normalizedPositiveFrequencyEmbedding mass energy px py pz q ∧
        uniformTwoChannelKleinGordonVector
            (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) phase =
          uniformTwoChannelScale (-I * (energy : ℂ)) phase
  positiveFrequencyNativeDensityBridge : ∀ mass energy px py pz,
    0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    ∀ q,
      cubicalCell4Density
          (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
        -uniformNativePhaseDensity q
          (fun component => -I * (energy : ℂ) * q component)
  positiveFrequencyNativeCurrentBridge : ∀ mass energy px py pz,
    0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    ∀ q axis,
      cubicalDiracCurrent axis
          (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
        c19ContinuumSpeed *
          (fun axis : Fin 3 =>
            if axis = 0 then px else if axis = 1 then py else pz) axis *
          uniformCell2Density q
  canonicalSpectralPositiveSameState : ∀ mass energy px py pz,
    energy ≠ 0 → 0 < energy + mass →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    ∀ q,
    let nativePhase :=
      nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)
    canonicalSpectralReadout mass energy px py pz nativePhase =
        normalizedPositiveFrequencyEmbedding mass energy px py pz q ∧
      cubicalCell4Density
          (canonicalSpectralReadout mass energy px py pz nativePhase) =
        -uniformNativePhaseDensity nativePhase.1 nativePhase.2 ∧
      ∀ axis,
        cubicalDiracCurrent axis
            (canonicalSpectralReadout mass energy px py pz nativePhase) =
          c19ContinuumSpeed *
            (fun axis : Fin 3 =>
              if axis = 0 then px else if axis = 1 then py else pz) axis *
            uniformCell2Density q
  finiteC19CurrentHasExplicitRemainder : ∀ momentum axis q,
    finiteC19PositiveAxisFlux momentum axis q =
      12 * momentum axis * uniformCell2Density q +
        finiteC19CurrentRemainder momentum axis q
  finiteC19CurrentRemainderBound : ∀ momentum axis q radius,
    0 ≤ radius →
    (∀ coordinate, |momentum coordinate| ≤ radius) →
    |finiteC19CurrentRemainder momentum axis q| ≤
      16 * radius ^ 3 * uniformCell2Density q
  finiteC19CurrentRemainderLimit : ∀ (momentum : LatticeMomentum)
      (axis : Fin 3) (q : UniformCell2),
    Tendsto
      (fun scale : ℝ =>
        finiteC19CurrentRemainder
          (fun coordinate => scale * momentum coordinate) axis q)
      (nhds 0) (nhds 0)
  nativeC19FluxIsDiracCurrent : ∀ (mass energy : ℝ)
      (momentum : LatticeMomentum),
    0 < energy + mass →
    energy ^ 2 = mass ^ 2 +
      c19ScaledMomentum momentum 0 ^ 2 +
      c19ScaledMomentum momentum 1 ^ 2 +
      c19ScaledMomentum momentum 2 ^ 2 →
    ∀ axis q,
    uniformNativePositiveAxisFlux momentum axis q =
      cubicalDiracCurrent axis
        (normalizedPositiveFrequencyEmbedding mass energy
          (c19ScaledMomentum momentum 0)
          (c19ScaledMomentum momentum 1)
          (c19ScaledMomentum momentum 2) q) +
        finiteC19CurrentRemainder momentum axis q
  canonicalSpectralC19Flux : ∀ (mass energy : ℝ)
      (momentum : LatticeMomentum),
    energy ≠ 0 → 0 < energy + mass →
    energy ^ 2 = mass ^ 2 +
      c19ScaledMomentum momentum 0 ^ 2 +
      c19ScaledMomentum momentum 1 ^ 2 +
      c19ScaledMomentum momentum 2 ^ 2 →
    ∀ axis q,
    let nativePhase :=
      nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)
    uniformNativePositiveAxisFlux momentum axis q =
      cubicalDiracCurrent axis
        (canonicalSpectralReadout mass energy
          (c19ScaledMomentum momentum 0)
          (c19ScaledMomentum momentum 1)
          (c19ScaledMomentum momentum 2) nativePhase) +
        finiteC19CurrentRemainder momentum axis q
  arbitraryNoetherIdentificationRejected :
    uniformNativePhaseDensity uniformNoetherMismatchPhase.1
        uniformNoetherMismatchPhase.2 = 0 ∧
      uniformPhaseSpaceDensity 1 (fun _ => 0)
        uniformNoetherMismatchPhase = 2
  positivePacketPointwiseOverclaimRejected :
    cubicalCell4Density packetScopeDiracAtOrigin ≠
      -uniformNativePhaseDensity packetScopeNativeAtOrigin.1
        packetScopeNativeAtOrigin.2
  positivePacketIntegratedChargeBridge : ∀ (L : ℕ) [NeZero L]
      (mass : ℝ)
      (energy : PeriodicCubicMomentum L → ℝ)
      (amplitude : PeriodicCubicMomentum L → UniformCell2),
    (∀ mode, energy mode ≠ 0) →
    (∀ mode, 0 < energy mode + mass) →
    (∀ mode, (energy mode) ^ 2 = mass ^ 2 +
      c19ScaledMomentum (periodicQuantizedMomentum L mode) 0 ^ 2 +
      c19ScaledMomentum (periodicQuantizedMomentum L mode) 1 ^ 2 +
      c19ScaledMomentum (periodicQuantizedMomentum L mode) 2 ^ 2) →
    periodicAveragedDiracDensity
        (periodicPositiveSpectralPacket L mass energy amplitude) =
      periodicAveragedNativePositiveCharge L energy amplitude
  positivePacketIntegratedCurrentBridge : ∀ (L : ℕ) [NeZero L]
      (mass : ℝ)
      (energy : PeriodicCubicMomentum L → ℝ)
      (amplitude : PeriodicCubicMomentum L → UniformCell2),
    (∀ mode, energy mode ≠ 0) →
    (∀ mode, 0 < energy mode + mass) →
    (∀ mode, (energy mode) ^ 2 = mass ^ 2 +
      c19ScaledMomentum (periodicQuantizedMomentum L mode) 0 ^ 2 +
      c19ScaledMomentum (periodicQuantizedMomentum L mode) 1 ^ 2 +
      c19ScaledMomentum (periodicQuantizedMomentum L mode) 2 ^ 2) →
    ∀ axis,
    periodicAveragedNativePositiveAxisFlux L axis amplitude =
      periodicAveragedDiracCurrent axis
          (periodicPositiveSpectralPacket L mass energy amplitude) +
        ∑ mode, finiteC19CurrentRemainder
          (periodicQuantizedMomentum L mode) axis (amplitude mode)

theorem complete_first_principles_free_dirac :
    CompleteFreeDiracCertificate where
  everyQuantizedPeriodicModeExists :=
    fun L _ label => ⟨canonicalPeriodicQuantizedMode L label⟩
  quantizedPeriodicModesAreComplete :=
    fun L _ => periodic_quantized_add_char_bijective L
  nativeVacuumCritical := fun _ _ _ _ direction bond =>
    uniform_axial_vacuum_first_variation_zero chi0 direction bond
  nativeVacuumMinimum := fun _ _ _ _ bond hw state =>
    uniform_axial_vacuum_is_global_minimum chi0
      (by norm_num [chi0]) bond hw state
  vacuumOrientationDegeneracy := fun _ _ _ _ chiField hnorm bond =>
    zero_psi_vacuum_texture_potential_zero
      chi0 chiField hnorm bond
  noLinearPsiChiCrossSource := fun _ _ _ _ chiField psiField bond =>
    zero_psi_state_has_no_linear_psi_source
      chi0 chiField psiField bond
  reciprocalChiSourceIsQuadratic :=
    fun _ _ _ _ eps f g chiField bond =>
      uniform_transverse_chi_source_is_quadratic
        chi0 eps f g chiField bond
  longitudinalPsiBondDecouples := fun _ eps eta f g h edge =>
    uniform_transverse_longitudinal_bond_eq
      chi0 eps eta f g h edge
  longitudinalPsiHasNoQuadraticMixing :=
    fun _ eps eta f g h site =>
      uniform_transverse_longitudinal_site_potential
        chi0 eps eta f g h site
  nativeActionToDirac := first_principles_free_dirac
  readoutCharacterizedWithoutExtraChoice :=
    cubical_readout_characterization
  twoFourComponentSectorsAreExhaustive :=
    cubical_flavor_classification
  fullNativePeriodicSectorInjective :=
    fun _ _ _ mode => periodic_full_native_tangent_embed_injective mode
  fullNativePhaseGeneratorIntertwines :=
    fun _ _ _ r mode phase =>
      periodic_full_native_tangent_generator_intertwines r mode phase
  fullNativePeriodicActionForce :=
    fun _ _ _ r hr mode position component site testAmplitude =>
      periodic_c19_action_hessian_mode_force
        r hr mode position component site testAmplitude
  fullNativeLongitudinalLeakageZero :=
    fun _ _ r eps longitudinal first second =>
      periodic_c19_transverse_longitudinal_cross_variation_zero
        r eps longitudinal first second
  fullNativeChiLeakageZero :=
    fun _ _ r first second chiDirection =>
      periodic_c19_transverse_chi_cross_hessian_zero
        r first second chiDirection
  fullNativePeriodicModeInvariant :=
    fun _ _ _ r mode phase =>
      periodic_mode_sector_is_invariant r mode phase
  covariantCliffordAndEquation := covariant_free_dirac
  canonicalEquation := canonical_native_tangent_is_free_dirac
  exactNativeCubicalCompressionMinus := fun momentum phase =>
    native_exact_generator_intertwines_cubical_minus
      chi0 (by norm_num [chi0]) momentum phase
  exactNativeCubicalCompressionPlus := fun momentum phase =>
    native_exact_generator_intertwines_cubical_plus
      chi0 (by norm_num [chi0]) momentum phase
  losslessCoordinates := canonical_native_phase_readout_bijective
  canonicalSpectralCoordinates :=
    fun mass energy px py pz henergy hpositive hshell =>
      canonical_spectral_readout_bijective
        mass energy px py pz henergy hpositive hshell
  canonicalSpectralGenerator :=
    fun mass energy px py pz henergy hdenom hshell phase =>
      canonical_spectral_native_tangent_is_free_dirac
        mass energy px py pz henergy hdenom hshell phase
  canonicalSpectralActionC19 :=
    fun _ _ momentum mass energy hmass henergy hdenom hshell mode phase =>
      periodic_full_native_action_to_canonical_spectral
        mass energy hmass henergy hdenom hshell mode phase
  canonicalSpectralCenteredUpdate :=
    fun mass energy dt momentum henergy hdenom hdt hshell phase =>
      canonical_spectral_centered_update_exact
        mass energy dt momentum henergy hdenom hdt hshell phase
  canonicalSpectralVerletDefectLimit :=
    canonical_spectral_verlet_local_defect_is_little_o_dt_sq
  massFromNativeVacuum := canonical_uniform_vacuum_mass_unique
  spatialErrorBound := c19_spatial_remainder_bound
  sameReadoutCenteredUpdate :=
    uniform_centered_update_through_same_dirac_readout
  centeredTemporalDefectLimit :=
    canonical_centered_temporal_defect_tends_to_zero
  centeredPositionIsVerlet :=
    fun dt momentum phase =>
      uniform_verlet_position_is_centered_recurrence
        chi0 dt momentum phase
  centeredPhaseStepSecondOrder :=
    fun dt momentum phase =>
      uniform_verlet_step_is_second_order chi0 dt momentum phase
  centeredLocalDefectLittleO :=
    canonical_verlet_local_defect_is_little_o_dt_sq
  centeredUpdateStableEnergy :=
    uniform_verlet_modified_energy_invariant
  centeredUpdateStableEveryIteration :=
    uniform_verlet_modified_energy_iterate
  verletModalFrequencyLimit :=
    uniform_verlet_angular_frequency_tends_to_native
  verletExactStableDispersion :=
    uniform_verlet_exact_dispersion
  verletExactAllIterationMode :=
    uniform_verlet_characteristic_solution
  sameReadoutNativeContinuity :=
    canonical_phase_space_density_current_continuity
  positionSpaceEquation := fun _ _ momentum phase site =>
    canonical_finite_fields_obey_position_space_dirac
      momentum phase site
  covariantPositionSpaceEquation := fun _ _ momentum phase site =>
    canonical_finite_fields_obey_covariant_dirac momentum phase site
  exactC19PositionSpaceEquation := fun _ _ momentum phase site =>
    canonical_finite_c19_fields_obey_dirac_with_remainder
      momentum phase site
  canonicalSpectralPositionSpaceEquation :=
    fun _ _ mass energy momentum phase henergy hdenom hshell site =>
      finite_spectral_native_c19_obeys_position_dirac_with_remainder
        mass energy momentum phase henergy hdenom hshell site
  nativeU1Continuity := fun _ _ massSq geometry position velocity site =>
    uniform_native_tangent_local_continuity
      massSq geometry position velocity site
  positiveRestDensityNoetherBridge :=
    uniform_positive_rest_density_noether_bridge
  positiveRestCurrentZero :=
    uniform_positive_rest_dirac_current_zero
  positiveFrequencyActionPreimage :=
    normalized_embedding_has_action_positive_preimage
  positiveFrequencyNativeDensityBridge :=
    normalized_density_is_positive_native_u1
  positiveFrequencyNativeCurrentBridge :=
    normalized_positive_frequency_current
  canonicalSpectralPositiveSameState :=
    lfm_canonical_spectral_positive_mode_has_density_current
  finiteC19CurrentHasExplicitRemainder :=
    finite_c19_flux_is_continuum_plus_remainder
  finiteC19CurrentRemainderBound :=
    finite_c19_current_remainder_bound
  finiteC19CurrentRemainderLimit :=
    finite_c19_current_remainder_tends_to_zero
  nativeC19FluxIsDiracCurrent :=
    native_plane_wave_flux_is_dirac_current_plus_remainder
  canonicalSpectralC19Flux :=
    lfm_canonical_spectral_positive_c19_flux_is_dirac_current
  arbitraryNoetherIdentificationRejected :=
    uniform_native_noether_is_not_arbitrary_dirac_density
  positivePacketPointwiseOverclaimRejected :=
    positive_packet_pointwise_bridge_is_false
  positivePacketIntegratedChargeBridge :=
    periodic_integrated_positive_packet_charge_bridge
  positivePacketIntegratedCurrentBridge :=
    periodic_integrated_positive_packet_current_bridge

end
end LeanDirac.V2

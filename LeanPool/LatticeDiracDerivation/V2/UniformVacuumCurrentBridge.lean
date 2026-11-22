/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.FirstPrinciplesFreeDirac

/-!
# Density and current through the same action-derived cubical readout

This module does not import the historical prepared-background current
certificate. The velocity operator is first derived as the momentum response
of the cubical Hamiltonian. Its density and current are then pulled through
the same bijective phase-space map used by the main operator theorem, and the
continuity identity is proved on the action-derived tangent flow.

The native second-order U(1) current is also derived separately. It is
indefinite on mixed-frequency data and therefore is not silently identified
with the positive four-component density.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Site : Type}

open Complex BigOperators
noncomputable section

/-- The real part of the Hermitian pairing on standard spinors. -/
def cubicalCell4RealPair (z w : CubicalCell4) : ℝ :=
  ∑ component, (star (z component) * w component).re

/-- The sum of squared component moduli of a spinor. -/
def cubicalCell4Density (z : CubicalCell4) : ℝ :=
  ∑ component, Complex.normSq (z component)

theorem cubical_cell4_real_pair_self (z : CubicalCell4) :
    cubicalCell4RealPair z z = cubicalCell4Density z := by
  simp [cubicalCell4RealPair, cubicalCell4Density,
    Complex.normSq, Complex.mul_re, Fin.sum_univ_succ]

/-- The Dirac transport matrix associated with the chosen axis. -/
def cubicalVelocityOperator
    (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  match axis with
  | 0 => fun component =>
      (c19ContinuumSpeed : ℂ) * cubicalStandardAlphaX z component
  | 1 => fun component =>
      (c19ContinuumSpeed : ℂ) * cubicalStandardAlphaY z component
  | _ => fun component =>
      (c19ContinuumSpeed : ℂ) * cubicalStandardAlphaZ z component

theorem cubical_velocity_sum {Mode : Type*} [Fintype Mode]
    (axis : Fin 3) (field : Mode → CubicalCell4) :
    cubicalVelocityOperator axis
        (fun component => ∑ mode, field mode component) =
      fun component => ∑ mode,
        cubicalVelocityOperator axis (field mode) component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalVelocityOperator, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      Finset.mul_sum]

theorem cubical_velocity_mul (axis : Fin 3) (scale : ℂ) (spinor : CubicalCell4) :
    cubicalVelocityOperator axis (fun component => scale * spinor component) =
      fun component => scale * cubicalVelocityOperator axis spinor component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalVelocityOperator, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring

/-- Shift just the specified component of the physical momentum. -/
def cubicalShiftMomentum
    (axis : Fin 3) (delta : ℂ) (px py pz : ℂ) : Fin 3 → ℂ
  | 0 => px + if axis = 0 then delta else 0
  | 1 => py + if axis = 1 then delta else 0
  | _ => pz + if axis = 2 then delta else 0

/-- The current matrix is not supplied independently: it is the exact
momentum derivative of the cube-incidence Hamiltonian. -/
theorem cubical_velocity_is_hamiltonian_momentum_response
    (mass px py pz delta : ℂ) (axis : Fin 3) (z : CubicalCell4) :
    cubicalStandardHamiltonian mass
        (cubicalShiftMomentum axis delta px py pz 0)
        (cubicalShiftMomentum axis delta px py pz 1)
        (cubicalShiftMomentum axis delta px py pz 2) z =
      fun component =>
        cubicalStandardHamiltonian mass px py pz z component +
          delta / (c19ContinuumSpeed : ℂ) *
            cubicalVelocityOperator axis z component := by
  have hc : (c19ContinuumSpeed : ℂ) ≠ 0 := by
    have hpos : 0 < c19ContinuumSpeed := by
      simp [c19ContinuumSpeed]
    exact_mod_cast ne_of_gt hpos
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalShiftMomentum, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalVelocityOperator,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hc] <;> ring

/-- The spinor expectation of the velocity operator for a chosen axis. -/
def cubicalDiracCurrent (axis : Fin 3) (z : CubicalCell4) : ℝ :=
  cubicalCell4RealPair z (cubicalVelocityOperator axis z)

/-- The differential of the spinor density in a given time direction. -/
def cubicalCell4DensityDerivative
    (z zdot : CubicalCell4) : ℝ :=
  2 * cubicalCell4RealPair z zdot

/-- The sum of directional derivatives of the three current components. -/
def cubicalCurrentDivergence
    (z : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) : ℝ :=
  2 * ∑ axis : Fin 3,
    cubicalCell4RealPair z
      (cubicalVelocityOperator axis (spatialDerivative axis))

/-- The mode time evolution given by minus the imaginary unit times the Hamiltonian. -/
def cubicalDiracTimeDerivative
    (mass : ℝ) (z : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) : CubicalCell4 :=
  fun component =>
    -I * (mass : ℂ) * cubicalStandardBeta z component -
      ∑ axis : Fin 3,
        cubicalVelocityOperator axis
          (spatialDerivative axis) component

/-- Local continuity for arbitrary four-component data follows from the
same cube-derived alpha and beta operators. -/
theorem cubical_dirac_local_continuity
    (mass : ℝ) (z : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) :
    cubicalCell4DensityDerivative z
        (cubicalDiracTimeDerivative mass z spatialDerivative) +
      cubicalCurrentDivergence z spatialDerivative = 0 := by
  simp [cubicalCell4DensityDerivative, cubicalCurrentDivergence,
    cubicalDiracTimeDerivative, cubicalCell4RealPair,
    cubicalVelocityOperator, cubicalStandardBeta,
    cubicalStandardAlphaX, cubicalStandardAlphaY,
    cubicalStandardAlphaZ, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

/-- The spatial derivative of a plane wave at the specified physical momentum. -/
def uniformPlaneWaveSpatialDerivative
    (momentum : LatticeMomentum) (z : CubicalCell4) :
    Fin 3 → CubicalCell4 :=
  fun axis component => I * (momentum axis : ℂ) * z component

/-- The Hamiltonian and position-space forms agree for arbitrary
four-component data; this lemma is independent of how the data were read out. -/
theorem cubical_standard_hamiltonian_is_position_dirac
    (mass : ℝ) (momentum : LatticeMomentum) (z : CubicalCell4) :
    (fun component =>
      -I * cubicalStandardHamiltonian (mass : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum) z component) =
      cubicalDiracTimeDerivative mass z
        (uniformPlaneWaveSpatialDerivative momentum z) := by
  funext component
  fin_cases component <;>
    simp [cubicalDiracTimeDerivative, uniformPlaneWaveSpatialDerivative,
      cubicalVelocityOperator, uniformContinuumPx, uniformContinuumPy,
      uniformContinuumPz, c19ScaledMomentum, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, Fin.sum_univ_succ] <;>
    ring_nf

theorem uniform_readout_tangent_is_position_dirac
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (uniformVacuumContinuumGenerator r momentum phase) =
      cubicalDiracTimeDerivative r
        (uniformActionToStandardDirac r momentum phase)
        (uniformPlaneWaveSpatialDerivative momentum
          (uniformActionToStandardDirac r momentum phase)) := by
  rw [uniform_action_tangent_intertwines_cubical_dirac r hr]
  exact cubical_standard_hamiltonian_is_position_dirac r momentum _

/-- The spinor density after reading out the native phase. -/
def uniformPhaseSpaceDensity
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : ℝ :=
  cubicalCell4Density
    (uniformActionToStandardDirac r momentum phase)

/-- The spinor current after reading out the native phase. -/
def uniformPhaseSpaceCurrent
    (axis : Fin 3) (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : ℝ :=
  cubicalDiracCurrent axis
    (uniformActionToStandardDirac r momentum phase)

/-- The continuum generator obeys the Dirac density and current continuity
law after applying the phase-space readout used in the operator theorem.
The exact lattice law is `periodic_c19_native_tangent_local_continuity`. -/
theorem uniform_action_readout_local_continuity
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    cubicalCell4DensityDerivative
        (uniformActionToStandardDirac r momentum phase)
        (uniformActionToStandardDirac r momentum
          (uniformVacuumContinuumGenerator r momentum phase)) +
      cubicalCurrentDivergence
        (uniformActionToStandardDirac r momentum phase)
        (uniformPlaneWaveSpatialDerivative momentum
          (uniformActionToStandardDirac r momentum phase)) = 0 := by
  rw [uniform_readout_tangent_is_position_dirac r hr]
  exact cubical_dirac_local_continuity r _ _

/-! ## The native U(1) current, kept distinct from positive Dirac density -/

/-- The scalar complex phase pairing used in the native continuity identity. -/
def uniformScalarPhasePair (source target : ℂ) : ℝ :=
  (star source * target).im

/-- The native phase charge formed from position and velocity at a site. -/
def uniformNativePhaseDensity (position velocity : UniformCell2) : ℝ :=
  ∑ component, uniformScalarPhasePair
    (position component) (velocity component)

/-- The flux of native phase charge along an oriented weighted bond. -/
def uniformNativeOutwardBondCurrent
    (weight : ℝ) (source target : ℂ) : ℝ :=
  -2 * weight * uniformScalarPhasePair source target

/-- Sum the outward currents over all directed bonds from a site. -/
def uniformNativeOutwardCurrentDivergence
    (geometry : C19Lattice Site)
    (position : Site → ℂ) (site : Site) : ℝ :=
  ∑ direction : C19Neighbor,
    uniformNativeOutwardBondCurrent (c19Weight direction)
      (position site) (position (geometry.neighbor site direction))

/-- The derivative of native charge given velocity and acceleration. -/
def uniformNativePhaseDensityDerivative
    (position velocity acceleration : ℂ) : ℝ :=
  uniformScalarPhasePair velocity velocity +
    uniformScalarPhasePair position acceleration

/-- Exact action-tangent U(1) continuity for one native transverse channel.
The second channel obeys the same identity and the two laws add. -/
theorem uniform_native_tangent_local_continuity
    (massSq : ℝ) (geometry : C19Lattice Site)
    (position velocity : Site → ℂ) (site : Site) :
    uniformNativePhaseDensityDerivative
        (position site) (velocity site)
        (uniformScalarTangentAcceleration massSq geometry position site) +
      uniformNativeOutwardCurrentDivergence geometry position site = 0 := by
  simp [uniformNativePhaseDensityDerivative,
    uniformScalarTangentAcceleration,
    uniformNativeOutwardCurrentDivergence,
    uniformNativeOutwardBondCurrent, uniformScalarPhasePair,
    Complex.mul_im]
  ring_nf
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro direction _
  ring

/-- Native charge continuity for the same force used in the periodic action Hessian. -/
theorem periodic_c19_native_tangent_local_continuity {L : ℕ}
    (r : ℝ) (position velocity : PeriodicCubicSite L → ℂ) (site : PeriodicCubicSite L) :
    uniformNativePhaseDensityDerivative (position site) (velocity site)
        (periodicC19LinearizedAcceleration r position site) +
      uniformNativeOutwardCurrentDivergence (periodicC19Geometry L) position site = 0 :=
  uniform_native_tangent_local_continuity (r ^ 2) (periodicC19Geometry L) position velocity site

/-- The native phase paired with velocity on the positive-frequency branch. -/
def uniformPositiveFrequencyPhase
    (energy : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  (position, fun component => -I * (energy : ℂ) * position component)

theorem uniform_native_u1_positive_frequency
    (energy : ℝ) (position : UniformCell2) :
    uniformNativePhaseDensity
        (uniformPositiveFrequencyPhase energy position).1
        (uniformPositiveFrequencyPhase energy position).2 =
      -energy * uniformCell2Density position := by
  simp [uniformNativePhaseDensity, uniformPositiveFrequencyPhase,
    uniformScalarPhasePair, uniformCell2Density,
    Complex.normSq, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

/-- On the native positive-rest-frequency sector, the positive Dirac density
and the action's U(1) charge density are the same quadratic information up to
the fixed mass/frequency normalization and sign convention.  This is the
largest exact identification available without discarding the negative-
frequency sector. -/
theorem uniform_positive_rest_density_noether_bridge
    (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    r * uniformPhaseSpaceDensity r (fun _ => 0)
        (uniformRestPositivePhase r position) =
      -4 * uniformNativePhaseDensity
        (uniformRestPositivePhase r position).1
        (uniformRestPositivePhase r position).2 := by
  simp [uniformPhaseSpaceDensity, cubicalCell4Density,
    uniformActionToStandardDirac, uniformRestPositivePhase,
    uniformContinuumPx, uniformContinuumPy, uniformContinuumPz, c19ScaledMomentum,
    cubicalPhaseReadout, cubicalPhaseLower, cubicalSpatialLower,
    cubicalStandardSpatial,
    uniformNativePhaseDensity,
    uniformScalarPhasePair, Complex.normSq, Complex.mul_re,
    Complex.mul_im, Fin.sum_univ_succ]
  field_simp [hr]
  ring

theorem uniform_positive_rest_dirac_current_zero
    (axis : Fin 3) (r : ℝ) (hr : r ≠ 0)
    (position : UniformCell2) :
    uniformPhaseSpaceCurrent axis r (fun _ => 0)
      (uniformRestPositivePhase r position) = 0 := by
  fin_cases axis <;>
    simp [uniformPhaseSpaceCurrent, cubicalDiracCurrent,
      cubicalCell4RealPair, cubicalVelocityOperator,
      uniformActionToStandardDirac, uniformRestPositivePhase,
      uniformContinuumPx, uniformContinuumPy, uniformContinuumPz, c19ScaledMomentum,
      cubicalPhaseReadout, cubicalPhaseLower, cubicalSpatialLower,
      cubicalStandardSpatial, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      Complex.mul_re, Complex.mul_im, Fin.sum_univ_succ] <;>
    field_simp [hr] <;> ring

theorem uniform_native_bond_current_zero_at_rest
    (weight : ℝ) (amplitude : ℂ) :
    uniformNativeOutwardBondCurrent weight amplitude amplitude = 0 := by
  have hpair : uniformScalarPhasePair amplitude amplitude = 0 := by
    simp [uniformScalarPhasePair, Complex.mul_im]
    ring
  rw [uniformNativeOutwardBondCurrent, hpair]
  ring

/-- The nonzero position with zero velocity witnessing the arbitrary-phase charge mismatch. -/
def uniformNoetherMismatchPhase : UniformTwoChannelPhase :=
  (fun component => if component = 0 then 1 else 0, fun _ => 0)

/-- Exact obstruction: the native second-order phase charge cannot equal the
positive four-component density on arbitrary mixed-frequency phase space. -/
theorem uniform_native_noether_is_not_arbitrary_dirac_density :
    uniformNativePhaseDensity uniformNoetherMismatchPhase.1
        uniformNoetherMismatchPhase.2 = 0 ∧
      uniformPhaseSpaceDensity 1 (fun _ => 0)
        uniformNoetherMismatchPhase = 2 := by
  constructor
  · norm_num [uniformNativePhaseDensity, uniformNoetherMismatchPhase,
      uniformScalarPhasePair, Complex.mul_im, Fin.sum_univ_succ]
  · unfold uniformPhaseSpaceDensity cubicalCell4Density
    simp [uniformActionToStandardDirac, cubicalPhaseReadout,
      cubicalPhaseLower, cubicalSpatialLower, cubicalUpperEmbedding,
      uniformContinuumPx, uniformContinuumPy, uniformContinuumPz, c19ScaledMomentum,
      uniformNoetherMismatchPhase, cubicalStandardSpatial,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, Complex.normSq, Fin.sum_univ_succ]
    norm_num

/-- The native lattice continuity law, its spinor form, and their frequency-dependent comparison. -/
structure UniformVacuumCurrentCertificate : Prop where
  momentumResponse : ∀ mass px py pz delta axis z,
    cubicalStandardHamiltonian mass
        (cubicalShiftMomentum axis delta px py pz 0)
        (cubicalShiftMomentum axis delta px py pz 1)
        (cubicalShiftMomentum axis delta px py pz 2) z =
      fun component =>
        cubicalStandardHamiltonian mass px py pz z component +
          delta / (c19ContinuumSpeed : ℂ) *
            cubicalVelocityOperator axis z component
  /-- Continuum Dirac continuity expressed in the native phase coordinates. -/
  sameReadoutNativeContinuity : ∀ r, r ≠ 0 → ∀ momentum phase,
    cubicalCell4DensityDerivative
        (uniformActionToStandardDirac r momentum phase)
        (uniformActionToStandardDirac r momentum
          (uniformVacuumContinuumGenerator r momentum phase)) +
      cubicalCurrentDivergence
        (uniformActionToStandardDirac r momentum phase)
        (uniformPlaneWaveSpatialDerivative momentum
          (uniformActionToStandardDirac r momentum phase)) = 0
  nativeU1Continuity : ∀ (Site : Type) [Fintype Site]
      (massSq : ℝ) (geometry : C19Lattice Site)
      (position velocity : Site → ℂ) (site : Site),
    uniformNativePhaseDensityDerivative
        (position site) (velocity site)
        (uniformScalarTangentAcceleration massSq geometry position site) +
      uniformNativeOutwardCurrentDivergence geometry position site = 0
  positiveRestDensityBridge : ∀ r, r ≠ 0 → ∀ position,
    r * uniformPhaseSpaceDensity r (fun _ => 0)
        (uniformRestPositivePhase r position) =
      -4 * uniformNativePhaseDensity
        (uniformRestPositivePhase r position).1
        (uniformRestPositivePhase r position).2
  positiveRestCurrentZero : ∀ axis r, r ≠ 0 → ∀ position,
    uniformPhaseSpaceCurrent axis r (fun _ => 0)
      (uniformRestPositivePhase r position) = 0
  noetherScopeIsStrict :
    uniformNativePhaseDensity uniformNoetherMismatchPhase.1
        uniformNoetherMismatchPhase.2 = 0 ∧
      uniformPhaseSpaceDensity 1 (fun _ => 0)
        uniformNoetherMismatchPhase = 2

theorem uniform_vacuum_current_bridge : UniformVacuumCurrentCertificate where
  momentumResponse := cubical_velocity_is_hamiltonian_momentum_response
  sameReadoutNativeContinuity := uniform_action_readout_local_continuity
  nativeU1Continuity := fun _ _ massSq geometry position velocity site =>
    uniform_native_tangent_local_continuity
      massSq geometry position velocity site
  positiveRestDensityBridge :=
    uniform_positive_rest_density_noether_bridge
  positiveRestCurrentZero :=
    uniform_positive_rest_dirac_current_zero
  noetherScopeIsStrict :=
    uniform_native_noether_is_not_arbitrary_dirac_density

end
end LeanDirac.V2

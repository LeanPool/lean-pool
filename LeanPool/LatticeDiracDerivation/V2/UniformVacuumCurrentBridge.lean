/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativePhaseReadout
public import LeanPool.LatticeDiracDerivation.V2.NativePhaseCharge

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
  fin_cases axis <;>
    simp [cubicalShiftMomentum, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalVelocityOperator, cubicalAlpha] <;>
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

/-- Local continuity for arbitrary four-component data follows from the
same cube-derived alpha and beta operators. -/
theorem cubical_dirac_local_continuity
    (mass : ℝ) (z : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) :
    cubicalCell4DensityDerivative z
        (cubicalDiracTimeDerivative mass z spatialDerivative) +
      cubicalCurrentDivergence z spatialDerivative = 0 := by
  have mass_pairing (component : Fin 4) :
      (star (z component) * (-I * (mass : ℂ) * cubicalStandardBeta z component)).re = 0 := by
    fin_cases component <;>
      simp [cubicalStandardBeta, Complex.mul_re, Complex.mul_im] <;> ring
  have transport_pairing :
      cubicalCell4RealPair z (cubicalDiracTimeDerivative mass z spatialDerivative) =
        -∑ axis : Fin 3, cubicalCell4RealPair z
          (cubicalVelocityOperator axis (spatialDerivative axis)) := by
    simp only [cubicalCell4RealPair, cubicalDiracTimeDerivative, mul_sub, sub_re,
      Finset.mul_sum, Complex.re_sum, mass_pairing, zero_sub, Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_comm
  rw [cubicalCell4DensityDerivative, transport_pairing]
  unfold cubicalCurrentDivergence
  ring

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
The exact periodic lattice law is developed in `FinitePeriodicSector`. -/
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
  have hcharge : uniformNativePhaseDensity (uniformRestPositivePhase r position).1
      (uniformRestPositivePhase r position).2 = -r * uniformCell2Density position :=
    uniform_native_u1_positive_frequency r position
  rw [uniformPhaseSpaceDensity, uniform_rest_positive_readout_eq_double r hr position, hcharge]
  simp [cubicalCell4Density, cubicalUpperEmbedding, uniformCell2Density,
    Complex.normSq, Fin.sum_univ_succ, two_mul]
  ring

theorem uniform_positive_rest_dirac_current_zero
    (axis : Fin 3) (r : ℝ) (hr : r ≠ 0)
    (position : UniformCell2) :
    uniformPhaseSpaceCurrent axis r (fun _ => 0)
      (uniformRestPositivePhase r position) = 0 := by
  rw [uniformPhaseSpaceCurrent, uniform_rest_positive_readout_eq_double r hr position]
  fin_cases axis <;>
    simp [cubicalDiracCurrent, cubicalCell4RealPair, cubicalVelocityOperator, cubicalAlpha,
      cubicalUpperEmbedding,
      cubicalStandardAlphaX, cubicalStandardAlphaY, cubicalStandardAlphaZ, Fin.sum_univ_succ,
      two_mul]

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
    simp [uniformActionToStandardDirac, cubicalPhaseReadout, cubicalFromPositionLower,
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

/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CubicalClifford
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumEulerLagrange

/-!
# Native phase readout and the free Dirac generator

The source operator in this file is the quadratic Euler--Lagrange generator
extracted in `UniformVacuumEulerLagrange`.  The target Clifford algebra is
constructed independently from abstract cube incidence in
`CubicalClifford`.  The exact C19-to-continuum mismatch remains visible.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex Filter Topology
noncomputable section

/-- The first-order phase-space form of the two action-derived transverse
Klein--Gordon channels.  This definition contains no Clifford data. -/
def uniformTwoChannelKleinGordonVector
    (mass px py pz : ℂ)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (phase.2, fun component =>
    -(mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) * phase.1 component)

/-- The first physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPx (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 0 : ℝ)

/-- The second physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPy (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 1 : ℝ)

/-- The third physical momentum coordinate, scaled by the C19 propagation speed. -/
def uniformContinuumPz (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 2 : ℝ)

theorem uniform_continuum_generator_is_kg
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVacuumContinuumGenerator r momentum phase =
      uniformTwoChannelKleinGordonVector (r : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum) phase := by
  have hcoefficient :
      (((r ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ)) =
        (r : ℂ) ^ 2 + (uniformContinuumPx momentum) ^ 2 +
          (uniformContinuumPy momentum) ^ 2 +
          (uniformContinuumPz momentum) ^ 2 := by
    simp only [uniformContinuumPx, uniformContinuumPy, uniformContinuumPz,
      c19_quadratic_symbol_eq_scaled_momentum, ofReal_add, ofReal_pow, add_assoc]
  apply Prod.ext
  · rfl
  · funext component
    simp only [uniformVacuumContinuumGenerator,
      uniformVacuumContinuumAcceleration,
      uniformTwoChannelKleinGordonVector]
    rw [hcoefficient]

/-- Embed the two native transverse positions into the positive beta half of
the four-coordinate cubical representation. -/
def cubicalUpperEmbedding (position : UniformCell2) : CubicalCell4
  | 0 => position 0
  | 1 => position 1
  | _ => 0

/-- Off-diagonal spatial response derived from the pure cubical incidence
Hamiltonian, restricted from the positive beta half to the negative half. -/
def cubicalSpatialLower
    (px py pz : ℂ) (position : UniformCell2) : UniformCell2
  | 0 => orientedCubicalSpatialCoordinates px py pz
      (cubicalUpperEmbedding position) 2
  | _ => orientedCubicalSpatialCoordinates px py pz
      (cubicalUpperEmbedding position) 3

private theorem cubical_upper_embedding_add (first second : UniformCell2) :
    cubicalUpperEmbedding (first + second) =
      cubicalUpperEmbedding first + cubicalUpperEmbedding second := by
  funext component
  fin_cases component <;> simp [cubicalUpperEmbedding]

private theorem cubical_upper_embedding_scale (scalar : ℂ) (position : UniformCell2) :
    cubicalUpperEmbedding (scalar • position) = scalar • cubicalUpperEmbedding position := by
  funext component
  fin_cases component <;> simp [cubicalUpperEmbedding]

private theorem cubical_standard_spatial_add (px py pz : ℂ) (first second : CubicalCell4) :
    cubicalStandardSpatial px py pz (first + second) =
      cubicalStandardSpatial px py pz first + cubicalStandardSpatial px py pz second := by
  funext component
  change cubicalStandardSpatial px py pz (fun index => first index + second index) component =
    cubicalStandardSpatial px py pz first component +
      cubicalStandardSpatial px py pz second component
  simpa only [cubicalStandardHamiltonian, zero_mul, zero_add] using
    congrFun (cubical_standard_hamiltonian_add 0 px py pz first second) component

private theorem cubical_standard_spatial_scale (px py pz scalar : ℂ) (position : CubicalCell4) :
    cubicalStandardSpatial px py pz (scalar • position) =
      scalar • cubicalStandardSpatial px py pz position := by
  funext component
  change cubicalStandardSpatial px py pz (fun index => scalar * position index) component =
    scalar * cubicalStandardSpatial px py pz position component
  simpa only [cubicalStandardHamiltonian, zero_mul, zero_add] using
    congrFun (cubical_standard_hamiltonian_scale 0 px py pz scalar position) component

/-- The incidence-derived block as a linear map on the transverse coordinates. -/
def cubicalSpatialLowerLinear (px py pz : ℂ) : UniformCell2 →ₗ[ℂ] UniformCell2 where
  toFun := cubicalSpatialLower px py pz
  map_add' first second := by
    have add (index : Fin 4) :
        orientedCubicalSpatialCoordinates px py pz (cubicalUpperEmbedding (first + second))
          index =
          orientedCubicalSpatialCoordinates px py pz (cubicalUpperEmbedding first) index +
            orientedCubicalSpatialCoordinates px py pz (cubicalUpperEmbedding second) index := by
      simp only [oriented_cubical_spatial_coordinates_eq_standard, cubical_upper_embedding_add,
        cubical_standard_spatial_add, Pi.add_apply]
    funext component
    fin_cases component
    · exact add 2
    · exact add 3
  map_smul' scalar position := by
    have scale (index : Fin 4) :
        orientedCubicalSpatialCoordinates px py pz (cubicalUpperEmbedding (scalar • position))
          index = scalar •
          orientedCubicalSpatialCoordinates px py pz (cubicalUpperEmbedding position) index := by
      simp only [oriented_cubical_spatial_coordinates_eq_standard, cubical_upper_embedding_scale,
        cubical_standard_spatial_scale, Pi.smul_apply]
    funext component
    fin_cases component
    · exact scale 2
    · exact scale 3

/-- The velocity-dependent two-component coordinate in the native-to-spinor map. -/
def cubicalPhaseLower
    (mass px py pz : ℂ) (phase : UniformTwoChannelPhase) : UniformCell2 :=
  fun component =>
    (I * phase.2 component +
      cubicalSpatialLower px py pz phase.1 component) / mass

/-- For nonzero mass, the lower two coordinates are uniquely forced by the
incidence balance.  They are solved from the native phase variables rather
than fitted as an independent spinor rule. -/
theorem cubical_phase_lower_unique
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (phase : UniformTwoChannelPhase) (lower : UniformCell2)
    (hbalance : ∀ component,
      mass * lower component =
        I * phase.2 component +
          cubicalSpatialLower px py pz phase.1 component) :
    lower = cubicalPhaseLower mass px py pz phase := by
  funext component
  unfold cubicalPhaseLower
  field_simp [hmass]
  simpa [mul_comm] using hbalance component

/-- Recover the two position coordinates by combining upper and lower spinor components. -/
def cubicalStandardPosition (z : CubicalCell4) : UniformCell2
  | 0 => (z 0 - z 2) / 2
  | _ => (z 1 - z 3) / 2

/-- Recover the two auxiliary coordinates from sums of spinor components. -/
def cubicalStandardLower (z : CubicalCell4) : UniformCell2
  | 0 => (z 0 + z 2) / 2
  | _ => (z 1 + z 3) / 2

/-- Reconstruct a four-coordinate vector from its native position half and
its complementary cubical half. -/
def cubicalFromPositionLower
    (position lower : UniformCell2) : CubicalCell4
  | 0 => position 0 + lower 0
  | 1 => position 1 + lower 1
  | 2 => -position 0 + lower 0
  | _ => -position 1 + lower 1

@[simp] theorem cubical_standard_position_from_position_lower
    (position lower : UniformCell2) :
    cubicalStandardPosition (cubicalFromPositionLower position lower) =
      position := by
  funext component
  fin_cases component <;>
    simp [cubicalStandardPosition, cubicalFromPositionLower]

@[simp] theorem cubical_standard_lower_from_position_lower
    (position lower : UniformCell2) :
    cubicalStandardLower (cubicalFromPositionLower position lower) = lower := by
  funext component
  fin_cases component <;>
    simp [cubicalStandardLower, cubicalFromPositionLower] <;> ring

/-- Position and complementary coordinates determine the four-component
vector. -/
theorem cubical_eq_from_position_and_lower (z : CubicalCell4) :
    cubicalFromPositionLower (cubicalStandardPosition z)
      (cubicalStandardLower z) = z := by
  funext component
  fin_cases component <;>
    simp [cubicalFromPositionLower, cubicalStandardPosition,
      cubicalStandardLower] <;> ring

/-- Four-component readout from the native position and the incidence balance. -/
def cubicalPhaseReadout
    (mass px py pz : ℂ) (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  cubicalFromPositionLower phase.1 (cubicalPhaseLower mass px py pz phase)

/-- Scalar multiplication on the native two-layer phase space. -/
def uniformTwoChannelScale
    (scalar : ℂ) (phase : UniformTwoChannelPhase) :
    UniformTwoChannelPhase :=
  (fun component => scalar * phase.1 component,
    fun component => scalar * phase.2 component)

theorem cubical_phase_readout_scale
    (mass px py pz scalar : ℂ) (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadout mass px py pz
        (uniformTwoChannelScale scalar phase) =
      fun component =>
        scalar * cubicalPhaseReadout mass px py pz phase component := by
  have spatial := (cubicalSpatialLowerLinear px py pz).map_smul scalar phase.1
  change cubicalSpatialLower px py pz (fun component => scalar * phase.1 component) =
    (fun component => scalar * cubicalSpatialLower px py pz phase.1 component) at spatial
  funext component
  fin_cases component <;>
    simp [uniformTwoChannelScale, cubicalPhaseReadout, cubicalFromPositionLower,
      cubicalPhaseLower, spatial] <;> ring

/-- The four-component readout with the continuum momentum determined by the action. -/
def uniformActionToStandardDirac
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  cubicalPhaseReadout (r : ℂ)
    (uniformContinuumPx momentum)
    (uniformContinuumPy momentum)
    (uniformContinuumPz momentum) phase

/-- Native positive-rest-frequency data.  The sign convention is
`q(t) = exp (-i r t) q(0)`. -/
def uniformRestPositivePhase
    (r : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  (position, fun component => -I * (r : ℂ) * position component)

/-- Native negative-rest-frequency data. -/
def uniformRestNegativePhase
    (r : ℝ) (position : UniformCell2) : UniformTwoChannelPhase :=
  (position, fun component => I * (r : ℂ) * position component)

private theorem cubical_spatial_lower_zero (position : UniformCell2) :
    cubicalSpatialLower 0 0 0 position = 0 := by
  funext component
  fin_cases component <;> simp [cubicalSpatialLower, cubicalStandardSpatial]

/-- The positive rest mode reads out as twice its upper-block embedding. -/
theorem uniform_rest_positive_readout_eq_double (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    uniformActionToStandardDirac r (fun _ => 0) (uniformRestPositivePhase r position) =
      2 • cubicalUpperEmbedding position := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlower :
      cubicalPhaseLower (r : ℂ) 0 0 0 (uniformRestPositivePhase r position) = position := by
    funext component
    simp only [cubicalPhaseLower, uniformRestPositivePhase, cubical_spatial_lower_zero,
      Pi.zero_apply, add_zero]
    apply (div_eq_iff hrC).2
    rw [← mul_assoc, ← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul, mul_comm]
  have hcoordinate (axis : Fin 3) : (c19ScaledMomentum (fun _ => 0) axis : ℂ) = 0 := by
    simp [c19ScaledMomentum]
  have hposition : (uniformRestPositivePhase r position).1 = position := rfl
  unfold uniformActionToStandardDirac
  simp only [uniformContinuumPx, uniformContinuumPy, uniformContinuumPz, hcoordinate]
  funext component
  fin_cases component <;>
    simp [cubicalPhaseReadout, cubicalFromPositionLower, cubicalUpperEmbedding,
      hlower, hposition, add_comm, two_mul]

/-- The cube-parity beta grading is forced by the native positive rest
frequency after the lossless phase-space reconstruction. -/
theorem uniform_rest_positive_readout_has_positive_beta
    (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestPositivePhase r position)) =
      uniformActionToStandardDirac r (fun _ => 0)
        (uniformRestPositivePhase r position) := by
  rw [uniform_rest_positive_readout_eq_double r hr position]
  funext component
  fin_cases component <;> simp [cubicalStandardBeta, cubicalUpperEmbedding, two_mul]

/-- The opposite native rest frequency lands in the negative beta sector. -/
theorem uniform_rest_negative_readout_has_negative_beta
    (r : ℝ) (hr : r ≠ 0) (position : UniformCell2) :
    cubicalStandardBeta
        (uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position)) =
      fun component =>
        -uniformActionToStandardDirac r (fun _ => 0)
          (uniformRestNegativePhase r position) component := by
  funext component
  fin_cases component <;>
    simp [uniformActionToStandardDirac, uniformRestNegativePhase,
      uniformContinuumPx, uniformContinuumPy, uniformContinuumPz, c19ScaledMomentum,
      cubicalPhaseReadout, cubicalFromPositionLower, cubicalPhaseLower, cubicalSpatialLower,
      cubicalUpperEmbedding, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hr] <;> ring_nf <;> rw [Complex.I_sq] <;> ring

private def cubicalRepeatedCoordinates (position : UniformCell2) : CubicalCell4
  | 0 => position 0
  | 1 => position 1
  | 2 => position 0
  | _ => position 1

private theorem cubical_repeated_coordinates_mul (scale : ℂ) (position : UniformCell2) :
    cubicalRepeatedCoordinates (fun i => scale * position i) =
      fun i => scale * cubicalRepeatedCoordinates position i := by
  funext i
  fin_cases i <;> rfl

private theorem cubical_phase_readout_factor (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadout mass px py pz phase =
      fun i => mass⁻¹ * (cubicalStandardHamiltonian mass px py pz
        (cubicalRepeatedCoordinates phase.1) i + I * cubicalRepeatedCoordinates phase.2 i) := by
  funext i
  fin_cases i <;>
    simp [cubicalPhaseReadout, cubicalFromPositionLower, cubicalPhaseLower, cubicalSpatialLower,
      cubicalUpperEmbedding, cubicalRepeatedCoordinates, cubicalStandardHamiltonian,
      cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;> field_simp [hmass] <;> ring

theorem cubical_phase_readout_intertwines
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadout mass px py pz
        (uniformTwoChannelKleinGordonVector mass px py pz phase) =
      fun component =>
        -I * cubicalStandardHamiltonian mass px py pz
          (cubicalPhaseReadout mass px py pz phase) component := by
  simp only [cubical_phase_readout_factor mass px py pz hmass, uniformTwoChannelKleinGordonVector,
    cubical_repeated_coordinates_mul, cubical_standard_hamiltonian_scale,
    cubical_standard_hamiltonian_add, cubical_standard_hamiltonian_square]
  funext i
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Recover native position and velocity from the four-component readout. -/
def cubicalPhaseReadoutInverse
    (mass px py pz : ℂ) (z : CubicalCell4) : UniformTwoChannelPhase :=
  let position := cubicalStandardPosition z
  (position, fun component =>
    -I * (mass * cubicalStandardLower z component -
      cubicalSpatialLower px py pz position component))

theorem cubical_phase_readout_left_inverse
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadoutInverse mass px py pz
        (cubicalPhaseReadout mass px py pz phase) = phase := by
  apply Prod.ext
  · change cubicalStandardPosition (cubicalPhaseReadout mass px py pz phase) = phase.1
    rw [cubicalPhaseReadout, cubical_standard_position_from_position_lower]
  · change (fun component ↦ -I * (mass * cubicalStandardLower
      (cubicalPhaseReadout mass px py pz phase) component -
        cubicalSpatialLower px py pz (cubicalStandardPosition
          (cubicalPhaseReadout mass px py pz phase)) component)) = phase.2
    rw [cubicalPhaseReadout, cubical_standard_position_from_position_lower,
      cubical_standard_lower_from_position_lower]
    funext component
    have balance : mass * cubicalPhaseLower mass px py pz phase component =
        I * phase.2 component + cubicalSpatialLower px py pz phase.1 component := by
      rw [cubicalPhaseLower]
      exact mul_div_cancel₀ _ hmass
    rw [balance, add_sub_cancel_right, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

theorem cubical_phase_readout_injective
    (mass px py pz : ℂ) (hmass : mass ≠ 0) :
    Function.Injective (cubicalPhaseReadout mass px py pz) := by
  have leftInverse : Function.LeftInverse (cubicalPhaseReadoutInverse mass px py pz)
      (cubicalPhaseReadout mass px py pz) := cubical_phase_readout_left_inverse mass px py pz hmass
  exact leftInverse.injective

theorem cubical_phase_readout_add
    (mass px py pz : ℂ) (first second : UniformTwoChannelPhase) :
    cubicalPhaseReadout mass px py pz
        (fun component => first.1 component + second.1 component,
         fun component => first.2 component + second.2 component) =
      fun component =>
        cubicalPhaseReadout mass px py pz first component +
          cubicalPhaseReadout mass px py pz second component := by
  have spatial := (cubicalSpatialLowerLinear px py pz).map_add first.1 second.1
  change cubicalSpatialLower px py pz (fun component => first.1 component + second.1 component) =
    (fun component => cubicalSpatialLower px py pz first.1 component +
      cubicalSpatialLower px py pz second.1 component) at spatial
  funext component
  fin_cases component <;>
    simp [cubicalPhaseReadout, cubicalFromPositionLower, cubicalPhaseLower, spatial] <;> ring

/-- The action-derived spinor readout preserves addition of native phases. -/
theorem uniform_action_readout_add
    (r : ℝ) (momentum : LatticeMomentum) (first second : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (fun component => first.1 component + second.1 component,
         fun component => first.2 component + second.2 component) =
      fun component =>
        uniformActionToStandardDirac r momentum first component +
          uniformActionToStandardDirac r momentum second component :=
  cubical_phase_readout_add _ _ _ _ first second

private theorem cubical_phase_lower_of_decoded_velocity (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (position lower : UniformCell2) :
    cubicalPhaseLower mass px py pz
      (position, fun component ↦ -I *
        (mass * lower component - cubicalSpatialLower px py pz position component)) = lower := by
  apply (cubical_phase_lower_unique mass px py pz hmass _ lower ?_).symm
  intro component
  dsimp only
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul, sub_add_cancel]

theorem cubical_phase_readout_right_inverse
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (z : CubicalCell4) :
    cubicalPhaseReadout mass px py pz
        (cubicalPhaseReadoutInverse mass px py pz z) = z := by
  change cubicalFromPositionLower (cubicalStandardPosition z)
    (cubicalPhaseLower mass px py pz
      (cubicalStandardPosition z, fun component ↦ -I * (mass * cubicalStandardLower z component -
        cubicalSpatialLower px py pz (cubicalStandardPosition z) component))) = z
  rw [cubical_phase_lower_of_decoded_velocity mass px py pz hmass,
    cubical_eq_from_position_and_lower]

theorem cubical_phase_readout_bijective
    (mass px py pz : ℂ) (hmass : mass ≠ 0) :
    Function.Bijective (cubicalPhaseReadout mass px py pz) := by
  constructor
  · exact cubical_phase_readout_injective mass px py pz hmass
  · intro z
    exact ⟨cubicalPhaseReadoutInverse mass px py pz z,
      cubical_phase_readout_right_inverse mass px py pz hmass z⟩

theorem uniform_action_to_standard_injective
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum) :
    Function.Injective (uniformActionToStandardDirac r momentum) := by
  exact cubical_phase_readout_injective (r : ℂ)
    (uniformContinuumPx momentum)
    (uniformContinuumPy momentum)
    (uniformContinuumPz momentum) (by exact_mod_cast hr)

theorem uniform_action_to_standard_bijective
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum) :
    Function.Bijective (uniformActionToStandardDirac r momentum) := by
  exact cubical_phase_readout_bijective (r : ℂ)
    (uniformContinuumPx momentum)
    (uniformContinuumPy momentum)
    (uniformContinuumPz momentum) (by exact_mod_cast hr)

/-- The same action-derived flow in conventional four-component coordinates,
where alpha and beta are downstream coordinates on pure cube incidence. -/
theorem uniform_action_tangent_intertwines_cubical_dirac
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (uniformVacuumContinuumGenerator r momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase) component := by
  unfold uniformActionToStandardDirac
  rw [uniform_continuum_generator_is_kg]
  exact cubical_phase_readout_intertwines
    (r : ℂ) (uniformContinuumPx momentum)
    (uniformContinuumPy momentum) (uniformContinuumPz momentum)
    (by exact_mod_cast hr) phase

/-- Both native cubical flavor copies carry that same derived four-component
operator.  Nothing selects or discards either copy. -/
theorem uniform_action_dirac_has_both_cubical_copies
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    (cubicalNativeHamiltonian (r : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum)
        (cubicalDiracEmbedMinus
          (uniformActionToStandardDirac r momentum phase)) =
      cubicalDiracEmbedMinus
        (cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase))) ∧
    (cubicalNativeHamiltonian (r : ℂ)
        (uniformContinuumPx momentum)
        (uniformContinuumPy momentum)
        (uniformContinuumPz momentum)
        (cubicalDiracEmbedPlus
          (uniformActionToStandardDirac r momentum phase)) =
      cubicalDiracEmbedPlus
        (cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase))) := by
  exact ⟨cubical_hamiltonian_intertwines_minus _ _ _ _ _,
    cubical_hamiltonian_intertwines_plus _ _ _ _ _⟩

/-- The phase correction whose acceleration component is the C19 spatial remainder. -/
def uniformNativeSpatialDefectPhase
    (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (fun _ => 0,
    fun component =>
      -(c19SpatialRemainder momentum : ℂ) * phase.1 component)

/-- Exact finite-spacing statement: the native C19 generator equals the
continuum generator plus one explicit action-derived spatial defect. -/
theorem uniform_native_generator_exact_defect
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVacuumNativeGenerator r momentum phase =
      (fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).1 component +
          (uniformNativeSpatialDefectPhase momentum phase).1 component,
       fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).2 component +
          (uniformNativeSpatialDefectPhase momentum phase).2 component) := by
  rw [uniform_native_generator_splits]
  apply Prod.ext
  · funext component
    simp [uniformNativeSpatialDefectPhase]
  · funext component
    simp [uniformNativeSpatialDefectPhase]
    ring

end
end LeanDirac.V2

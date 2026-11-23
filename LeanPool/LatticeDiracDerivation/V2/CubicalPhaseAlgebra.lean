/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CubicalSpinorBlocks

/-! # Linear cubical coordinates and the algebraic phase-space readout -/

@[expose] public section

namespace LeanDirac.V2

open Complex
noncomputable section

/-- The first-order phase-space form of the two action-derived transverse
Klein--Gordon channels.  This definition contains no Clifford data. -/
def uniformTwoChannelKleinGordonVector
    (mass px py pz : ℂ)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (phase.2, fun component =>
    -(mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) * phase.1 component)

/-- Off-diagonal spatial response derived from the pure cubical incidence
Hamiltonian, restricted from the positive beta half to the negative half. -/
def cubicalSpatialLower (px py pz : ℂ) (position : UniformCell2) : UniformCell2 :=
  cubicalCell4LowerHalf
    (orientedCubicalSpatialCoordinates px py pz (cubicalUpperEmbedding position))

private def cubicalUpperLinear : UniformCell2 →ₗ[ℂ] CubicalCell4 :=
  cubicalSpinorOfBlocksLinear.comp (LinearMap.inl ℂ UniformCell2 UniformCell2)

private theorem cubical_upper_embedding_add (first second : UniformCell2) :
    cubicalUpperEmbedding (first + second) =
      cubicalUpperEmbedding first + cubicalUpperEmbedding second :=
  cubicalUpperLinear.map_add first second

private theorem cubical_upper_embedding_scale (scalar : ℂ) (position : UniformCell2) :
    cubicalUpperEmbedding (scalar • position) = scalar • cubicalUpperEmbedding position :=
  cubicalUpperLinear.map_smul scalar position

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
    simp only [cubicalSpatialLower, oriented_cubical_spatial_coordinates_eq_standard,
      cubical_upper_embedding_add, cubical_standard_spatial_add]
    rfl
  map_smul' scalar position := by
    simp only [cubicalSpatialLower, oriented_cubical_spatial_coordinates_eq_standard,
      cubical_upper_embedding_scale, cubical_standard_spatial_scale]
    rfl

@[simp] theorem cubical_spatial_lower_zero_amplitude (px py pz : ℂ) :
    cubicalSpatialLower px py pz 0 = 0 :=
  (cubicalSpatialLowerLinear px py pz).map_zero

/-- The Hamiltonian acts by the diagonal mass and off-diagonal spatial blocks. -/
theorem cubical_standard_hamiltonian_blocks (mass px py pz : ℂ) (upper lower : UniformCell2) :
    cubicalStandardHamiltonian mass px py pz (cubicalSpinorOfBlocks upper lower) =
      cubicalSpinorOfBlocks
        (fun i => mass * upper i + cubicalSpatialLower px py pz lower i)
        (fun i => cubicalSpatialLower px py pz upper i - mass * lower i) := by
  funext component
  fin_cases component <;>
    simp [cubicalStandardHamiltonian, cubicalStandardSpatial, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY, cubicalStandardAlphaZ,
      cubicalSpatialLower, cubicalUpperEmbedding] <;> ring

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
def cubicalStandardPosition (z : CubicalCell4) : UniformCell2 := fun component =>
  (cubicalCell4Upper z component - cubicalCell4LowerHalf z component) / 2

/-- Recover the two auxiliary coordinates from sums of spinor components. -/
def cubicalStandardLower (z : CubicalCell4) : UniformCell2 := fun component =>
  (cubicalCell4Upper z component + cubicalCell4LowerHalf z component) / 2

/-- Reconstruct a spinor from its native position and complementary coordinates. -/
def cubicalFromPositionLower (position lower : UniformCell2) : CubicalCell4 :=
  cubicalSpinorOfBlocks (position + lower) (-position + lower)

@[simp] theorem cubical_standard_position_from_position_lower
    (position lower : UniformCell2) :
    cubicalStandardPosition (cubicalFromPositionLower position lower) = position := by
  funext component
  simp [cubicalStandardPosition, cubicalFromPositionLower]

@[simp] theorem cubical_standard_lower_from_position_lower
    (position lower : UniformCell2) :
    cubicalStandardLower (cubicalFromPositionLower position lower) = lower := by
  funext component
  simp [cubicalStandardLower, cubicalFromPositionLower]
  ring

/-- Position and complementary coordinates determine the four-component vector. -/
theorem cubical_eq_from_position_and_lower (z : CubicalCell4) :
    cubicalFromPositionLower (cubicalStandardPosition z) (cubicalStandardLower z) = z := by
  calc
    _ = cubicalSpinorOfBlocks (cubicalCell4Upper z) (cubicalCell4LowerHalf z) := by
      unfold cubicalFromPositionLower
      apply congrArg₂ cubicalSpinorOfBlocks
      · funext component
        simp only [Pi.add_apply, cubicalStandardPosition, cubicalStandardLower]
        ring
      · funext component
        simp only [Pi.add_apply, Pi.neg_apply, cubicalStandardPosition, cubicalStandardLower]
        ring
    _ = z := cubical_spinor_of_its_blocks z

/-- Four-component readout from the native position and the incidence balance. -/
def cubicalPhaseReadout
    (mass px py pz : ℂ) (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  cubicalFromPositionLower phase.1 (cubicalPhaseLower mass px py pz phase)

/-- Linear map computing the velocity-dependent block from the native phase. -/
def cubicalPhaseLowerLinear (mass px py pz : ℂ) : UniformTwoChannelPhase →ₗ[ℂ] UniformCell2 :=
  mass⁻¹ • (I • LinearMap.snd ℂ UniformCell2 UniformCell2 +
    (cubicalSpatialLowerLinear px py pz).comp (LinearMap.fst ℂ UniformCell2 UniformCell2))

/-- Complex-linear native-to-spinor readout in the cubical basis. -/
def cubicalPhaseReadoutLinear (mass px py pz : ℂ) :
    UniformTwoChannelPhase →ₗ[ℂ] CubicalCell4 :=
  let position := LinearMap.fst ℂ UniformCell2 UniformCell2
  let lower := cubicalPhaseLowerLinear mass px py pz
  cubicalSpinorOfBlocksLinear.comp ((position + lower).prod (-position + lower))

private theorem cubical_phase_lower_linear_apply (mass px py pz : ℂ)
    (phase : UniformTwoChannelPhase) :
    cubicalPhaseLowerLinear mass px py pz phase = cubicalPhaseLower mass px py pz phase := by
  funext component
  change mass⁻¹ * (I * phase.2 component + cubicalSpatialLower px py pz phase.1 component) = _
  rw [cubicalPhaseLower, div_eq_mul_inv, mul_comm]

theorem cubical_phase_readout_linear_apply (mass px py pz : ℂ) (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadoutLinear mass px py pz phase = cubicalPhaseReadout mass px py pz phase := by
  change cubicalSpinorOfBlocks (phase.1 + cubicalPhaseLowerLinear mass px py pz phase)
    (-phase.1 + cubicalPhaseLowerLinear mass px py pz phase) = _
  rw [cubical_phase_lower_linear_apply]
  rfl

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
  change cubicalPhaseReadout mass px py pz (scalar • phase) =
    scalar • cubicalPhaseReadout mass px py pz phase
  simpa only [cubical_phase_readout_linear_apply] using
    (cubicalPhaseReadoutLinear mass px py pz).map_smul scalar phase

private def cubicalRepeatedCoordinates (position : UniformCell2) : CubicalCell4 :=
  cubicalSpinorOfBlocks position position

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
  unfold cubicalPhaseReadout cubicalFromPositionLower cubicalRepeatedCoordinates
  rw [cubical_standard_hamiltonian_blocks]
  let upper : UniformCell2 := fun i => mass * phase.1 i + cubicalSpatialLower px py pz phase.1 i
  let lower : UniformCell2 := fun i => cubicalSpatialLower px py pz phase.1 i - mass * phase.1 i
  change cubicalSpinorOfBlocks _ _ =
    mass⁻¹ • (cubicalSpinorOfBlocks upper lower + I • cubicalSpinorOfBlocks phase.2 phase.2)
  have scale (a : ℂ) (x y : UniformCell2) :
      a • cubicalSpinorOfBlocks x y = cubicalSpinorOfBlocks (a • x) (a • y) :=
    (cubicalSpinorOfBlocksLinear.map_smul a (x, y)).symm
  have add (x y x' y' : UniformCell2) :
      cubicalSpinorOfBlocks x y + cubicalSpinorOfBlocks x' y' =
        cubicalSpinorOfBlocks (x + x') (y + y') :=
    (cubicalSpinorOfBlocksLinear.map_add (x, y) (x', y')).symm
  rw [scale I, add, scale]
  apply congrArg₂ cubicalSpinorOfBlocks
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cubicalPhaseLower, upper]
    field_simp [hmass]
    ring
  · funext i
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cubicalPhaseLower, lower]
    field_simp [hmass]
    ring

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
  change cubicalPhaseReadout mass px py pz (first + second) =
    cubicalPhaseReadout mass px py pz first + cubicalPhaseReadout mass px py pz second
  simpa only [cubical_phase_readout_linear_apply] using
    (cubicalPhaseReadoutLinear mass px py pz).map_add first second

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

end
end LeanDirac.V2

/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativePhaseReadout

/-!
# Native phase space compressed into the cubical Clifford fibers

This module closes the operator diagram between the action-derived two-channel
phase space and each of the two rank-four flavor fibers of the oriented-cube
Clifford representation.  The embeddings below are emergent readouts attached
to a lattice momentum.  Their eight coordinates are an internal cubical fiber;
they are **not** asserted to be eight separate physical lattice sites.

For the continuum tangent, both embeddings exactly intertwine the native
generator with the corresponding cubical Dirac Hamiltonian.  For the exact
C19 tangent, the same statement holds with the already-derived finite-spacing
remainder transported through the very same embedding.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex
noncomputable section

/-- The native phase space read through the negative cubical flavor fiber. -/
def nativeCubicalPhaseEmbedMinus
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell8 :=
  cubicalDiracEmbedMinus (uniformActionToStandardDirac r momentum phase)

/-- The native phase space read through the positive cubical flavor fiber. -/
def nativeCubicalPhaseEmbedPlus
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell8 :=
  cubicalDiracEmbedPlus (uniformActionToStandardDirac r momentum phase)

theorem native_cubical_phase_embed_minus_injective
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum) :
    Function.Injective (nativeCubicalPhaseEmbedMinus r momentum) := by
  intro first second h
  apply uniform_action_to_standard_injective r hr momentum
  exact cubical_dirac_embed_minus_injective h

theorem native_cubical_phase_embed_plus_injective
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum) :
    Function.Injective (nativeCubicalPhaseEmbedPlus r momentum) := by
  intro first second h
  apply uniform_action_to_standard_injective r hr momentum
  exact cubical_dirac_embed_plus_injective h

theorem native_cubical_phase_embed_minus_has_negative_flavor
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    cubicalFlavor (nativeCubicalPhaseEmbedMinus r momentum phase) =
      fun corner => -nativeCubicalPhaseEmbedMinus r momentum phase corner := by
  exact cubical_embed_minus_has_negative_flavor
    (standardToCubicalMinus (uniformActionToStandardDirac r momentum phase))

theorem native_cubical_phase_embed_plus_has_positive_flavor
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    cubicalFlavor (nativeCubicalPhaseEmbedPlus r momentum phase) =
      nativeCubicalPhaseEmbedPlus r momentum phase := by
  exact cubical_embed_plus_has_positive_flavor
    (standardToCubicalPlus (uniformActionToStandardDirac r momentum phase))

theorem cubical_dirac_embed_minus_scale
    (scalar : ℂ) (z : CubicalCell4) :
    cubicalDiracEmbedMinus (fun component => scalar * z component) =
      fun corner => scalar * cubicalDiracEmbedMinus z corner :=
  map_smul cubicalDiracLinearEmbedMinus scalar z

theorem cubical_dirac_embed_plus_scale
    (scalar : ℂ) (z : CubicalCell4) :
    cubicalDiracEmbedPlus (fun component => scalar * z component) =
      fun corner => scalar * cubicalDiracEmbedPlus z corner :=
  map_smul cubicalDiracLinearEmbedPlus scalar z

/-- The action-derived continuum tangent, compressed into the negative
flavor fiber, is exactly the cubical Dirac flow. -/
theorem native_continuum_generator_intertwines_cubical_minus
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    nativeCubicalPhaseEmbedMinus r momentum
        (uniformVacuumContinuumGenerator r momentum phase) =
      fun corner =>
        -I * cubicalNativeHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (nativeCubicalPhaseEmbedMinus r momentum phase) corner := by
  unfold nativeCubicalPhaseEmbedMinus
  rw [uniform_action_tangent_intertwines_cubical_dirac r hr]
  rw [cubical_dirac_embed_minus_scale]
  rw [cubical_hamiltonian_intertwines_minus]

/-- The same action-derived continuum tangent in the positive flavor fiber. -/
theorem native_continuum_generator_intertwines_cubical_plus
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    nativeCubicalPhaseEmbedPlus r momentum
        (uniformVacuumContinuumGenerator r momentum phase) =
      fun corner =>
        -I * cubicalNativeHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (nativeCubicalPhaseEmbedPlus r momentum phase) corner := by
  unfold nativeCubicalPhaseEmbedPlus
  rw [uniform_action_tangent_intertwines_cubical_dirac r hr]
  rw [cubical_dirac_embed_plus_scale]
  rw [cubical_hamiltonian_intertwines_plus]

/-- Add the position and velocity components of two native phases separately. -/
def uniformPhaseAdd
    (first second : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (fun component => first.1 component + second.1 component,
   fun component => first.2 component + second.2 component)

theorem native_cubical_phase_embed_minus_add
    (r : ℝ) (momentum : LatticeMomentum)
    (first second : UniformTwoChannelPhase) :
    nativeCubicalPhaseEmbedMinus r momentum
        (uniformPhaseAdd first second) =
      fun corner =>
        nativeCubicalPhaseEmbedMinus r momentum first corner +
          nativeCubicalPhaseEmbedMinus r momentum second corner := by
  unfold nativeCubicalPhaseEmbedMinus uniformPhaseAdd
  rw [uniform_action_readout_add r momentum first second]
  exact map_add cubicalDiracLinearEmbedMinus _ _

theorem native_cubical_phase_embed_plus_add
    (r : ℝ) (momentum : LatticeMomentum)
    (first second : UniformTwoChannelPhase) :
    nativeCubicalPhaseEmbedPlus r momentum
        (uniformPhaseAdd first second) =
      fun corner =>
        nativeCubicalPhaseEmbedPlus r momentum first corner +
          nativeCubicalPhaseEmbedPlus r momentum second corner := by
  unfold nativeCubicalPhaseEmbedPlus uniformPhaseAdd
  rw [uniform_action_readout_add r momentum first second]
  exact map_add cubicalDiracLinearEmbedPlus _ _

theorem uniform_native_generator_is_phase_add
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVacuumNativeGenerator r momentum phase =
      uniformPhaseAdd
        (uniformVacuumContinuumGenerator r momentum phase)
        (uniformNativeSpatialDefectPhase momentum phase) := by
  rw [uniform_native_generator_exact_defect]
  rfl

/-- The lattice spatial correction expressed in the negative cube sector. -/
def nativeCubicalSpatialDefectMinus
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell8 :=
  nativeCubicalPhaseEmbedMinus r momentum
    (uniformNativeSpatialDefectPhase momentum phase)

/-- The lattice spatial correction expressed in the positive cube sector. -/
def nativeCubicalSpatialDefectPlus
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell8 :=
  nativeCubicalPhaseEmbedPlus r momentum
    (uniformNativeSpatialDefectPhase momentum phase)

/-- Exact finite-C19 operator identity in the negative flavor fiber.  The
only departure from the continuum Dirac flow is the explicit mapped C19
spatial remainder. -/
theorem native_exact_generator_intertwines_cubical_minus
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    nativeCubicalPhaseEmbedMinus r momentum
        (uniformVacuumNativeGenerator r momentum phase) =
      fun corner =>
        -I * cubicalNativeHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (nativeCubicalPhaseEmbedMinus r momentum phase) corner +
        nativeCubicalSpatialDefectMinus r momentum phase corner := by
  rw [uniform_native_generator_is_phase_add]
  rw [native_cubical_phase_embed_minus_add]
  rw [native_continuum_generator_intertwines_cubical_minus r hr]
  rfl

/-- Exact finite-C19 operator identity in the positive flavor fiber. -/
theorem native_exact_generator_intertwines_cubical_plus
    (r : ℝ) (hr : r ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    nativeCubicalPhaseEmbedPlus r momentum
        (uniformVacuumNativeGenerator r momentum phase) =
      fun corner =>
        -I * cubicalNativeHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (nativeCubicalPhaseEmbedPlus r momentum phase) corner +
        nativeCubicalSpatialDefectPlus r momentum phase corner := by
  rw [uniform_native_generator_is_phase_add]
  rw [native_cubical_phase_embed_plus_add]
  rw [native_continuum_generator_intertwines_cubical_plus r hr]
  rfl

end
end LeanDirac.V2

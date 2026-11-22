/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativePhaseReadout

/-!
# Characterization of the cubical phase-space readout

The native action fixes a second-order two-channel tangent generator.  The
oriented cubical cell complex fixes a Kähler--Dirac Hamiltonian, up to the
already documented global orientation, axis ordering, and commuting flavor
choice.  This file proves that, after those geometric conventions are fixed,
the existing four-component readout is not an additional free choice: it is
the unique readout that recovers the native position and intertwines the
native tangent generator with the cubical first-order generator.

This is deliberately not a theorem that the scalar native action selects a
preferred global cube orientation or one of the two flavor copies.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex
noncomputable section

private theorem cubical_position_of_hamiltonian_step
    (mass px py pz : ℂ) (position lower : UniformCell2) :
    cubicalStandardPosition (fun component => -I * cubicalStandardHamiltonian mass px py pz
        (cubicalFromPositionLower position lower) component) =
      fun component => -I *
        (mass * lower component - cubicalSpatialLower px py pz position component) := by
  funext component
  fin_cases component <;>
    simp [cubicalStandardPosition, cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX, cubicalStandardAlphaY, cubicalStandardAlphaZ,
      cubicalSpatialLower, cubicalUpperEmbedding, cubicalFromPositionLower] <;> ring

/-- The position half of the first-order cubical equation forces the
complementary half.  This is the spectral/Kähler--Dirac origin of
`cubicalPhaseLower`; its defining balance is not assumed here. -/
theorem cubical_lower_forced_by_position_intertwining
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (candidate : UniformTwoChannelPhase → CubicalCell4)
    (hposition : ∀ phase,
      cubicalStandardPosition (candidate phase) = phase.1)
    (hintertwines : ∀ phase,
      candidate (uniformTwoChannelKleinGordonVector mass px py pz phase) =
        fun component =>
          -I * cubicalStandardHamiltonian mass px py pz
            (candidate phase) component)
    (phase : UniformTwoChannelPhase) :
    cubicalStandardLower (candidate phase) =
      cubicalPhaseLower mass px py pz phase := by
  have hnext := hposition
    (uniformTwoChannelKleinGordonVector mass px py pz phase)
  rw [hintertwines phase] at hnext
  have hcurrent := hposition phase
  have hz : candidate phase =
      cubicalFromPositionLower phase.1
        (cubicalStandardLower (candidate phase)) := by
    rw [← hcurrent]
    exact (cubical_eq_from_position_and_lower (candidate phase)).symm
  rw [hz] at hnext
  apply cubical_phase_lower_unique mass px py pz hmass phase
    (cubicalStandardLower (candidate phase))
  rw [cubical_position_of_hamiltonian_step] at hnext
  intro component
  have hi := congrArg (fun value : ℂ => I * value) (congrFun hnext component)
  change I * (-I * (mass * cubicalStandardLower (candidate phase) component -
    cubicalSpatialLower px py pz phase.1 component)) = I * phase.2 component at hi
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul] at hi
  exact sub_eq_iff_eq_add.mp hi

/-- Once the Kähler--Dirac root and the native-position normalization are
fixed, the existing readout is the unique map intertwining the native
second-order flow with that first-order root. -/
theorem cubical_phase_readout_unique_from_intertwining
    (mass px py pz : ℂ) (hmass : mass ≠ 0)
    (candidate : UniformTwoChannelPhase → CubicalCell4)
    (hposition : ∀ phase,
      cubicalStandardPosition (candidate phase) = phase.1)
    (hintertwines : ∀ phase,
      candidate (uniformTwoChannelKleinGordonVector mass px py pz phase) =
        fun component =>
          -I * cubicalStandardHamiltonian mass px py pz
            (candidate phase) component) :
    candidate = cubicalPhaseReadout mass px py pz := by
  funext phase
  rw [← cubical_eq_from_position_and_lower (candidate phase)]
  rw [hposition phase]
  rw [cubical_lower_forced_by_position_intertwining mass px py pz hmass
    candidate hposition hintertwines phase]
  rfl

/-- The concrete readout therefore satisfies the intrinsic characterization:
it recovers native position, intertwines the generators, and is the only map
with both properties. -/
theorem cubical_phase_readout_is_uniquely_characterized
    (mass px py pz : ℂ) (hmass : mass ≠ 0) :
    (∀ phase,
      cubicalStandardPosition
        (cubicalPhaseReadout mass px py pz phase) = phase.1) ∧
    (∀ phase,
      cubicalPhaseReadout mass px py pz
          (uniformTwoChannelKleinGordonVector mass px py pz phase) =
        fun component =>
          -I * cubicalStandardHamiltonian mass px py pz
            (cubicalPhaseReadout mass px py pz phase) component) ∧
    (∀ candidate : UniformTwoChannelPhase → CubicalCell4,
      (∀ phase, cubicalStandardPosition (candidate phase) = phase.1) →
      (∀ phase,
        candidate (uniformTwoChannelKleinGordonVector mass px py pz phase) =
          fun component =>
            -I * cubicalStandardHamiltonian mass px py pz
              (candidate phase) component) →
      candidate = cubicalPhaseReadout mass px py pz) := by
  refine ⟨?_, cubical_phase_readout_intertwines mass px py pz hmass, ?_⟩
  · intro phase
    funext component
    fin_cases component <;>
      simp [cubicalPhaseReadout]
  · intro candidate hposition hintertwines
    exact cubical_phase_readout_unique_from_intertwining
      mass px py pz hmass candidate hposition hintertwines

/-! ## Honest residual coordinate freedom -/

/-- A scalar second-order operator can never distinguish a first-order root
from its global negative.  This is a mathematical obstruction to claiming
that the action Hessian alone selects every first-order convention. -/
theorem operator_root_global_sign_is_invisible
    (operator : CubicalCell8 → CubicalCell8)
    (hodd : ∀ amplitude corner,
      operator (fun inner => -amplitude inner) corner =
        -operator amplitude corner)
    (amplitude : CubicalCell8) :
    (fun corner =>
      -operator (fun inner => -operator amplitude inner) corner) =
      operator (operator amplitude) := by
  funext corner
  rw [hodd (operator amplitude) corner]
  simp

/-- Compact boundary for what is and is not selected.  The Kähler--Dirac
root plus native-position normalization uniquely fixes the readout, while the
global sign and the two commuting cubical flavor charts remain genuine
coordinate freedoms. -/
structure CubicalReadoutCharacterizationCertificate : Prop where
  uniqueNormalizedIntertwiner : ∀ mass px py pz, mass ≠ 0 →
    ∀ candidate : UniformTwoChannelPhase → CubicalCell4,
      (∀ phase, cubicalStandardPosition (candidate phase) = phase.1) →
      (∀ phase,
        candidate (uniformTwoChannelKleinGordonVector mass px py pz phase) =
          fun component =>
            -I * cubicalStandardHamiltonian mass px py pz
              (candidate phase) component) →
      candidate = cubicalPhaseReadout mass px py pz
  rootSignInvisible : ∀ (operator : CubicalCell8 → CubicalCell8),
    (∀ amplitude corner,
      operator (fun inner => -amplitude inner) corner =
        -operator amplitude corner) →
    ∀ amplitude,
    (fun corner =>
      -operator (fun inner => -operator amplitude inner) corner) =
      operator (operator amplitude)
  bothCubicalFlavorsRemain : ∀ (r : ℝ) momentum phase,
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
          (uniformActionToStandardDirac r momentum phase)))

theorem cubical_readout_characterization :
    CubicalReadoutCharacterizationCertificate where
  uniqueNormalizedIntertwiner := fun mass px py pz hmass candidate
      hposition hintertwines =>
    cubical_phase_readout_unique_from_intertwining
      mass px py pz hmass candidate hposition hintertwines
  rootSignInvisible := fun operator hodd amplitude =>
    operator_root_global_sign_is_invisible operator hodd amplitude
  bothCubicalFlavorsRemain := uniform_action_dirac_has_both_cubical_copies

end
end LeanDirac.V2

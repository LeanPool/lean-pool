/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CubicalPhaseCharacterization
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

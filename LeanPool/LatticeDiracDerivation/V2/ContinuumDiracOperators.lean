/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativePhaseReadout

/-! # Continuum Dirac operators and plane waves -/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

/-- The Dirac transport matrix associated with the chosen axis. -/
def cubicalVelocityOperator (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  fun component => (c19ContinuumSpeed : ℂ) * cubicalAlpha axis z component

theorem cubical_velocity_sum {Mode : Type*} [Fintype Mode]
    (axis : Fin 3) (field : Mode → CubicalCell4) :
    cubicalVelocityOperator axis
        (fun component => ∑ mode, field mode component) =
      fun component => ∑ mode,
        cubicalVelocityOperator axis (field mode) component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalVelocityOperator, cubicalAlpha, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      Finset.mul_sum]

theorem cubical_velocity_mul (axis : Fin 3) (scale : ℂ) (spinor : CubicalCell4) :
    cubicalVelocityOperator axis (fun component => scale * spinor component) =
      fun component => scale * cubicalVelocityOperator axis spinor component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cubicalVelocityOperator, cubicalAlpha, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring

/-- The mode time evolution given by minus the imaginary unit times the Hamiltonian. -/
def cubicalDiracTimeDerivative
    (mass : ℝ) (z : CubicalCell4)
    (spatialDerivative : Fin 3 → CubicalCell4) : CubicalCell4 :=
  fun component =>
    -I * (mass : ℂ) * cubicalStandardBeta z component -
      ∑ axis : Fin 3,
        cubicalVelocityOperator axis
          (spatialDerivative axis) component

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
  have velocity (axis : Fin 3) :
      cubicalVelocityOperator axis (uniformPlaneWaveSpatialDerivative momentum z axis) component =
        (I * (momentum axis : ℂ)) * cubicalVelocityOperator axis z component :=
    congrFun (cubical_velocity_mul axis (I * (momentum axis : ℂ)) z) component
  simp only [cubicalDiracTimeDerivative, velocity]
  simp only [Fin.sum_univ_three, cubicalVelocityOperator, cubicalAlpha,
    uniformContinuumPx, uniformContinuumPy, uniformContinuumPz, c19ScaledMomentum,
    Complex.ofReal_mul, cubicalStandardHamiltonian, cubicalStandardSpatial]
  ring

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

end
end LeanDirac.V2

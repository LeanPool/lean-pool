/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumCurrentBridge
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumDiscreteTime

/-!
# Position-space free Dirac equation for finite Fourier fields

The operator theorem is first proved mode by mode because C19 translation is
diagonal in lattice momentum.  This module performs the inverse step for an
arbitrary finite superposition.  It proves the displayed position-space
Dirac equation, not merely its dispersion relation.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Mode : Type*}

open Complex BigOperators
noncomputable section

/-- Synthesize a position-space spinor from a finite family of lattice modes. -/
def finiteDiracField [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      uniformActionToStandardDirac r (momentum mode) (phase mode) component

/-- Synthesize the time derivative by evolving each Fourier spinor with its generator. -/
def finiteDiracTimeDerivative [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      uniformActionToStandardDirac r (momentum mode)
        (uniformVacuumContinuumGenerator r
          (momentum mode) (phase mode)) component

/-- The exact finite-C19 native tangent derivative, before replacing the
C19 symbol by its quadratic continuum part. -/
def finiteNativeDiracTimeDerivative [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      uniformActionToStandardDirac r (momentum mode)
        (uniformVacuumNativeGenerator r
          (momentum mode) (phase mode)) component

/-- The exact mapped C19 remainder in position space.  It is displayed as a
separate field rather than absorbed into the Dirac operator. -/
def finiteMappedC19Remainder [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    cubicLatticeCharacter (momentum mode) site *
      uniformActionToStandardDirac r (momentum mode)
        (uniformNativeSpatialDefectPhase
          (momentum mode) (phase mode)) component

/-- The coordinate derivative from differentiating each plane-wave factor. -/
def finiteDiracSpatialDerivative [Fintype Mode]
    (axis : Fin 3) (r : ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    I * ((momentum mode axis : ℝ) : ℂ) *
      cubicLatticeCharacter (momentum mode) site *
        uniformActionToStandardDirac r
          (momentum mode) (phase mode) component

theorem cubical_standard_beta_sum [Fintype Mode]
    (field : Mode → CubicalCell4) :
    cubicalStandardBeta (fun component => ∑ mode, field mode component) =
      fun component => ∑ mode, cubicalStandardBeta (field mode) component := by
  funext component
  fin_cases component <;> simp [cubicalStandardBeta]

theorem cubical_velocity_sum [Fintype Mode]
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

theorem cubical_dirac_time_derivative_sum [Fintype Mode]
    (mass : ℝ) (field : Mode → CubicalCell4)
    (spatialDerivative : Mode → Fin 3 → CubicalCell4) :
    cubicalDiracTimeDerivative mass
        (fun component => ∑ mode, field mode component)
        (fun axis component => ∑ mode,
          spatialDerivative mode axis component) =
      fun component => ∑ mode,
        cubicalDiracTimeDerivative mass (field mode)
          (spatialDerivative mode) component := by
  funext component
  simp only [cubicalDiracTimeDerivative, cubical_standard_beta_sum, cubical_velocity_sum,
    Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem cubical_dirac_time_derivative_mul (scale : ℂ) (mass : ℝ)
    (field : CubicalCell4) (spatialDerivative : Fin 3 → CubicalCell4) :
    cubicalDiracTimeDerivative mass (fun component => scale * field component)
        (fun axis component => scale * spatialDerivative axis component) =
      fun component =>
        scale * cubicalDiracTimeDerivative mass field spatialDerivative component := by
  funext component
  fin_cases component <;>
    simp [cubicalDiracTimeDerivative, cubicalVelocityOperator, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY, cubicalStandardAlphaZ,
      Fin.sum_univ_succ] <;> ring

/-- Every finite superposition of action-derived continuum tangent modes
obeys the full four-component position-space free Dirac equation. -/
theorem finite_native_tangent_obeys_position_space_dirac [Fintype Mode]
    (r : ℝ) (hr : r ≠ 0)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    finiteDiracTimeDerivative r momentum phase site =
      cubicalDiracTimeDerivative r
        (finiteDiracField r momentum phase site)
        (fun axis =>
          finiteDiracSpatialDerivative axis r momentum phase site) := by
  rw [show finiteDiracTimeDerivative r momentum phase site =
      fun component => ∑ mode,
        cubicLatticeCharacter (momentum mode) site *
          cubicalDiracTimeDerivative r
            (uniformActionToStandardDirac r
              (momentum mode) (phase mode))
            (uniformPlaneWaveSpatialDerivative (momentum mode)
              (uniformActionToStandardDirac r
                (momentum mode) (phase mode))) component by
    funext component
    unfold finiteDiracTimeDerivative
    apply Finset.sum_congr rfl
    intro mode _
    rw [uniform_readout_tangent_is_position_dirac
      r hr (momentum mode) (phase mode)]]
  rw [show finiteDiracField r momentum phase site =
      fun component => ∑ mode,
        (fun component =>
          cubicLatticeCharacter (momentum mode) site *
            uniformActionToStandardDirac r
              (momentum mode) (phase mode) component) component by rfl]
  rw [show (fun axis =>
      finiteDiracSpatialDerivative axis r momentum phase site) =
      fun axis component => ∑ mode,
        cubicLatticeCharacter (momentum mode) site *
          uniformPlaneWaveSpatialDerivative (momentum mode)
            (uniformActionToStandardDirac r
              (momentum mode) (phase mode)) axis component by
    funext axis component
    unfold finiteDiracSpatialDerivative
      uniformPlaneWaveSpatialDerivative
    apply Finset.sum_congr rfl
    intro mode _
    ring]
  rw [cubical_dirac_time_derivative_sum]
  funext component
  apply Finset.sum_congr rfl
  intro mode _
  exact (congrFun (cubical_dirac_time_derivative_mul _ _ _ _) component).symm

theorem finite_native_time_derivative_splits [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    finiteNativeDiracTimeDerivative r momentum phase site =
      fun component =>
        finiteDiracTimeDerivative r momentum phase site component +
          finiteMappedC19Remainder r momentum phase site component := by
  funext component
  unfold finiteNativeDiracTimeDerivative finiteDiracTimeDerivative
    finiteMappedC19Remainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mode _
  rw [uniform_native_generator_exact_defect]
  rw [show uniformActionToStandardDirac r (momentum mode)
      (fun channel =>
          (uniformVacuumContinuumGenerator r
            (momentum mode) (phase mode)).1 channel +
            (uniformNativeSpatialDefectPhase
              (momentum mode) (phase mode)).1 channel,
       fun channel =>
          (uniformVacuumContinuumGenerator r
            (momentum mode) (phase mode)).2 channel +
            (uniformNativeSpatialDefectPhase
              (momentum mode) (phase mode)).2 channel) =
      fun output =>
        uniformActionToStandardDirac r (momentum mode)
            (uniformVacuumContinuumGenerator r
              (momentum mode) (phase mode)) output +
          uniformActionToStandardDirac r (momentum mode)
            (uniformNativeSpatialDefectPhase
              (momentum mode) (phase mode)) output by
    unfold uniformActionToStandardDirac
    exact cubical_phase_readout_add _ _ _ _ _ _]
  ring

/-- Exact discrete position-space statement: the native C19 tangent equals
the continuum free-Dirac field equation plus the explicit C19 remainder. -/
theorem finite_native_c19_obeys_position_dirac_with_remainder [Fintype Mode]
    (r : ℝ) (hr : r ≠ 0)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    finiteNativeDiracTimeDerivative r momentum phase site =
      fun component =>
        cubicalDiracTimeDerivative r
          (finiteDiracField r momentum phase site)
          (fun axis =>
            finiteDiracSpatialDerivative axis r momentum phase site)
          component +
        finiteMappedC19Remainder r momentum phase site component := by
  rw [finite_native_time_derivative_splits]
  rw [finite_native_tangent_obeys_position_space_dirac r hr]

end
end LeanDirac.V2

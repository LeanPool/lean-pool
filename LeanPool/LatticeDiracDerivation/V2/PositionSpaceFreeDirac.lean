/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.ContinuumDiracOperators

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

/-- Inverse Fourier synthesis of an arbitrary finite family of spinor coefficients. -/
def finiteFourierSynthesis [Fintype Mode]
    (momentum : Mode → LatticeMomentum) (field : Mode → CubicalCell4)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode, cubicLatticeCharacter (momentum mode) site * field mode component

/-- Synthesis after differentiating each plane-wave factor in the given direction. -/
def finiteFourierSpatialDerivative [Fintype Mode]
    (axis : Fin 3) (momentum : Mode → LatticeMomentum) (field : Mode → CubicalCell4)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  fun component => ∑ mode,
    I * ((momentum mode axis : ℝ) : ℂ) * cubicLatticeCharacter (momentum mode) site *
      field mode component

/-- Synthesize a position-space spinor from a finite family of lattice modes. -/
def finiteDiracField [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  finiteFourierSynthesis momentum
    (fun mode => uniformActionToStandardDirac r (momentum mode)
      (phase mode)) site

/-- Synthesize the time derivative by evolving each Fourier spinor with its generator. -/
def finiteDiracTimeDerivative [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  finiteFourierSynthesis momentum
    (fun mode => uniformActionToStandardDirac r (momentum mode)
      (uniformVacuumContinuumGenerator r (momentum mode) (phase mode))) site

/-- The exact finite-C19 native tangent derivative, before replacing the
C19 symbol by its quadratic continuum part. -/
def finiteNativeDiracTimeDerivative [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  finiteFourierSynthesis momentum
    (fun mode => uniformActionToStandardDirac r (momentum mode)
      (uniformVacuumNativeGenerator r (momentum mode) (phase mode))) site

/-- The exact mapped C19 remainder in position space.  It is displayed as a
separate field rather than absorbed into the Dirac operator. -/
def finiteMappedC19Remainder [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  finiteFourierSynthesis momentum
    (fun mode => uniformActionToStandardDirac r (momentum mode)
      (uniformNativeSpatialDefectPhase (momentum mode) (phase mode))) site

/-- The coordinate derivative from differentiating each plane-wave factor. -/
def finiteDiracSpatialDerivative [Fintype Mode]
    (axis : Fin 3) (r : ℝ)
    (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) : CubicalCell4 :=
  finiteFourierSpatialDerivative axis momentum
    (fun mode => uniformActionToStandardDirac r (momentum mode)
      (phase mode)) site

theorem cubical_standard_beta_sum [Fintype Mode]
    (field : Mode → CubicalCell4) :
    cubicalStandardBeta (fun component => ∑ mode, field mode component) =
      fun component => ∑ mode, cubicalStandardBeta (field mode) component := by
  funext component
  fin_cases component <;> simp [cubicalStandardBeta]

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
  have beta_scale :
      cubicalStandardBeta (fun component => scale * field component) =
        fun component => scale * cubicalStandardBeta field component := by
    funext component
    fin_cases component <;> simp [cubicalStandardBeta]
  funext component
  simp only [cubicalDiracTimeDerivative, beta_scale, cubical_velocity_mul, ← Finset.mul_sum]
  ring

/-- Lift a family of plane-wave Dirac equations to its finite Fourier field. -/
theorem finite_fourier_sum_obeys_position_space_dirac [Fintype Mode]
    (mass : ℝ) (momentum : Mode → LatticeMomentum) (field timeDerivative : Mode → CubicalCell4)
    (equation : ∀ mode, timeDerivative mode = cubicalDiracTimeDerivative mass (field mode)
      (uniformPlaneWaveSpatialDerivative (momentum mode) (field mode)))
    (site : InfiniteCubicSite) :
    finiteFourierSynthesis momentum timeDerivative site =
      cubicalDiracTimeDerivative mass (finiteFourierSynthesis momentum field site)
        (fun axis => finiteFourierSpatialDerivative axis momentum field site) := by
  have spatial :
      (fun axis => finiteFourierSpatialDerivative axis momentum field site) =
      fun axis component => ∑ mode,
        cubicLatticeCharacter (momentum mode) site *
          uniformPlaneWaveSpatialDerivative (momentum mode) (field mode) axis component := by
    funext axis component
    apply Finset.sum_congr rfl
    intro mode _
    unfold uniformPlaneWaveSpatialDerivative
    ring
  unfold finiteFourierSynthesis
  rw [spatial, cubical_dirac_time_derivative_sum]
  funext component
  apply Finset.sum_congr rfl
  intro mode _
  rw [equation mode, cubical_dirac_time_derivative_mul]

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
  exact finite_fourier_sum_obeys_position_space_dirac r momentum
    (fun mode => uniformActionToStandardDirac r (momentum mode) (phase mode))
    (fun mode => uniformActionToStandardDirac r (momentum mode)
      (uniformVacuumContinuumGenerator r (momentum mode) (phase mode)))
    (fun mode => uniform_readout_tangent_is_position_dirac r hr (momentum mode) (phase mode))
    site

/-- Synthesize the native generator as a continuum evolution and an explicit C19 defect
in any additive spinor readout. -/
theorem finite_fourier_native_time_derivative_splits [Fintype Mode]
    (mass : ℝ) (momentum : Mode → LatticeMomentum) (phase : Mode → UniformTwoChannelPhase)
    (readout : Mode → UniformTwoChannelPhase → CubicalCell4)
    (readout_add : ∀ mode (first second : UniformTwoChannelPhase),
      readout mode (first + second) = readout mode first + readout mode second)
    (site : InfiniteCubicSite) :
    finiteFourierSynthesis momentum
        (fun mode => readout mode (uniformVacuumNativeGenerator mass (momentum mode) (phase mode)))
        site =
      finiteFourierSynthesis momentum
        (fun mode => readout mode
          (uniformVacuumContinuumGenerator mass (momentum mode) (phase mode)))
        site +
      finiteFourierSynthesis momentum
        (fun mode => readout mode (uniformNativeSpatialDefectPhase (momentum mode) (phase mode)))
        site := by
  funext component
  simp only [Pi.add_apply, finiteFourierSynthesis, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mode _
  rw [uniform_native_generator_exact_defect]
  change _ * readout mode (_ + _) component = _
  rw [readout_add, Pi.add_apply, mul_add]

theorem finite_native_time_derivative_splits [Fintype Mode]
    (r : ℝ) (momentum : Mode → LatticeMomentum)
    (phase : Mode → UniformTwoChannelPhase)
    (site : InfiniteCubicSite) :
    finiteNativeDiracTimeDerivative r momentum phase site =
      fun component =>
        finiteDiracTimeDerivative r momentum phase site component +
          finiteMappedC19Remainder r momentum phase site component :=
  finite_fourier_native_time_derivative_splits r momentum phase
    (fun mode => uniformActionToStandardDirac r (momentum mode))
    (fun mode => uniform_action_readout_add r (momentum mode)) site

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

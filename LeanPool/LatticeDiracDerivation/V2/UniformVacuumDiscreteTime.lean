/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativePhaseReadout

/-!
# The actual centered two-layer update through the same Dirac readout

The second phase coordinate here is the backward-difference velocity
`(q_n-q_(n-1))/dt`.  The update below is exactly the native centered
recurrence, not a separately supplied exponential branch.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex Filter Topology
noncomputable section

/-- Reconstruct the previous position from the centered phase data. -/
def uniformCenteredPrevious (dt : ℝ)
    (phase : UniformTwoChannelPhase) : UniformCell2 :=
  fun component => phase.1 component - (dt : ℂ) * phase.2 component

/-- Advance the two-layer centered recurrence by one position. -/
def uniformCenteredNext
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformCell2 :=
  fun component =>
    2 * phase.1 component - uniformCenteredPrevious dt phase component -
      (dt ^ 2 * uniformVacuumModalSquare r momentum : ℝ) * phase.1 component

/-- The centered lattice step written in native phase coordinates. -/
def uniformCenteredPhaseStep
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  let next := uniformCenteredNext r dt momentum phase
  (next, fun component =>
    phase.2 component -
      (dt * uniformVacuumModalSquare r momentum : ℝ) * phase.1 component)

theorem uniform_centered_next_is_native_recurrence
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformCenteredNext r dt momentum phase = fun component =>
      2 * phase.1 component - uniformCenteredPrevious dt phase component -
        (dt ^ 2 * uniformVacuumModalSquare r momentum : ℝ) *
          phase.1 component := rfl

/-- Divide the phase increment of the centered step by the time step. -/
def uniformCenteredDifferenceQuotient
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (fun component =>
      ((uniformCenteredPhaseStep r dt momentum phase).1 component -
        phase.1 component) / (dt : ℂ),
    fun component =>
      ((uniformCenteredPhaseStep r dt momentum phase).2 component -
        phase.2 component) / (dt : ℂ))

/-- The part of the centered-update defect caused only by representing the
second-order state with a backward-difference velocity. It is exactly linear
in `dt`; no spatial approximation is included here. -/
def uniformCenteredTemporalDefect
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (fun component =>
      -(dt * uniformVacuumModalSquare r momentum : ℝ) * phase.1 component,
    fun _ => 0)

/-- The finite-C19 spatial defect, separated from the timestep defect. -/
abbrev uniformCenteredSpatialDefect := uniformNativeSpatialDefectPhase

/-- The explicit defect between the centered difference quotient and the free Dirac evolution. -/
def uniformCenteredDiracDefect
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  uniformCenteredTemporalDefect r dt momentum phase + uniformCenteredSpatialDefect momentum phase

theorem uniform_centered_dirac_defect_splits
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformCenteredDiracDefect r dt momentum phase =
      (fun component =>
          (uniformCenteredTemporalDefect r dt momentum phase).1 component +
            (uniformCenteredSpatialDefect momentum phase).1 component,
       fun component =>
          (uniformCenteredTemporalDefect r dt momentum phase).2 component +
            (uniformCenteredSpatialDefect momentum phase).2 component) := rfl

/-- Exact joint time-and-space defect of the actual centered update. -/
theorem uniform_centered_difference_quotient_splits
    (r dt : ℝ) (hdt : dt ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformCenteredDifferenceQuotient r dt momentum phase =
      (fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).1 component +
          (uniformCenteredDiracDefect r dt momentum phase).1 component,
       fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).2 component +
          (uniformCenteredDiracDefect r dt momentum phase).2 component) := by
  have temporal :
      uniformCenteredDifferenceQuotient r dt momentum phase =
        uniformVacuumNativeGenerator r momentum phase +
          uniformCenteredTemporalDefect r dt momentum phase := by
    apply Prod.ext <;> funext component
    · simp only [uniformCenteredDifferenceQuotient, uniformCenteredPhaseStep,
        uniformCenteredNext, uniformCenteredPrevious, uniformVacuumNativeGenerator,
        uniformCenteredTemporalDefect, Prod.fst_add, Pi.add_apply]
      field_simp [hdt]
      push_cast
      ring
    · simp only [uniformCenteredDifferenceQuotient, uniformCenteredPhaseStep,
        uniformVacuumNativeGenerator, uniformVacuumModalAcceleration, uniformCenteredTemporalDefect,
        Prod.snd_add, Pi.add_apply, add_zero, uniformVacuumModalSquare]
      field_simp [hdt]
      push_cast
      ring
  rw [temporal, uniform_native_generator_exact_defect]
  change uniformVacuumContinuumGenerator r momentum phase +
        uniformNativeSpatialDefectPhase momentum phase +
        uniformCenteredTemporalDefect r dt momentum phase =
    uniformVacuumContinuumGenerator r momentum phase +
      (uniformCenteredTemporalDefect r dt momentum phase +
        uniformNativeSpatialDefectPhase momentum phase)
  ac_rfl

/-- The actual two-layer native difference quotient, transported through the
same cubical phase-space readout, equals the Dirac flow plus one displayed
defect containing both `dt` and the C19 spatial remainder. -/
theorem uniform_centered_update_through_same_dirac_readout
    (r dt : ℝ) (hr : r ≠ 0) (hdt : dt ≠ 0)
    (momentum : LatticeMomentum) (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (uniformCenteredDifferenceQuotient r dt momentum phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (r : ℂ)
          (uniformContinuumPx momentum)
          (uniformContinuumPy momentum)
          (uniformContinuumPz momentum)
          (uniformActionToStandardDirac r momentum phase) component +
        uniformActionToStandardDirac r momentum
          (uniformCenteredDiracDefect r dt momentum phase) component := by
  rw [uniform_centered_difference_quotient_splits r dt hdt]
  rw [show uniformActionToStandardDirac r momentum
      (fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).1 component +
          (uniformCenteredDiracDefect r dt momentum phase).1 component,
       fun component =>
        (uniformVacuumContinuumGenerator r momentum phase).2 component +
          (uniformCenteredDiracDefect r dt momentum phase).2 component) =
      fun component =>
        uniformActionToStandardDirac r momentum
            (uniformVacuumContinuumGenerator r momentum phase) component +
          uniformActionToStandardDirac r momentum
            (uniformCenteredDiracDefect r dt momentum phase) component by
    unfold uniformActionToStandardDirac
    exact cubical_phase_readout_add _ _ _ _ _ _]
  rw [uniform_action_tangent_intertwines_cubical_dirac r hr]

/-- Through the exact same four-component readout used by the Dirac
intertwining, the temporal defect is multiplication by `dt` of one fixed
four-component vector. -/
theorem uniform_centered_temporal_defect_readout_scale
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (uniformCenteredTemporalDefect r dt momentum phase) =
      fun component =>
        (dt : ℂ) *
          uniformActionToStandardDirac r momentum
            (uniformCenteredTemporalDefect r 1 momentum phase) component := by
  have hscale : uniformCenteredTemporalDefect r dt momentum phase =
      uniformTwoChannelScale (dt : ℂ) (uniformCenteredTemporalDefect r 1 momentum phase) := by
    apply Prod.ext
    · funext component
      simp [uniformCenteredTemporalDefect, uniformTwoChannelScale]
      ring
    · funext component
      simp [uniformCenteredTemporalDefect, uniformTwoChannelScale]
  rw [hscale]
  unfold uniformActionToStandardDirac
  exact cubical_phase_readout_scale _ _ _ _ _ _

/-- The actual centered-update temporal defect vanishes at first order in
the timestep through the same fixed native-to-Dirac readout. The C19 spatial
remainder is intentionally not hidden in this limit. -/
theorem uniform_centered_temporal_defect_readout_tends_to_zero
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) (component : Fin 4) :
    Tendsto
      (fun dt : ℝ =>
        uniformActionToStandardDirac r momentum
          (uniformCenteredTemporalDefect r dt momentum phase) component)
      (nhds 0) (nhds 0) := by
  have hfun :
      (fun dt : ℝ =>
        uniformActionToStandardDirac r momentum
          (uniformCenteredTemporalDefect r dt momentum phase) component) =
      (fun dt : ℝ =>
        (dt : ℂ) *
          uniformActionToStandardDirac r momentum
            (uniformCenteredTemporalDefect r 1 momentum phase) component) := by
    funext dt
    exact congrFun
      (uniform_centered_temporal_defect_readout_scale
        r dt momentum phase) component
  rw [hfun]
  let value : ℂ :=
    uniformActionToStandardDirac r momentum
      (uniformCenteredTemporalDefect r 1 momentum phase) component
  have hcontinuous : ContinuousAt (fun dt : ℝ => (dt : ℂ) * value) 0 :=
    (Complex.continuous_ofReal.mul
      (continuous_const : Continuous (fun _ : ℝ => value))).continuousAt
  have htendsto :
      Tendsto (fun dt : ℝ => (dt : ℂ) * value) (nhds 0)
        (nhds (((0 : ℝ) : ℂ) * value)) := hcontinuous
  simpa [value] using htendsto

end
end LeanDirac.V2

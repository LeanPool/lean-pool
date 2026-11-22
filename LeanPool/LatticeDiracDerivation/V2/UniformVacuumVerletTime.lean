/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.FirstPrinciplesFreeDirac

/-!
# Second-order phase coordinates for the native centered recurrence

The centered two-layer position recurrence is second order, but the raw
backward difference `(q_n-q_(n-1))/dt` is only a first-order velocity
coordinate.  The acceleration-corrected coordinate below is reconstructed
from the same two committed layers and gives the velocity-Verlet form of the
identical recurrence.  Its one-step local defect relative to the exact native
tangent generator is exactly cubic in `dt`.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex Filter Topology
noncomputable section

/-- The position one step earlier reconstructed from a Verlet phase. -/
def uniformVerletPrevious
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformCell2 := fun component =>
  phase.1 component - (dt : ℂ) * phase.2 component -
    ((dt ^ 2 / 2) * uniformVacuumModalSquare r momentum : ℝ) *
      phase.1 component

/-- The next position of the exact native centered recurrence. -/
def uniformVerletNext
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformCell2 := fun component =>
  phase.1 component + (dt : ℂ) * phase.2 component -
    ((dt ^ 2 / 2) * uniformVacuumModalSquare r momentum : ℝ) *
      phase.1 component

/-- The updated phase velocity after the centered position update. -/
def uniformVerletNextVelocity
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformCell2 := fun component =>
  phase.2 component -
    ((dt / 2) * uniformVacuumModalSquare r momentum : ℝ) *
      (phase.1 component + uniformVerletNext r dt momentum phase component)

/-- The native centered recurrence expressed as a single Verlet phase step. -/
def uniformVerletPhaseStep
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (uniformVerletNext r dt momentum phase,
    uniformVerletNextVelocity r dt momentum phase)

/-- The acceleration-corrected velocity is reconstructed from the current
and previous committed layers only. -/
theorem uniform_verlet_velocity_from_committed_layers
    (r dt : ℝ) (hdt : dt ≠ 0) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) (component : Fin 2) :
    (phase.1 component -
        uniformVerletPrevious r dt momentum phase component) / (dt : ℂ) -
      (((dt / 2) * uniformVacuumModalSquare r momentum : ℝ) : ℂ) *
        phase.1 component = phase.2 component := by
  simp [uniformVerletPrevious]
  field_simp [hdt]
  ring

/-- The position part is exactly the original centered two-layer recurrence;
the phase-space rewrite has not changed the native integrator. -/
theorem uniform_verlet_position_is_centered_recurrence
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVerletNext r dt momentum phase = fun component =>
      2 * phase.1 component -
        uniformVerletPrevious r dt momentum phase component -
        (dt ^ 2 * uniformVacuumModalSquare r momentum : ℝ) *
          phase.1 component := by
  funext component
  simp [uniformVerletNext, uniformVerletPrevious]
  ring

/-- The second-order Taylor phase obtained from the exact native generator. -/
def uniformNativeTaylor2
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  let first := uniformVacuumNativeGenerator r momentum phase
  let second := uniformVacuumNativeGenerator r momentum first
  (fun component =>
      phase.1 component + (dt : ℂ) * first.1 component +
        ((dt ^ 2 / 2 : ℝ) : ℂ) * second.1 component,
    fun component =>
      phase.2 component + (dt : ℂ) * first.2 component +
        ((dt ^ 2 / 2 : ℝ) : ℂ) * second.2 component)

/-- The difference between the Verlet step and the native second-order Taylor phase. -/
def uniformVerletLocalDefect
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : UniformTwoChannelPhase :=
  (fun _ => 0,
    fun component =>
      (((dt ^ 3 / 4) * (uniformVacuumModalSquare r momentum) ^ 2 : ℝ) : ℂ) *
        phase.1 component)

/-- Exact local-error identity.  The actual centered native step equals the
second-order Taylor step of its own action-derived tangent generator plus a
single displayed `dt ^ 3` defect. -/
theorem uniform_verlet_step_is_second_order
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVerletPhaseStep r dt momentum phase =
      (fun component =>
          (uniformNativeTaylor2 r dt momentum phase).1 component +
            (uniformVerletLocalDefect r dt momentum phase).1 component,
        fun component =>
          (uniformNativeTaylor2 r dt momentum phase).2 component +
            (uniformVerletLocalDefect r dt momentum phase).2 component) := by
  apply Prod.ext <;> funext component
  · simp [uniformVerletPhaseStep, uniformVerletNext,
      uniformNativeTaylor2, uniformVacuumNativeGenerator,
      uniformVacuumModalAcceleration, uniformVerletLocalDefect]
    ring
  · simp [uniformVerletPhaseStep, uniformVerletNextVelocity,
      uniformVerletNext, uniformNativeTaylor2,
      uniformVacuumNativeGenerator, uniformVacuumModalAcceleration,
      uniformVerletLocalDefect]
    ring

theorem uniform_verlet_local_defect_readout_scale
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformActionToStandardDirac r momentum
        (uniformVerletLocalDefect r dt momentum phase) =
      fun component =>
        ((dt ^ 3 : ℝ) : ℂ) *
          uniformActionToStandardDirac r momentum
            (uniformVerletLocalDefect r 1 momentum phase) component := by
  funext component
  fin_cases component <;>
    simp [uniformActionToStandardDirac, uniformVerletLocalDefect,
      cubicalPhaseReadout, cubicalPhaseLower, cubicalSpatialLower,
      cubicalUpperEmbedding, cubicalStandardSpatial,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;>
    ring

/-- Dividing the one-step error by `dt ^ 2` still tends to zero.  This is the
local consistency ingredient for a globally second-order convergence proof;
stability is established separately and no accumulated-error bound is
claimed by this theorem alone. -/
theorem uniform_verlet_local_defect_is_little_o_dt_sq
    (r : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) (component : Fin 4) :
    Tendsto
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          uniformActionToStandardDirac r momentum
              (uniformVerletLocalDefect r dt momentum phase) component /
            ((dt ^ 2 : ℝ) : ℂ))
      (nhds 0) (nhds 0) := by
  have hfun :
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          uniformActionToStandardDirac r momentum
                (uniformVerletLocalDefect r dt momentum phase) component /
              ((dt ^ 2 : ℝ) : ℂ)) =
      (fun dt : ℝ =>
        (dt : ℂ) *
          uniformActionToStandardDirac r momentum
            (uniformVerletLocalDefect r 1 momentum phase) component) := by
    funext dt
    by_cases hdt : dt = 0
    · subst dt
      simp
    · rw [ite_eq_right hdt,
        congrFun (uniform_verlet_local_defect_readout_scale
          r dt momentum phase) component]
      push_cast
      field_simp [hdt]
  rw [hfun]
  simpa using ((Complex.continuous_ofReal.tendsto 0).mul
    tendsto_const_nhds)

end
end LeanDirac.V2

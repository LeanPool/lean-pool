/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumVerletTime

/-!
# Stability of the native centered update on each Fourier mode

The preceding module proves an exact cubic one-step consistency defect.  This
module adds the separate stability statement needed before that fact may be
used in a convergence argument.  For every fixed native C19 mode, the
velocity-Verlet form of the unchanged two-layer recurrence preserves an exact
modified quadratic energy.  Inside `0 <= dt ^ 2 Omega ^ 2 <= 4` that energy is
nonnegative and controls the iterates.

No global-in-time error theorem is claimed here: preservation and local
consistency are the two proved ingredients, not a replacement for an
accumulated-error estimate.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex
noncomputable section

/-- The dimensionless squared time step times the squared native frequency. -/
def uniformVerletStabilityParameter
    (r dt : ℝ) (momentum : LatticeMomentum) : ℝ :=
  dt ^ 2 * uniformVacuumModalSquare r momentum

/-- The strict stability condition for the modified energy of the native centered recurrence. -/
def uniformVerletStable
    (r dt : ℝ) (momentum : LatticeMomentum) : Prop :=
  0 ≤ uniformVerletStabilityParameter r dt momentum ∧
    uniformVerletStabilityParameter r dt momentum ≤ 4

/-- The position coefficient in the modified discrete energy. -/
def uniformVerletPositionWeight
    (r dt : ℝ) (momentum : LatticeMomentum) : ℝ :=
  uniformVacuumModalSquare r momentum *
    (1 - uniformVerletStabilityParameter r dt momentum / 4)

/-- The quadratic energy conserved by the native Verlet phase step. -/
def uniformVerletModifiedEnergy
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : ℝ :=
  uniformCell2Density phase.2 +
    uniformVerletPositionWeight r dt momentum *
      uniformCell2Density phase.1

theorem uniform_vacuum_modal_square_nonnegative
    (r : ℝ) (momentum : LatticeMomentum) :
    0 ≤ uniformVacuumModalSquare r momentum := by
  unfold uniformVacuumModalSquare
  exact add_nonneg (sq_nonneg r) (c19_transport_symbol_nonnegative momentum)

theorem uniform_verlet_stability_parameter_nonnegative
    (r dt : ℝ) (momentum : LatticeMomentum) :
    0 ≤ uniformVerletStabilityParameter r dt momentum := by
  unfold uniformVerletStabilityParameter
  exact mul_nonneg (sq_nonneg dt)
    (uniform_vacuum_modal_square_nonnegative r momentum)

theorem uniform_verlet_position_factor_bounds
    (r dt : ℝ) (momentum : LatticeMomentum)
    (hstable : uniformVerletStable r dt momentum) :
    0 ≤ 1 - uniformVerletStabilityParameter r dt momentum / 4 ∧
      1 - uniformVerletStabilityParameter r dt momentum / 4 ≤ 1 := by
  rcases hstable with ⟨hzero, hfour⟩
  constructor <;> linarith

theorem uniform_verlet_position_weight_nonnegative
    (r dt : ℝ) (momentum : LatticeMomentum)
    (hstable : uniformVerletStable r dt momentum) :
    0 ≤ uniformVerletPositionWeight r dt momentum := by
  unfold uniformVerletPositionWeight
  exact mul_nonneg
    (uniform_vacuum_modal_square_nonnegative r momentum)
    (uniform_verlet_position_factor_bounds r dt momentum hstable).1

/-- The exact invariant quadratic form of velocity Verlet.  This algebraic
identity holds for every timestep; positivity requires the stability window
and is proved separately. -/
theorem uniform_verlet_modified_energy_invariant
    (r dt : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) :
    uniformVerletModifiedEnergy r dt momentum
        (uniformVerletPhaseStep r dt momentum phase) =
      uniformVerletModifiedEnergy r dt momentum phase := by
  simp [uniformVerletModifiedEnergy, uniformVerletPositionWeight,
    uniformVerletStabilityParameter, uniformVerletPhaseStep,
    uniformVerletNextVelocity, uniformVerletNext,
    uniformCell2Density, Complex.normSq, Fin.sum_univ_succ]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Iterate the native Verlet update a specified number of times. -/
def uniformVerletIterate
    (r dt : ℝ) (momentum : LatticeMomentum) :
    ℕ → UniformTwoChannelPhase → UniformTwoChannelPhase
  | 0, phase => phase
  | n + 1, phase =>
      uniformVerletPhaseStep r dt momentum
        (uniformVerletIterate r dt momentum n phase)

/-- Exact bounded-power statement in the modified energy norm. -/
theorem uniform_verlet_modified_energy_iterate
    (r dt : ℝ) (momentum : LatticeMomentum)
    (n : ℕ) (phase : UniformTwoChannelPhase) :
    uniformVerletModifiedEnergy r dt momentum
        (uniformVerletIterate r dt momentum n phase) =
      uniformVerletModifiedEnergy r dt momentum phase := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show uniformVerletIterate r dt momentum (n + 1) phase =
          uniformVerletPhaseStep r dt momentum
            (uniformVerletIterate r dt momentum n phase) by rfl,
        uniform_verlet_modified_energy_invariant, ih]

theorem uniform_verlet_modified_energy_nonnegative
    (r dt : ℝ) (momentum : LatticeMomentum)
    (hstable : uniformVerletStable r dt momentum)
    (phase : UniformTwoChannelPhase) :
    0 ≤ uniformVerletModifiedEnergy r dt momentum phase := by
  unfold uniformVerletModifiedEnergy
  exact add_nonneg
    (Finset.sum_nonneg (fun component _ =>
      Complex.normSq_nonneg (phase.2 component)))
    (mul_nonneg
      (uniform_verlet_position_weight_nonnegative r dt momentum hstable)
      (Finset.sum_nonneg (fun component _ =>
        Complex.normSq_nonneg (phase.1 component))))

/-- Every iterate's native velocity norm is bounded by the initial modified
energy throughout the exact stability window. -/
theorem uniform_verlet_velocity_bounded_by_initial_energy
    (r dt : ℝ) (momentum : LatticeMomentum)
    (hstable : uniformVerletStable r dt momentum)
    (n : ℕ) (phase : UniformTwoChannelPhase) :
    uniformCell2Density
        (uniformVerletIterate r dt momentum n phase).2 ≤
      uniformVerletModifiedEnergy r dt momentum phase := by
  rw [← uniform_verlet_modified_energy_iterate r dt momentum n phase]
  unfold uniformVerletModifiedEnergy
  have hposition : 0 ≤
      uniformVerletPositionWeight r dt momentum *
        uniformCell2Density
          (uniformVerletIterate r dt momentum n phase).1 :=
    mul_nonneg
      (uniform_verlet_position_weight_nonnegative r dt momentum hstable)
      (Finset.sum_nonneg (fun component _ =>
        Complex.normSq_nonneg
          ((uniformVerletIterate r dt momentum n phase).1 component)))
  linarith

end
end LeanDirac.V2

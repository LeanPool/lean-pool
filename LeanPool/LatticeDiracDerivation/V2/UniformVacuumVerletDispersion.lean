/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumVerletStability
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Exact stable Verlet dispersion and its continuum-frequency limit

The actual native two-layer recurrence is a scalar oscillator on each C19
Fourier channel.  This file gives its exact stable angular frequency, proves
the corresponding characteristic root solves that recurrence for every
iteration, and proves that frequency converges to the action-derived modal
frequency as the timestep tends to zero.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex Filter Topology
noncomputable section

/-- The nonnegative square root of the exact native squared mode frequency. -/
def uniformVacuumModalFrequency
    (r : ℝ) (momentum : LatticeMomentum) : ℝ :=
  Real.sqrt (uniformVacuumModalSquare r momentum)

theorem uniform_vacuum_modal_frequency_nonnegative
    (r : ℝ) (momentum : LatticeMomentum) :
    0 ≤ uniformVacuumModalFrequency r momentum :=
  Real.sqrt_nonneg _

theorem uniform_vacuum_modal_frequency_square
    (r : ℝ) (momentum : LatticeMomentum) :
    uniformVacuumModalFrequency r momentum ^ 2 =
      uniformVacuumModalSquare r momentum := by
  exact Real.sq_sqrt (uniform_vacuum_modal_square_nonnegative r momentum)

/-- The exact stable Verlet angular frequency.  `dslope` supplies the
continuous value at `dt = 0`, so no arbitrary branch value is inserted. -/
def uniformVerletAngularFrequency
    (r dt : ℝ) (momentum : LatticeMomentum) : ℝ :=
  let omega := uniformVacuumModalFrequency r momentum
  omega * dslope Real.arcsin 0 (dt * omega / 2)

@[simp] theorem uniform_verlet_angular_frequency_zero
    (r : ℝ) (momentum : LatticeMomentum) :
    uniformVerletAngularFrequency r 0 momentum =
      uniformVacuumModalFrequency r momentum := by
  simp [uniformVerletAngularFrequency, dslope_same, Real.deriv_arcsin]

/-- The exact discrete frequency converges to the native action-Hessian
frequency, rather than merely matching one Taylor coefficient. -/
theorem uniform_verlet_angular_frequency_tends_to_native
    (r : ℝ) (momentum : LatticeMomentum) :
    Tendsto (fun dt : ℝ => uniformVerletAngularFrequency r dt momentum)
      (nhds 0) (nhds (uniformVacuumModalFrequency r momentum)) := by
  let omega := uniformVacuumModalFrequency r momentum
  have harcsin : DifferentiableAt ℝ Real.arcsin 0 :=
    (Real.hasDerivAt_arcsin (by norm_num) (by norm_num)).differentiableAt
  have hslope : ContinuousAt (dslope Real.arcsin 0) 0 :=
    continuousAt_dslope_same.mpr harcsin
  have hinner : Tendsto (fun dt : ℝ => dt * omega / 2)
      (nhds 0) (nhds 0) := by
    have hid : Tendsto (fun dt : ℝ => dt) (nhds 0) (nhds 0) := tendsto_id
    simpa using ((hid.mul_const omega).div_const (2 : ℝ))
  have hcomp : Tendsto
      (fun dt : ℝ => dslope Real.arcsin 0 (dt * omega / 2))
      (nhds 0) (nhds (dslope Real.arcsin 0 0)) :=
    hslope.tendsto.comp hinner
  have hmul : Tendsto
      (fun dt : ℝ => omega * dslope Real.arcsin 0 (dt * omega / 2))
      (nhds 0) (nhds (omega * dslope Real.arcsin 0 0)) :=
    tendsto_const_nhds.mul hcomp
  simpa [uniformVerletAngularFrequency, omega, dslope_same,
    Real.deriv_arcsin] using hmul

theorem uniform_verlet_step_angle
    (r dt : ℝ) (momentum : LatticeMomentum) :
    dt * uniformVerletAngularFrequency r dt momentum =
      2 * Real.arcsin
        (dt * uniformVacuumModalFrequency r momentum / 2) := by
  let omega := uniformVacuumModalFrequency r momentum
  have hslope := sub_smul_dslope Real.arcsin 0 (dt * omega / 2)
  change (dt * omega / 2 - 0) * dslope Real.arcsin 0
      (dt * omega / 2) = Real.arcsin (dt * omega / 2) -
        Real.arcsin 0 at hslope
  simp only [sub_zero, Real.arcsin_zero] at hslope
  unfold uniformVerletAngularFrequency
  dsimp only
  linear_combination 2 * hslope

/-- Exact discrete dispersion relation of the stable native recurrence. -/
theorem uniform_verlet_exact_dispersion
    (r dt : ℝ) (momentum : LatticeMomentum)
    (hstable : uniformVerletStable r dt momentum) :
    Real.cos (dt * uniformVerletAngularFrequency r dt momentum) =
      1 - uniformVerletStabilityParameter r dt momentum / 2 := by
  let omega := uniformVacuumModalFrequency r momentum
  let x := dt * omega / 2
  have homega : omega ^ 2 = uniformVacuumModalSquare r momentum := by
    exact uniform_vacuum_modal_frequency_square r momentum
  have hxSq : x ^ 2 =
      uniformVerletStabilityParameter r dt momentum / 4 := by
    change (dt * omega / 2) ^ 2 =
      dt ^ 2 * uniformVacuumModalSquare r momentum / 4
    rw [show (dt * omega / 2) ^ 2 = dt ^ 2 * omega ^ 2 / 4 by ring,
      homega]
  have hxSqLe : x ^ 2 ≤ 1 := by
    rw [hxSq]
    linarith [hstable.2]
  have hxLower : -1 ≤ x := by
    nlinarith [sq_nonneg (x - 1)]
  have hxUpper : x ≤ 1 := by
    nlinarith [sq_nonneg (x + 1)]
  rw [uniform_verlet_step_angle]
  change Real.cos (2 * Real.arcsin x) = _
  rw [Real.cos_two_mul']
  rw [Real.sin_arcsin hxLower hxUpper]
  have htrig := Real.sin_sq_add_cos_sq (Real.arcsin x)
  rw [Real.sin_arcsin hxLower hxUpper] at htrig
  nlinarith [hxSq]

/-- The complex multiplier on the negative-angle characteristic branch of the centered
recurrence. -/
def uniformVerletCharacteristicRoot
    (r dt : ℝ) (momentum : LatticeMomentum) : ℂ :=
  Complex.exp
    (-I * ((dt * uniformVerletAngularFrequency r dt momentum : ℝ) : ℂ))

theorem uniform_verlet_characteristic_root_norm
    (r dt : ℝ) (momentum : LatticeMomentum) :
    ‖uniformVerletCharacteristicRoot r dt momentum‖ = 1 := by
  let theta := dt * uniformVerletAngularFrequency r dt momentum
  unfold uniformVerletCharacteristicRoot
  change ‖Complex.exp (-I * (theta : ℂ))‖ = 1
  rw [show -I * (theta : ℂ) = ((-theta : ℝ) : ℂ) * I by
    push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The exact unit-modulus root of the native centered recurrence. -/
theorem uniform_verlet_characteristic_root_equation
    (r dt : ℝ) (momentum : LatticeMomentum)
    (hstable : uniformVerletStable r dt momentum) :
    uniformVerletCharacteristicRoot r dt momentum ^ 2 -
        ((2 - uniformVerletStabilityParameter r dt momentum : ℝ) : ℂ) *
          uniformVerletCharacteristicRoot r dt momentum + 1 = 0 := by
  let theta := dt * uniformVerletAngularFrequency r dt momentum
  have hcos : Real.cos theta =
      1 - uniformVerletStabilityParameter r dt momentum / 2 :=
    uniform_verlet_exact_dispersion r dt momentum hstable
  have hroot : uniformVerletCharacteristicRoot r dt momentum =
      (Real.cos theta : ℂ) - I * (Real.sin theta : ℂ) := by
    unfold uniformVerletCharacteristicRoot
    change Complex.exp (-I * (theta : ℂ)) = _
    rw [show -I * (theta : ℂ) = ((-theta : ℝ) : ℂ) * I by
      push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp
    ring
  rw [hroot]
  change ((Real.cos theta : ℂ) - I * (Real.sin theta : ℂ)) ^ 2 -
      ((2 - uniformVerletStabilityParameter r dt momentum : ℝ) : ℂ) *
        ((Real.cos theta : ℂ) - I * (Real.sin theta : ℂ)) + 1 = 0
  have htrig := Real.sin_sq_add_cos_sq theta
  apply Complex.ext
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    rw [hcos] at htrig ⊢
    nlinarith
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    rw [hcos]
    ring

/-- Every amplitude generated by the stable characteristic root satisfies
the actual two-layer native position recurrence at every discrete time. -/
theorem uniform_verlet_characteristic_solution
    (r dt : ℝ) (momentum : LatticeMomentum)
    (hstable : uniformVerletStable r dt momentum)
    (amplitude : ℂ) (n : ℕ) :
    uniformVerletCharacteristicRoot r dt momentum ^ (n + 2) * amplitude =
      (2 - uniformVerletStabilityParameter r dt momentum : ℝ) *
          (uniformVerletCharacteristicRoot r dt momentum ^ (n + 1) *
            amplitude) -
        uniformVerletCharacteristicRoot r dt momentum ^ n * amplitude := by
  have hchar := uniform_verlet_characteristic_root_equation
    r dt momentum hstable
  let root := uniformVerletCharacteristicRoot r dt momentum
  have hroot : root ^ 2 =
      ((2 - uniformVerletStabilityParameter r dt momentum : ℝ) : ℂ) *
        root - 1 := by
    dsimp [root] at hchar ⊢
    linear_combination hchar
  rw [show n + 2 = n + 2 by rfl, pow_add, hroot]
  rw [show n + 1 = n + 1 by rfl, pow_add]
  push_cast
  ring

end
end LeanDirac.V2

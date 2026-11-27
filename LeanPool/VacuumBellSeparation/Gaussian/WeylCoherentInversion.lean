/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.WeylVacuumIntegral
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeWeylProduct

/-!
# Displaced weak Weyl inversion

The actual unitary Weyl conjugation produces the Fourier phase of a
coherent projector. This identifies every scalar matrix element of that
projector as a Gaussian-weighted integral over the actual Weyl operators.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory ContinuousLinearMap
open scoped ComplexConjugate

theorem multiOscillatorWeyl_adjoint {m : ℕ} (w : MultiModePhaseSpace m) :
    (multiOscillatorWeyl w).adjoint = multiOscillatorWeyl (-w) := by
  have hi : multiOscillatorWeyl w * multiOscillatorWeyl (-w) = 1 := by
    rw [multiOscillatorWeyl_mul,
      weylPhase_neg_right (id : MultiModePhaseSpace m → MultiModePhaseSpace m)
        (fun _ _ => rfl), one_smul, add_neg_cancel, multiOscillatorWeyl_zero]
  have hs := Unitary.star_mul_self_of_mem (multiOscillatorWeyl_mem_unitary w)
  change star (multiOscillatorWeyl w) = _
  calc
    _ = star (multiOscillatorWeyl w) *
        (multiOscillatorWeyl w * multiOscillatorWeyl (-w)) := by rw [hi, mul_one]
    _ = _ := by rw [← mul_assoc, hs, one_mul]

/-- Coherent Fourier phase given by `Complex.exp (-2 * Complex.I * ((inner ℂ w z).im : ℂ))`. -/
def coherentFourierPhase {m : ℕ} (w z : MultiModePhaseSpace m) : ℂ :=
  Complex.exp (-2 * Complex.I * ((inner ℂ w z).im : ℂ))

theorem norm_coherentFourierPhase {m : ℕ} (w z : MultiModePhaseSpace m) :
    ‖coherentFourierPhase w z‖ = 1 := by
  simp [coherentFourierPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem multiOscillatorWeyl_conjugate {m : ℕ} (w z : MultiModePhaseSpace m) :
    multiOscillatorWeyl w * multiOscillatorWeyl z * (multiOscillatorWeyl w).adjoint =
      coherentFourierPhase w z • multiOscillatorWeyl z := by
  rw [multiOscillatorWeyl_adjoint, multiOscillatorWeyl_mul, smul_mul_assoc,
    multiOscillatorWeyl_mul, smul_smul,
    show w + z + -w = z by abel]
  congr 1
  rw [weylPhase, weylPhase, coherentFourierPhase, ← Complex.exp_add]
  congr 1
  have hself : (inner ℂ w w).im = 0 := by
    simpa only [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) w
  have hswap : (inner ℂ z w).im = -(inner ℂ w z).im := by
    simpa only [RCLike.im_to_complex] using inner_im_symm (𝕜 := ℂ) z w
  simp only [id_eq, inner_add_left, inner_neg_right, Complex.add_im,
    Complex.neg_im, hself, hswap, zero_add]
  push_cast
  ring

theorem multiOscillatorWeyl_exponential_zero {m : ℕ} (w : MultiModePhaseSpace m) :
    multiOscillatorWeyl w (multiExponentialVector (0 : Fin m → ℂ)) =
      multiCoherentVector w := by
  have hv : multiExponentialVector (0 : Fin m → ℂ) =
      multiCoherentVector (0 : MultiModePhaseSpace m) := by
    simp only [multiCoherentVector, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_div, neg_zero, Complex.ofReal_zero, Complex.exp_zero, one_smul, PiLp.zero_apply]
    rfl
  rw [hv, multiOscillatorWeyl_coherentVector,
    weylPhase_zero_right (id : MultiModePhaseSpace m → MultiModePhaseSpace m)
      (fun _ _ => rfl), one_smul, add_zero]

theorem inner_adjointWeyl_conjugate {m : ℕ} (w z : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    inner ℂ ((multiOscillatorWeyl w).adjoint x)
      (multiOscillatorWeyl z ((multiOscillatorWeyl w).adjoint y)) =
        coherentFourierPhase w z * inner ℂ x (multiOscillatorWeyl z y) := by
  rw [(multiOscillatorWeyl w).adjoint_inner_left]
  rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, multiOscillatorWeyl_conjugate,
    smul_apply, inner_smul_right]

theorem integral_coherentWeyl_kernel {m : ℕ} (w : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    (∫ z : Fin m → ℂ, weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        inner ℂ x (multiOscillatorWeyl (WithLp.toLp 2 z) y)) =
      (Real.pi : ℂ) ^ m * inner ℂ x (multiCoherentVector w) *
        inner ℂ (multiCoherentVector w) y := by
  have h := integral_gaussianWeyl_kernel
    ((multiOscillatorWeyl w).adjoint x) ((multiOscillatorWeyl w).adjoint y)
  simp only [inner_adjointWeyl_conjugate, ← mul_assoc] at h
  rw [(multiOscillatorWeyl w).adjoint_inner_left,
    (multiOscillatorWeyl w).adjoint_inner_right] at h
  simpa only [multiOscillatorWeyl_exponential_zero] using h

theorem integrable_coherentWeyl_kernel {m : ℕ} (w : MultiModePhaseSpace m)
    (x y : MultiModeOscillatorSpace m) :
    Integrable (fun z : Fin m → ℂ => weylVacuumWeight m z *
      coherentFourierPhase w (WithLp.toLp 2 z) *
        inner ℂ x (multiOscillatorWeyl (WithLp.toLp 2 z) y)) := by
  have h := (integrable_weylVacuumOrbit ((multiOscillatorWeyl w).adjoint y)).const_inner (𝕜 := ℂ)
    ((multiOscillatorWeyl w).adjoint x)
  simpa only [inner_smul_right, inner_adjointWeyl_conjugate, ← mul_assoc] using h

end VacuumBellSeparation.Gaussian

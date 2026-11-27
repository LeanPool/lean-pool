/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexGaussianBilinear
public import LeanPool.VacuumBellSeparation.Gaussian.CoherentRotationAveraging
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCanonicalThermalModel

/-!
# Gaussian-weighted Weyl inversion on the actual exponential vectors

The kernel is derived from the constructed Weyl action, including its
phase. Its genuine scalar Gaussian integral equals the vacuum rank-one
matrix element. Extension to arbitrary vectors is a separate continuity
step; this file makes no operator-norm Bochner integral assertion.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

theorem multiOscillatorWeyl_exponential_kernel {m : ℕ}
    (z a b : MultiModePhaseSpace m) :
    inner ℂ (multiExponentialVector (fun j => a j))
      (multiOscillatorWeyl z (multiExponentialVector (fun j => b j))) =
      Complex.exp (((-‖z‖ ^ 2 / 2 : ℝ) : ℂ) - inner ℂ z b + inner ℂ a (z + b)) := by
  rw [multiExponentialVector_eq_normalized, multiExponentialVector_eq_normalized,
    map_smul, multiOscillatorWeyl_coherentVector, inner_smul_left, inner_smul_right,
    inner_smul_right, inner_multiCoherentVector]
  change conj (Complex.exp ((‖a‖ ^ 2 / 2 : ℝ) : ℂ)) *
    (Complex.exp ((‖b‖ ^ 2 / 2 : ℝ) : ℂ) *
      (weylPhase id z b * weylKernel id a (z + b))) = _
  simp only [weylPhase, weylKernel, id_eq, ← Complex.exp_conj, Complex.conj_ofReal,
    ← Complex.exp_add]
  congr 1
  rw [norm_add_sq (𝕜 := ℂ)]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      RCLike.re_to_complex] <;> ring

theorem gaussianWeyl_exponential_kernel_product {m : ℕ}
    (z a b : Fin m → ℂ) :
    Complex.exp ((-‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 / 2 : ℝ) : ℂ) *
      inner ℂ (multiExponentialVector a)
        (multiOscillatorWeyl (WithLp.toLp 2 z) (multiExponentialVector b)) =
      Complex.exp (∑ j, conj (a j) * b j) *
        ∏ j, Complex.exp (((-‖z j‖ ^ 2 : ℝ) : ℂ) +
          conj (a j) * z j + (-b j) * conj (z j)) := by
  rw [multiOscillatorWeyl_exponential_kernel (WithLp.toLp 2 z)
    (WithLp.toLp 2 a) (WithLp.toLp 2 b), ← Complex.exp_add,
    ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  simp only [EuclideanSpace.norm_sq_eq, PiLp.inner_apply,
    PiLp.add_apply, RCLike.inner_apply', Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_sum]
  have hcomm : (∑ j, conj (z j) * b j) = ∑ j, b j * conj (z j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  rw [hcomm]
  norm_num; ring

theorem integrable_gaussianWeyl_exponential_kernel {m : ℕ} (a b : Fin m → ℂ) :
    Integrable (fun z : Fin m → ℂ =>
      Complex.exp ((-‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 / 2 : ℝ) : ℂ) *
        inner ℂ (multiExponentialVector a)
          (multiOscillatorWeyl (WithLp.toLp 2 z) (multiExponentialVector b))) := by
  simp_rw [gaussianWeyl_exponential_kernel_product]
  have h := integrable_multiComplexGaussianBilinear
    (s := fun _ : Fin m => 1) (fun _ => zero_lt_one)
    (fun j => conj (a j)) (fun j => -b j)
  simpa only [neg_one_mul] using h.const_mul (Complex.exp (∑ j, conj (a j) * b j))

/-- Scalar matrix element of weak Weyl inversion. The value is π^m
because both vacuum/exponential inner products are exactly one. -/
theorem integral_gaussianWeyl_exponential_kernel {m : ℕ} (a b : Fin m → ℂ) :
    (∫ z : Fin m → ℂ,
      Complex.exp ((-‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 / 2 : ℝ) : ℂ) *
        inner ℂ (multiExponentialVector a)
          (multiOscillatorWeyl (WithLp.toLp 2 z) (multiExponentialVector b))) =
      (Real.pi : ℂ) ^ m := by
  simp_rw [gaussianWeyl_exponential_kernel_product]
  rw [integral_const_mul]
  have h := integral_multiComplexGaussianBilinear
    (s := fun _ : Fin m => 1) (fun _ => zero_lt_one)
    (fun j => conj (a j)) (fun j => -b j)
  simp only [neg_one_mul, div_one, Complex.ofReal_one] at h
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Complex.exp_sum]
  have hc : (∑ j, conj (a j) * b j) + (∑ j, conj (a j) * -b j) = 0 := by
    simp only [mul_neg, Finset.sum_neg_distrib, add_neg_cancel]
  calc
    _ = (Real.pi : ℂ) ^ m * (Complex.exp (∑ j, conj (a j) * b j) *
        Complex.exp (∑ j, conj (a j) * -b j)) := by ring
    _ = _ := by rw [← Complex.exp_add, hc, Complex.exp_zero, mul_one]

end VacuumBellSeparation.Gaussian

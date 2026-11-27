/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Complex Gaussian integration with independent holomorphic coefficients

The two coefficients need not be conjugates or imaginary phases. The
literal Lebesgue integral and integrability follow from the pinned real
two-dimensional Gaussian theorem. This is used for weak Weyl inversion
on exponential vectors, before any trace or representation uniqueness.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

private theorem complex_gaussian_bilinear_coordinates (s : ℝ) (a b z : ℂ) :
    -(s : ℂ) * ∑ i : Fin 2, ((Complex.measurableEquivPi z i : ℝ) : ℂ) ^ 2 +
      ∑ i : Fin 2, (![a + b, Complex.I * (a - b)] i) *
        ((Complex.measurableEquivPi z i : ℝ) : ℂ) =
      ((-s * ‖z‖ ^ 2 : ℝ) : ℂ) + a * z + b * conj z := by
  simp only [Fin.sum_univ_two, Complex.measurableEquivPi_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.sq_norm,
    Complex.normSq_apply]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, pow_two] <;> ring

theorem integrable_complex_gaussian_bilinear {s : ℝ} (hs : 0 < s) (a b : ℂ) :
    Integrable (fun z : ℂ =>
      Complex.exp (((-s * ‖z‖ ^ 2 : ℝ) : ℂ) + a * z + b * conj z)) := by
  have h := Complex.volume_preserving_equiv_pi.integrable_comp_of_integrable
    (GaussianFourier.integrable_cexp_neg_mul_sum_add
      (b := (s : ℂ)) (show 0 < (s : ℂ).re from hs) ![a + b, Complex.I * (a - b)])
  simpa only [Function.comp_def, complex_gaussian_bilinear_coordinates] using h

theorem integral_complex_gaussian_bilinear {s : ℝ} (hs : 0 < s) (a b : ℂ) :
    (∫ z : ℂ, Complex.exp (((-s * ‖z‖ ^ 2 : ℝ) : ℂ) + a * z + b * conj z)) =
      ((Real.pi / s : ℝ) : ℂ) * Complex.exp (a * b / (s : ℂ)) := by
  have hc := Complex.volume_preserving_equiv_pi.integral_comp
    Complex.measurableEquivPi.measurableEmbedding
    (fun x : Fin 2 → ℝ => Complex.exp (-(s : ℂ) * ∑ i, (x i : ℂ) ^ 2 +
      ∑ i, (![a + b, Complex.I * (a - b)] i) * (x i : ℂ)))
  simp only [complex_gaussian_bilinear_coordinates] at hc
  rw [hc, GaussianFourier.integral_cexp_neg_mul_sum_add
    (show 0 < (s : ℂ).re from hs)]
  norm_num only [Fintype.card_fin, Nat.cast_ofNat,
    div_self (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  rw [Complex.ofReal_div]
  congr 2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [show (s : ℂ) ≠ 0 by exact_mod_cast hs.ne']
  ring_nf
  simp [Complex.I_sq]; ring

theorem integrable_multiComplexGaussianBilinear {m : ℕ} {s : Fin m → ℝ}
    (hs : ∀ j, 0 < s j) (a b : Fin m → ℂ) :
    Integrable (fun z : Fin m → ℂ => ∏ j,
      Complex.exp (((-s j * ‖z j‖ ^ 2 : ℝ) : ℂ) + a j * z j + b j * conj (z j))) :=
  Integrable.fintype_prod fun j => integrable_complex_gaussian_bilinear (hs j) (a j) (b j)

theorem integral_multiComplexGaussianBilinear {m : ℕ} {s : Fin m → ℝ}
    (hs : ∀ j, 0 < s j) (a b : Fin m → ℂ) :
    (∫ z : Fin m → ℂ, ∏ j,
      Complex.exp (((-s j * ‖z j‖ ^ 2 : ℝ) : ℂ) + a j * z j + b j * conj (z j))) =
      ∏ j, ((Real.pi / s j : ℝ) : ℂ) * Complex.exp (a j * b j / (s j : ℂ)) := by
  calc
    _ = ∏ j, ∫ z : ℂ,
        Complex.exp (((-s j * ‖z‖ ^ 2 : ℝ) : ℂ) + a j * z + b j * conj z) :=
      integral_fintype_prod_volume_eq_prod (fun j (z : ℂ) =>
        Complex.exp (((-s j * ‖z‖ ^ 2 : ℝ) : ℂ) + a j * z + b j * conj z))
    _ = _ := ?_
  apply Finset.prod_congr rfl
  intro j _
  exact integral_complex_gaussian_bilinear (hs j) (a j) (b j)

end VacuumBellSeparation.Gaussian

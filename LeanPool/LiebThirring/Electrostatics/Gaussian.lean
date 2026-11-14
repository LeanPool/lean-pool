/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import LeanPool.LiebThirring.Defs.Coulomb

/-!
# Gaussian representations of the Coulomb kernel

Equation, including the infinite diagonal.

Pointwise completion of squares, prior to integration.
-/

public section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace LiebThirring

theorem measurable_coulombKernel : Measurable (Function.uncurry coulombKernel) := by
  exact ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv

theorem coulombKernel_symm (x y : Position) : coulombKernel x y = coulombKernel y x := by
  simp only [coulombKernel, norm_sub_rev]

theorem inverse_eq_lintegral_gaussian (s : ℝ) (hs : 0 ≤ s) :
    (ENNReal.ofReal s)⁻¹ =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (2 / Real.sqrt Real.pi * Real.exp (-(t ^ 2 * s ^ 2))) := by
  by_cases hzero : s = 0
  · subst s
    simp only [sq, mul_zero, neg_zero, Real.exp_zero, mul_one]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioi]
    simp only [ENNReal.ofReal_zero, ENNReal.inv_zero]
    exact (ENNReal.mul_top (by positivity)).symm
  · have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
    have hi : Integrable (fun t : ℝ => 2 / Real.sqrt Real.pi *
        Real.exp (-(t ^ 2 * s ^ 2))) (volume.restrict (Ioi 0)) := by
      have hg := (integrable_exp_neg_mul_sq (sq_pos_of_pos hpos)).restrict (s := Ioi 0)
      convert hg.const_mul (2 / Real.sqrt Real.pi) using 1
      ext t
      rw [mul_comm (t ^ 2), neg_mul]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => by positivity)), integral_const_mul]
    have heq : (∫ t : ℝ in Ioi 0, Real.exp (-(t ^ 2 * s ^ 2))) =
        Real.sqrt (Real.pi / s ^ 2) / 2 := by
      convert integral_gaussian_Ioi (s ^ 2) using 1
      congr 1
      ext t
      rw [mul_comm (t ^ 2), neg_mul]
    rw [heq, Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hs]
    have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    have halgebra : 2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / s / 2) = s⁻¹ := by
      field_simp
    rw [halgebra, ENNReal.ofReal_inv_of_pos hpos]

/-- Equation (2.1), including the infinite diagonal. -/
theorem coulombKernel_eq_lintegral_gaussian (x y : Position) :
    coulombKernel x y =
      ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (2 / Real.sqrt Real.pi * Real.exp (-(t ^ 2 * ‖x - y‖ ^ 2))) :=
  inverse_eq_lintegral_gaussian ‖x - y‖ (norm_nonneg _)

theorem norm_midpoint_sq (x y z : Position) :
    ‖x - z‖ ^ 2 + ‖y - z‖ ^ 2 =
      2 * ‖z - (1 / 2 : ℝ) • (x + y)‖ ^ 2 + ‖x - y‖ ^ 2 / 2 := by
  simp only [norm_sub_sq_real, norm_smul,
    real_inner_smul_right, inner_add_right, Real.norm_eq_abs]
  rw [real_inner_comm z x, real_inner_comm z y]
  simp only [mul_pow]
  rw [norm_add_sq_real]
  norm_num
  ring
/-- Pointwise completion of squares, prior to integration. -/
theorem gaussian_product_eq (b : ℝ) (x y z : Position) :
    Real.exp (-2 * b * ‖x - z‖ ^ 2) * Real.exp (-2 * b * ‖y - z‖ ^ 2) =
      Real.exp (-b * ‖x - y‖ ^ 2) *
        Real.exp (-(4 * b) * ‖z - (1 / 2 : ℝ) • (x + y)‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  calc
    -2 * b * ‖x - z‖ ^ 2 + -2 * b * ‖y - z‖ ^ 2 =
        -2 * b * (‖x - z‖ ^ 2 + ‖y - z‖ ^ 2) := by ring
    _ = _ := by rw [norm_midpoint_sq]; ring

theorem integral_gaussian_product (b : ℝ) (hb : 0 < b) (x y : Position) :
    (∫ z : Position, Real.exp (-2 * b * ‖x - z‖ ^ 2) *
      Real.exp (-2 * b * ‖y - z‖ ^ 2)) =
        Real.exp (-b * ‖x - y‖ ^ 2) * (Real.pi / (4 * b)) ^ (3 / 2 : ℝ) := by
  simp_rw [gaussian_product_eq]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun z : Position => Real.exp (-(4 * b) * ‖z‖ ^ 2))]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  simp only [Position, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]

theorem integrable_gaussian_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Position => Real.exp (-b * ‖z‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := Position) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  convert h using 1
  ext z
  simp only [zero_mul, add_zero]
  change Real.exp (-b * ‖z‖ ^ 2) = (Complex.exp (-↑b * (↑‖z‖ : ℂ) ^ 2)).re
  rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.exp_ofReal_re]

/-- Absolute integrability of the product in (2.2). -/
theorem integrable_gaussian_product {b : ℝ} (hb : 0 < b) (x y : Position) :
    Integrable (fun z : Position => Real.exp (-2 * b * ‖x - z‖ ^ 2) *
      Real.exp (-2 * b * ‖y - z‖ ^ 2)) := by
  simp_rw [gaussian_product_eq]
  exact ((integrable_gaussian_norm (by positivity : 0 < 4 * b)).comp_sub_right
    ((1 / 2 : ℝ) • (x + y))).const_mul _

/-- Spatial Gaussian convolution mass in three Euclidean dimensions. -/
@[expose] noncomputable def gaussianMass (b : ℝ) : ℝ :=
  (Real.pi / (4 * b)) ^ (3 / 2 : ℝ)

/-- A nonnegative Gaussian feature with scalar normalization `c`. -/
@[expose] noncomputable def gaussianFeature (c b : ℝ) (x z : Position) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (c / gaussianMass b) * Real.exp (-2 * b * ‖x - z‖ ^ 2))

/-- Cancellation of the square root normalization. -/
theorem sqrt_mul_sqrt_mul (a u v : ℝ) (ha : 0 ≤ a) :
    (Real.sqrt a * u) * (Real.sqrt a * v) = a * (u * v) := by
  calc
    _ = (Real.sqrt a) ^ 2 * (u * v) := by ring
    _ = _ := by rw [Real.sq_sqrt ha]

/-- Integral Gram representation of a Gaussian kernel. -/
theorem lintegral_gaussianFeature_mul {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c)
    (x y : Position) :
    (∫⁻ z : Position, gaussianFeature c b x z * gaussianFeature c b y z) =
      ENNReal.ofReal (c * Real.exp (-b * ‖x - y‖ ^ 2)) := by
  have hm : 0 < gaussianMass b := Real.rpow_pos_of_pos (by positivity) _
  have hnormal : 0 ≤ c / gaussianMass b := div_nonneg hc hm.le
  simp only [gaussianFeature, ← ENNReal.ofReal_mul
    (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]
  simp_rw [sqrt_mul_sqrt_mul _ _ _ hnormal]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_gaussian_product hb x y).const_mul (c / gaussianMass b))
    (Filter.Eventually.of_forall (fun _ => by positivity)), integral_const_mul,
    integral_gaussian_product b hb x y]
  congr 1
  change c / gaussianMass b * (Real.exp (-b * ‖x - y‖ ^ 2) * gaussianMass b) = _
  field_simp

end LiebThirring
end

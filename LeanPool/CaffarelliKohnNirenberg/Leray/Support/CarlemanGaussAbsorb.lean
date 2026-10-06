/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussDerivatives
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar bounds for the Gaussian Carleman estimate

These inequalities combine `eq:carleman-I` of the Escauriaza–Seregin–Šverák manuscript with the integrated gradient
identity and the cross term in `eq:carleman-E` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

noncomputable section

namespace CKN

/-- The coefficient left after adding the gradient and phase-gradient terms. -/
theorem gaussCarleman_coefficient_le {q t : ℝ}
    (hq : 0 ≤ q) (ht : 0 < t) :
    -t + q * t ^ 2 * (1 / t - 1 / 3) ≤ q * t := by
  have htne : t ≠ 0 := ne_of_gt ht
  have h : t ^ 2 * (1 / t) = t := by
    field_simp [htne]
  have hqt : 0 ≤ q * t ^ 2 := mul_nonneg hq (sq_nonneg t)
  rw [mul_sub, mul_assoc q (t ^ 2) (1 / t), h]
  nlinarith only [hqt, ht]

/-- Cauchy–Schwarz and `I ≤ P` absorb the cross term with the constant `√6`. -/
theorem gaussCarleman_absorb {E I P C : ℝ}
    (hI : 0 ≤ I) (hIP : I ≤ P)
    (hE : E ≤ 3 * I + |C|)
    (hC : C ^ 2 ≤ 6 * I * P) :
    E ≤ (3 + Real.sqrt 6) * P := by
  have hP : 0 ≤ P := le_trans hI hIP
  have hsqrt : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hsqrt2 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hmul : I * P ≤ P * P := mul_le_mul_of_nonneg_right hIP hP
  have hC2 : C ^ 2 ≤ (Real.sqrt 6 * P) ^ 2 := by
    calc
      C ^ 2 ≤ 6 * I * P := hC
      _ ≤ 6 * P ^ 2 := by nlinarith only [hmul]
      _ = (Real.sqrt 6 * P) ^ 2 := by rw [mul_pow, hsqrt2]
  have habs : |C| ≤ Real.sqrt 6 * P := by
    have hnonneg : 0 ≤ Real.sqrt 6 * P := mul_nonneg hsqrt hP
    nlinarith only [hC2, hnonneg, abs_nonneg C, sq_abs C]
  nlinarith only [hE, habs, hIP, hP, hsqrt]

/-- The scalar estimate with the final unweighted coefficient. -/
theorem gaussCarleman_final_absorb {q J E I P : ℝ}
    (hJ : q * J = 3 * I) (hIP : I ≤ P)
    (hE : E ≤ (3 + Real.sqrt 6) * P) :
    q * J + 2 * E ≤ (9 + 2 * Real.sqrt 6) * P := by
  nlinarith only [hJ, hIP, hE]

/-- A pointwise Young bound for the Gaussian cross term, with the same
constant as the Cauchy–Schwarz estimate in `eq:carleman-E` (ESS). -/
theorem gaussCarleman_cross_pointwise {q t v L : ℝ}
    (hq : 1 ≤ q) (ht0 : 0 < t) (ht2 : t < 2) :
    |t ^ 2 * v * L| ≤ Real.sqrt 6 / 2 *
      (q / 3 * t * v ^ 2 + t ^ 2 * L ^ 2) := by
  let r : ℝ := Real.sqrt 6
  have hrpos : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr2 : r ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hcoeff : t ≤ 2 * q := by linarith only [hq, ht2]
  have hnonneg : 0 ≤ t * v ^ 2 := mul_nonneg (le_of_lt ht0) (sq_nonneg v)
  have hmul := mul_le_mul_of_nonneg_right hcoeff hnonneg
  have hX : (t * v) ^ 2 ≤ 6 * (q / 3 * t * v ^ 2) := by
    nlinarith only [hmul]
  have hsq : 0 ≤ (|t * v| - r * |t * L|) ^ 2 := sq_nonneg _
  have hyoung : 2 * r * |(t * v) * (t * L)| ≤
      (t * v) ^ 2 + 6 * (t * L) ^ 2 := by
    rw [sub_sq, mul_pow, hr2, sq_abs, sq_abs] at hsq
    rw [abs_mul]
    nlinarith only [hsq]
  have hcross : 2 * r * |t ^ 2 * v * L| ≤
      6 * (q / 3 * t * v ^ 2 + t ^ 2 * L ^ 2) := by
    have heq : t ^ 2 * v * L = (t * v) * (t * L) := by ring
    rw [heq]
    nlinarith only [hyoung, hX]
  have htarget : 2 * r * (r / 2 *
      (q / 3 * t * v ^ 2 + t ^ 2 * L ^ 2)) =
      6 * (q / 3 * t * v ^ 2 + t ^ 2 * L ^ 2) := by
    rw [← hr2]
    ring
  apply le_of_mul_le_mul_left (a := 2 * r) (a0 := by positivity)
  rw [htarget]
  exact hcross

/-- The integral Young bound and `I ≤ P` give the Gaussian energy constant. -/
theorem gaussCarleman_absorb_young {E I P C : ℝ}
    (hIP : I ≤ P) (hE : E ≤ 3 * I + |C|)
    (hC : |C| ≤ Real.sqrt 6 / 2 * (I + P)) :
    E ≤ (3 + Real.sqrt 6) * P := by
  have hr : 0 ≤ Real.sqrt 6 / 2 :=
    div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hmul : Real.sqrt 6 / 2 * I ≤ Real.sqrt 6 / 2 * P :=
    mul_le_mul_of_nonneg_left hIP hr
  nlinarith only [hIP, hE, hC, hmul]

end CKN

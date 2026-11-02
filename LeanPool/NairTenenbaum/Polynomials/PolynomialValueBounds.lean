/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialHeight

/-! # Power bounds for values under the height hypothesis -/

@[expose] public section

namespace NairTenenbaum

open Polynomial

theorem eval_natAbs_le_height_real (Q : ℤ[X]) {x : ℝ} (hx : 1 ≤ x)
    {n : ℤ} (hn : (n.natAbs : ℝ) ≤ 2 * x) :
    ((Q.eval n).natAbs : ℝ) ≤ (polynomialHeight Q : ℝ) * (Q.natDegree + 1) *
      (2 * x) ^ Q.natDegree := by
  have H : ((Q.eval n).natAbs : ℝ) ≤ (polynomialHeight Q : ℝ) * (Q.natDegree + 1) *
      (max 1 (n.natAbs : ℝ)) ^ Q.natDegree := by
    exact_mod_cast eval_natAbs_le_height Q n
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (max_le (by linarith) hn) _

/-- A uniform threshold absorbs the elementary coefficient-height constant.
The exponent has one unit of slack, avoiding any coefficient-dependent constant. -/
theorem eval_natAbs_le_rpow_of_height {Q : ℤ[X]} {g : ℕ} (hg : Q.natDegree = g)
    {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    (hheight : (polynomialHeight Q : ℝ) ^ δ ≤ x)
    (hlarge : ((g : ℝ) + 1) * 2 ^ g ≤ x) {n : ℤ} (hn : (n.natAbs : ℝ) ≤ 2 * x) :
    ((Q.eval n).natAbs : ℝ) ≤ x ^ ((g : ℝ) + 1 / δ + 1) := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hH : (polynomialHeight Q : ℝ) ≤ x ^ (1 / δ) := by
    have H := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) δ) hheight
      (by positivity : 0 ≤ 1 / δ)
    rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hδ.ne', Real.rpow_one] at H
    exact H
  have H := eval_natAbs_le_height_real Q hx hn
  rw [hg, mul_pow] at H
  calc
    _ ≤ (polynomialHeight Q : ℝ) * ((g : ℝ) + 1) * (2 ^ g * x ^ g) := H
    _ = ((g : ℝ) + 1) * 2 ^ g * (polynomialHeight Q : ℝ) * x ^ g := by ring
    _ ≤ x * (x ^ (1 / δ)) * x ^ g := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hlarge hH (Nat.cast_nonneg _) hx₀.le) (pow_nonneg hx₀.le _)
    _ = x ^ ((g : ℝ) + 1 / δ + 1) := by
      rw [← Real.rpow_natCast]
      nth_rw 1 [← Real.rpow_one x]
      rw [← Real.rpow_add hx₀, ← Real.rpow_add hx₀]
      congr 1
      ring

/-- Retaining the degree-only coefficient avoids losing a power of `x` when
bounding contributions that rely on a small positive exponent saving. -/
theorem eval_natAbs_le_const_rpow_of_height {Q : ℤ[X]} {g : ℕ} (hg : Q.natDegree = g)
    {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    (hheight : (polynomialHeight Q : ℝ) ^ δ ≤ x) {n : ℤ} (hn : (n.natAbs : ℝ) ≤ 2 * x) :
    ((Q.eval n).natAbs : ℝ) ≤ (((g : ℝ) + 1) * 2 ^ g) * x ^ ((g : ℝ) + 1 / δ) := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hH : (polynomialHeight Q : ℝ) ≤ x ^ (1 / δ) := by
    have H := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) δ) hheight
      (by positivity : 0 ≤ 1 / δ)
    rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hδ.ne', Real.rpow_one] at H
    exact H
  have H := eval_natAbs_le_height_real Q hx hn
  rw [hg, mul_pow] at H
  calc
    _ ≤ (polynomialHeight Q : ℝ) * ((g : ℝ) + 1) * (2 ^ g * x ^ g) := H
    _ = (((g : ℝ) + 1) * 2 ^ g) * ((polynomialHeight Q : ℝ) * x ^ g) := by ring
    _ ≤ (((g : ℝ) + 1) * 2 ^ g) * (x ^ (1 / δ) * x ^ g) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH (pow_nonneg hx₀.le _)) (by
        positivity)
    _ = _ := by
      rw [← Real.rpow_natCast x g, ← Real.rpow_add hx₀, add_comm (1 / δ)]

end NairTenenbaum

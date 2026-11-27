/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentCoordinates
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Actual complex-plane Gaussian moments

The radial moment is the pinned Gamma integral over complex Lebesgue
measure. Off-diagonal moments vanish by a genuine measure-preserving
rotation: a root of minus one changes the monomial's sign. These are
scalar integral foundations for coherent resolution and Gaussian density
identification, not an assumed resolution-of-identity formula.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

theorem integral_radial_monomial_eq_zero_of_lt (g : ℝ → ℝ) {m n : ℕ}
    (hmn : m < n) :
    (∫ z : ℂ, (g ‖z‖ : ℂ) * conj z ^ m * z ^ n) = 0 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (Nat.sub_pos_of_lt hmn)
  have hunorm : ‖u‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg u)
      (Nat.ne_of_gt (Nat.sub_pos_of_lt hmn))).mp
    simpa only [norm_pow, norm_neg, norm_one] using congrArg norm hu
  let c : Circle := ⟨u, mem_sphere_zero_iff_norm.mpr hunorm⟩
  have hunit : conj u * u = 1 := by rw [Complex.conj_mul', hunorm]; norm_num
  have hphase : conj u ^ m * u ^ n = -1 := by
    calc
      conj u ^ m * u ^ n = conj u ^ m * (u ^ m * u ^ (n - m)) := by
        rw [← pow_add, Nat.add_sub_of_le hmn.le]
      _ = (conj u * u) ^ m * u ^ (n - m) := by rw [mul_pow]; ring
      _ = -1 := by rw [hunit, one_pow, one_mul, hu]
  let f : ℂ → ℂ := fun z => (g ‖z‖ : ℂ) * conj z ^ m * z ^ n
  have hrotate (z : ℂ) : f (rotation c z) = -f z := by
    change (g ‖u * z‖ : ℂ) * conj (u * z) ^ m * (u * z) ^ n =
      -((g ‖z‖ : ℂ) * conj z ^ m * z ^ n)
    rw [norm_mul, hunorm, one_mul, map_mul, mul_pow, mul_pow]
    calc
      (g ‖z‖ : ℂ) * (conj u ^ m * conj z ^ m) * (u ^ n * z ^ n) =
          (conj u ^ m * u ^ n) * ((g ‖z‖ : ℂ) * conj z ^ m * z ^ n) := by ring
      _ = _ := by rw [hphase]; ring
  have hrot := (rotation c).measurePreserving.integral_comp
    (rotation c).toHomeomorph.measurableEmbedding f
  simp_rw [hrotate] at hrot
  rw [integral_neg] at hrot
  have hz : (2 : ℂ) * (∫ z : ℂ, f z) = 0 := by linear_combination -hrot
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem integral_radial_monomial_eq_zero (g : ℝ → ℝ) {m n : ℕ} (hmn : m ≠ n) :
    (∫ z : ℂ, (g ‖z‖ : ℂ) * conj z ^ m * z ^ n) = 0 := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact integral_radial_monomial_eq_zero_of_lt g hlt
  · have h := congrArg conj (integral_radial_monomial_eq_zero_of_lt g hgt)
    rw [← integral_conj] at h
    simpa only [map_mul, map_pow, Complex.conj_ofReal, starRingEnd_self_apply,
      map_zero, mul_comm, mul_left_comm, mul_assoc] using h

theorem integral_gaussian_radial_even_moment {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ (2 * n) * Real.exp (-a * ‖z‖ ^ 2)) =
      Real.pi * (n.factorial : ℝ) / a ^ (n + 1) := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := (2 * n : ℕ)) (b := a) (by norm_num)
      (by have hn : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) ha
  have hquot : (((2 * n : ℕ) : ℝ) + 2) / 2 = (n : ℝ) + 1 := by push_cast; ring
  have hneg : -(((2 * n : ℕ) : ℝ) + 2) / 2 = -((n + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hquot, hneg, Real.Gamma_nat_eq_factorial, Real.rpow_neg ha.le,
    Real.rpow_natCast] at h
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  calc
    (∫ z : ℂ, ‖z‖ ^ (2 * n) * Real.exp (-a * ‖z‖ ^ 2)) =
        (2 * Real.pi / 2) * (a ^ (n + 1))⁻¹ * (n.factorial : ℝ) := h
    _ = _ := by ring

theorem integrable_gaussian_radial_even_moment {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ (2 * n) * Real.exp (-a * ‖z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussian_radial_even_moment ha]
  exact ne_of_gt (div_pos (mul_pos Real.pi_pos (by positivity)) (pow_pos ha _))

theorem integral_gaussian_monomial {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    (∫ z : ℂ, (Real.exp (-a * ‖z‖ ^ 2) : ℂ) * conj z ^ m * z ^ n) =
      if m = n then ((Real.pi * (n.factorial : ℝ) / a ^ (n + 1) : ℝ) : ℂ) else 0 := by
  split_ifs with hmn
  · subst m
    have hfun (z : ℂ) :
        (Real.exp (-a * ‖z‖ ^ 2) : ℂ) * conj z ^ n * z ^ n =
          ((‖z‖ ^ (2 * n) * Real.exp (-a * ‖z‖ ^ 2) : ℝ) : ℂ) := by
      rw [mul_assoc, ← mul_pow, Complex.conj_mul', ← pow_mul,
        Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    simp_rw [hfun]
    rw [integral_complex_ofReal, integral_gaussian_radial_even_moment ha]
  · exact integral_radial_monomial_eq_zero (fun r => Real.exp (-a * r ^ 2)) hmn

theorem integral_coherentCoefficient_norm_sq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ z : ℂ, Real.exp (-a * ‖z‖ ^ 2) * ‖coherentCoefficient z n‖ ^ 2) =
      Real.pi / a ^ (n + 1) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hfun (z : ℂ) :
      Real.exp (-a * ‖z‖ ^ 2) * ‖coherentCoefficient z n‖ ^ 2 =
        (‖z‖ ^ (2 * n) * Real.exp (-a * ‖z‖ ^ 2)) / (n.factorial : ℝ) := by
    rw [coherentCoefficient_norm_sq, ← pow_mul]
    ring
  simp_rw [hfun]
  rw [integral_div, integral_gaussian_radial_even_moment ha]
  field_simp

end VacuumBellSeparation.Gaussian

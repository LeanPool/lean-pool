/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight

/-! A polynomial box cutoff from the homogeneous coefficient-height bound.
The constants are explicit; only their dependence on dimension is needed in
the affine auxiliary-polynomial theorem. -/

@[expose] public section
namespace CCDN

private lemma box_le_of_logarithmic_height_bound {A B N D : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hN : 1 ≤ N) (hD : 0 ≤ D)
    (hheight : B / A ≤ N * Real.log N + N * D * Real.log B) :
    B ≤ 4 * A ^ 2 * N ^ 4 * (D + 1) ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogN : Real.log N ≤ N := Real.log_le_self hN0
  have hlogB : Real.log B ≤ 2 * Real.sqrt B := by
    have hh := Real.log_le_rpow_div hB0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have ht : 1 ≤ Real.sqrt B := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hB
  have ht0 : 0 < Real.sqrt B := by linarith
  have hNsq : N ≤ N ^ 2 := by nlinarith
  have hfirst : N * Real.log N ≤ N ^ 2 * Real.sqrt B := by
    calc
      _ ≤ N ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlogN hN0]
      _ ≤ _ := le_mul_of_one_le_right (sq_nonneg N) ht
  have hsecond : N * D * Real.log B ≤ 2 * N ^ 2 * D * Real.sqrt B := by
    calc
      _ ≤ N * D * (2 * Real.sqrt B) :=
        mul_le_mul_of_nonneg_left hlogB (mul_nonneg hN0 hD)
      _ ≤ N ^ 2 * D * (2 * Real.sqrt B) := by gcongr
      _ = _ := by ring
  have hmain : B ≤ (A * N ^ 2 * (1 + 2 * D)) * Real.sqrt B := by
    have hh := (div_le_iff₀ hA0).mp hheight
    have hh' := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hA0.le
    nlinarith only [hh, hh']
  have hroot : Real.sqrt B ≤ A * N ^ 2 * (1 + 2 * D) := by
    apply (mul_le_mul_iff_right₀ ht0).mp
    simpa only [← pow_two, Real.sq_sqrt hB0.le, mul_comm] using hmain
  have hroot' : Real.sqrt B ≤ 2 * A * N ^ 2 * (D + 1) := by
    have hh : 0 ≤ A * N ^ 2 := by positivity
    nlinarith only [hroot, hh]
  have hh := pow_le_pow_left₀ ht0.le hroot' 2
  rw [Real.sq_sqrt hB0.le] at hh
  nlinarith only [hh]

/-- If the constant-coefficient prime choice fails while the coefficient
height obeys the determinant bound, the box is polynomially bounded in d. -/
theorem affine_coefficient_height_cutoff (n d : ℕ) {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hheight : B / A ≤ ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
      ((n + d).choose d : ℝ) * d * Real.log B) :
    B ≤ 4 * A ^ 2 * ((d : ℝ) + 1) ^ (4 * n + 2) := by
  have hN : (1 : ℝ) ≤ (n + d).choose d := by
    exact_mod_cast Nat.choose_pos (show d ≤ n + d by omega)
  have hbound := box_le_of_logarithmic_height_bound hA hB hN (Nat.cast_nonneg d) hheight
  have hcount : ((n + d).choose d : ℝ) ≤ ((d : ℝ) + 1) ^ n := by
    rw [← Nat.choose_symm_add, Nat.add_comm n d]
    exact_mod_cast Nat.choose_add_le_add_one_pow d n
  calc
    B ≤ 4 * A ^ 2 * ((n + d).choose d : ℝ) ^ 4 * ((d : ℝ) + 1) ^ 2 := hbound
    _ ≤ 4 * A ^ 2 * (((d : ℝ) + 1) ^ n) ^ 4 * ((d : ℝ) + 1) ^ 2 := by
      gcongr
    _ = _ := by rw [pow_add, Nat.mul_comm 4 n, pow_mul]; ring

/-- The extra projective box exponent is uniformly bounded on every
polynomial range in the degree. -/
private theorem polynomial_box_root_power_bound {r d k : ℕ} (hr : 0 < r) (hd : 0 < d)
    {S B : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((d : ℝ) + 1) ^ k) :
    B ^ (1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.exp (Real.log S + (k : ℝ) * ((r : ℝ) + 1)) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hS0 : 0 < S := by linarith
  have hB0 : 0 < B := by linarith
  have hroot : (1 : ℝ) ≤ (d : ℝ) ^ (1 / (r : ℝ)) :=
    Real.one_le_rpow hd1 (by positivity)
  have hden : (1 : ℝ) ≤ r * (d : ℝ) ^ (1 / (r : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hr1 hroot
  have hlogS := Real.log_nonneg hS
  have hlogd := log_nat_add_one_le_root hr hd
  have hlog := Real.log_le_log hB0 hbound
  rw [Real.log_mul hS0.ne' (by positivity), Real.log_pow] at hlog
  have hstep : Real.log B ≤
      (Real.log S + (k : ℝ) * ((r : ℝ) + 1)) *
        ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) := by
    have hfirst := mul_le_mul_of_nonneg_left hden hlogS
    have hsecond := mul_le_mul_of_nonneg_left hlogd (Nat.cast_nonneg (α := ℝ) k)
    have hthird := mul_le_mul_of_nonneg_left hr1
      (show 0 ≤ (k : ℝ) * ((r : ℝ) + 1) * (d : ℝ) ^ (1 / (r : ℝ)) by positivity)
    nlinarith only [hlog, hfirst, hsecond, hthird]
  rw [Real.rpow_def_of_pos hB0, Real.exp_le_exp, ← div_eq_mul_one_div]
  exact (div_le_iff₀ (by linarith)).mpr hstep

/-- On a polynomial box range, the projective main term has the affine
box exponent up to a constant independent of the degree and the box. -/
theorem polynomial_box_projective_power_bound {r d k : ℕ}
    (hr : 0 < r) (hd : 0 < d) {S B : ℝ}
    (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((d : ℝ) + 1) ^ k) :
    B ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.exp (Real.log S + (k : ℝ) * ((r : ℝ) + 1)) *
        B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  have he : ((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) =
      1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) +
        1 / (d : ℝ) ^ (1 / (r : ℝ)) := by field_simp; ring
  rw [he, Real.rpow_add (by linarith)]
  exact mul_le_mul_of_nonneg_right
    (polynomial_box_root_power_bound hr hd hS hB hbound) (by positivity)

end CCDN

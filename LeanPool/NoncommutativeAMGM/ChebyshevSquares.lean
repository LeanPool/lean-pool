/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic

/-! # Chebyshev polynomial identities for the Boolean matrix sums of squares -/

@[expose] public section
open Polynomial Polynomial.Chebyshev
namespace NoncommutativeAMGM
theorem chebyshev_pell (r : ℕ) :
    (T ℝ (r : ℤ)) ^ 2 + (1 - X ^ 2) * (U ℝ ((r : ℤ) - 1)) ^ 2 = 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have ht := T_eq_X_mul_T_sub_pol_U ℝ ((r : ℤ) - 1)
    have hu := U_eq_X_mul_U_add_T ℝ ((r : ℤ) - 1)
    have h1 : ((r : ℤ) - 1 + 2) = (r : ℤ) + 1 := by omega
    have h2 : ((r : ℤ) - 1 + 1) = (r : ℤ) := by omega
    rw [h1, h2] at ht
    rw [h2] at hu
    push_cast
    rw [show (r : ℤ) + 1 - 1 = (r : ℤ) by omega]
    rw [ht, hu]
    linear_combination ih
/-- The even plus square identity. -/
theorem chebyshev_even_plus (r : ℕ) :
    1 + T ℝ (2 * (r : ℤ)) = 2 * T ℝ (r : ℤ) ^ 2 := by
  have h := T_mul_T ℝ (r : ℤ) (r : ℤ)
  simp only [sub_self, T_zero] at h
  rw [← two_mul] at h
  linear_combination -h

/-- The even minus square identity, including the factor `1-X²`. -/
theorem chebyshev_even_minus (r : ℕ) :
    1 - T ℝ (2 * (r : ℤ)) = 2 * (1 - X ^ 2) * U ℝ ((r : ℤ) - 1) ^ 2 := by
  linear_combination -2 * chebyshev_pell r - chebyshev_even_plus r

/-- The third-kind factor, with the sign matching `1+T₂ᵣ₊₁`. -/
noncomputable def chebyshevPlusFactor (r : ℕ) : Polynomial ℝ :=
  U ℝ (r : ℤ) - U ℝ ((r : ℤ) - 1)

/-- The fourth-kind factor, with the sign matching `1-T₂ᵣ₊₁`. -/
noncomputable def chebyshevMinusFactor (r : ℕ) : Polynomial ℝ :=
  U ℝ (r : ℤ) + U ℝ ((r : ℤ) - 1)

theorem chebyshev_odd_minus (r : ℕ) :
    1 - T ℝ (2 * (r : ℤ) + 1) = (1 - X) * chebyshevMinusFactor r ^ 2 := by
  have hmul := T_mul_T ℝ (r : ℤ) ((r : ℤ) + 1)
  have hpell := chebyshev_pell r
  have ht := T_eq_X_mul_U_sub_U ℝ ((r : ℤ) - 1)
  have he : (r : ℤ) - 1 + 2 = (r : ℤ) + 1 := by omega
  have he' : (r : ℤ) - 1 + 1 = (r : ℤ) := by omega
  rw [he, he'] at ht
  have ht0 := T_eq_U_sub_X_mul_U ℝ (r : ℤ)
  rw [ht0] at hpell hmul
  rw [ht] at hmul
  have hsum : (r : ℤ) + ((r : ℤ) + 1) = 2 * (r : ℤ) + 1 := by omega
  have hsub : (r : ℤ) - ((r : ℤ) + 1) = -1 := by omega
  rw [hsum, hsub] at hmul
  simp only [T_neg_one] at hmul
  unfold chebyshevMinusFactor
  linear_combination hmul - (1 + X) * hpell

theorem chebyshev_odd_plus (r : ℕ) :
    1 + T ℝ (2 * (r : ℤ) + 1) = (1 + X) * chebyshevPlusFactor r ^ 2 := by
  have hmul := T_mul_T ℝ (r : ℤ) ((r : ℤ) + 1)
  have hpell := chebyshev_pell r
  have ht := T_eq_X_mul_U_sub_U ℝ ((r : ℤ) - 1)
  have he : (r : ℤ) - 1 + 2 = (r : ℤ) + 1 := by omega
  have he' : (r : ℤ) - 1 + 1 = (r : ℤ) := by omega
  rw [he, he'] at ht
  have ht0 := T_eq_U_sub_X_mul_U ℝ (r : ℤ)
  rw [ht0] at hpell hmul
  rw [ht] at hmul
  have hsum : (r : ℤ) + ((r : ℤ) + 1) = 2 * (r : ℤ) + 1 := by omega
  have hsub : (r : ℤ) - ((r : ℤ) + 1) = -1 := by omega
  rw [hsum, hsub] at hmul
  simp only [T_neg_one] at hmul
  unfold chebyshevPlusFactor
  linear_combination -hmul - (1 - X) * hpell

theorem chebyshevPlusFactor_natDegree (r : ℕ) : (chebyshevPlusFactor r).natDegree ≤ r := by
  unfold chebyshevPlusFactor
  apply (natDegree_sub_le _ _).trans
  simp only [natDegree_U, sub_add_cancel, Int.natAbs_natCast]
  omega

theorem chebyshevMinusFactor_natDegree (r : ℕ) : (chebyshevMinusFactor r).natDegree ≤ r := by
  unfold chebyshevMinusFactor
  apply (natDegree_add_le _ _).trans
  simp only [natDegree_U, sub_add_cancel, Int.natAbs_natCast]
  omega

end NoncommutativeAMGM

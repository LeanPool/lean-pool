/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


-- [TABLET NODE: P4903T1ScalarTangencies]

/-!
# P4903T1ScalarTangencies

Adapted from Wesley Pegden’s Apache - 2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4903T1ScalarTangencies (a b r D x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hD : 0 < D)
    (hra : r < a) (hrb : r < b)
    (hDsq : D ^ 2 = 4 * a * b) (hxsq : x ^ 2 = 4 * r * a)
    (hysq : (D - x) ^ 2 = 4 * r * b) :
    0 < x ∧ 0 < D - x ∧ r * (a + b + D) = a * b ∧
      2 * x * D = D ^ 2 + 4 * r * (a - b) := by
-- BODY
  have hxD : 2 * x * D = D ^ 2 + 4 * r * (a - b) := by nlinarith [hxsq, hysq]
  have hDy : 2 * (D - x) * D = D ^ 2 + 4 * r * (b - a) := by nlinarith [hxsq, hysq]
  have hxab : 0 < a * b + r * (a - b) := by
    by_cases hab : a ≤ b
    · have hba : 0 ≤ b - a := sub_nonneg.mpr hab
      have hmul : r * (b - a) ≤ a * (b - a) := mul_le_mul_of_nonneg_right hra.le hba
      nlinarith [hmul, sq_pos_of_pos ha]
    · have hab' : 0 < a - b := by linarith
      have hm : 0 < r * (a - b) := mul_pos hr hab'
      nlinarith [hm]
  have hyab : 0 < a * b + r * (b - a) := by
    by_cases hba : b ≤ a
    · have hab : 0 ≤ a - b := sub_nonneg.mpr hba
      have hmul : r * (a - b) ≤ b * (a - b) := mul_le_mul_of_nonneg_right hrb.le hab
      nlinarith [hmul, sq_pos_of_pos hb]
    · have hba' : 0 < b - a := by linarith
      have hm : 0 < r * (b - a) := mul_pos hr hba'
      nlinarith [hm]
  have hxpos : 0 < x := by nlinarith [hxD, hD, hxab]
  have hypos : 0 < D - x := by nlinarith [hDy, hD, hyab]
  have hprod : x * (D - x) = 2 * (a * b - r * (a + b)) := by nlinarith [hDsq, hxsq, hysq]
  have hprodpos : 0 < a * b - r * (a + b) := by
    have htwice : 0 < 2 * (a * b - r * (a + b)) := by
      rw [← hprod]
      exact mul_pos hxpos hypos
    nlinarith only [htwice]
  have htwo : (2 * (a * b - r * (a + b))) ^ 2=(2 * (r * D)) ^ 2 := by
    have htemp := congrArg (fun z : ℝ => z ^ 2) hprod
    have hprodSq : (x * (D - x)) ^ 2 = (2 * (r * D)) ^ 2 := by
      calc
        (x * (D - x)) ^ 2 = x ^ 2 * (D - x) ^ 2 := by ring
        _ = (4 * r * a) * (4 * r * b) := by rw [hxsq, hysq]
        _ = 4 * r ^ 2 * (4 * a * b) := by ring
        _ = 4 * r ^ 2 * D ^ 2 := by rw [hDsq]
        _ = (2 * (r * D)) ^ 2 := by ring
    exact htemp.symm.trans hprodSq
  have hleftpos : 0 < 2 * (a * b - r * (a + b)) :=
    mul_pos zero_lt_two hprodpos
  have hrightpos : 0 < 2 * (r * D) :=
    mul_pos zero_lt_two (mul_pos hr hD)
  have heq2 : 2 * (a * b - r * (a + b))=2 * (r * D) :=
    (sq_eq_sq₀ hleftpos.le hrightpos.le).mp htwo
  have heq : a * b - r * (a + b) = r * D :=
    mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) heq2
  have hrel : r * (a + b + D)=a * b := by
    calc
      r * (a + b + D)=r * (a + b) + r * D := by ring
      _=r * (a + b) + (a * b - r * (a + b)) := by rw [← heq]
      _=r * (a + b) + a * b - r * (a + b) := (add_sub_assoc _ _ _).symm
      _=a * b + r * (a + b) - r * (a + b) := by rw [add_comm (r * (a + b)) (a * b)]
      _=a * b := add_sub_cancel_right _ _
  exact ⟨hxpos, hypos, hrel, hxD⟩

end ApollonianSuperharmonic

end

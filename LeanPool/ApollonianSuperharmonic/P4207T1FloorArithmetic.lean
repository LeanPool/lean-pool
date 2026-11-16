/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4207T1DiamondFormula

-- [TABLET NODE: P4207T1FloorArithmetic]

/-!
# P4207T1FloorArithmetic

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4207T1FloorArithmetic :
    (∀ n m : Int, (n + 2 * m) ^ 2 / 4 = n ^ 2 / 4 + m * n + m ^ 2) ∧
    (∀ n : Int, (n + 1) ^ 2 / 4 - n ^ 2 / 4 = (n + 1) / 2) ∧
    (∀ x : GaussianInt,
      P4207T1DiamondFormula (x + ⟨0, 2⟩) - P4207T1DiamondFormula x =
        x.re - x.im - 1) ∧
    (∀ a b : Int,
      P4207T1DiamondFormula ⟨a, b + 1⟩ - P4207T1DiamondFormula ⟨a, b⟩ =
        (a - b) / 2) ∧
    (∀ a b : Int,
      P4207T1DiamondFormula ⟨-a, b⟩ =
        P4207T1DiamondFormula ⟨a, b⟩ - a * b) := by
-- BODY
  have shift (n m : Int) : (n + 2 * m) ^ 2 / 4 = n ^ 2 / 4 + m * n + m ^ 2 := by
    have e : (n + 2 * m) ^ 2 = n ^ 2 + (m * n + m ^ 2) * 4 := by ring
    rw [e, Int.add_mul_ediv_right]
    · ring
    · norm_num
  have successive (n : Int) : (n + 1) ^ 2 / 4 - n ^ 2 / 4 = (n + 1) / 2 := by
    have hr0 : 0 ≤ n % 2 := Int.emod_nonneg n (by norm_num)
    have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
    generalize hq : n / 2 = q at *
    rcases hr with hr | hr
    · have he : n = 0 + 2 * q := by omega
      have he' : n + 1 = 1 + 2 * q := by omega
      rw [he', shift, he, shift]
      norm_num
      omega
    · have he : n = 1 + 2 * q := by omega
      have he' : n + 1 = 0 + 2 * (q + 1) := by omega
      rw [he', shift, he, shift]
      norm_num
      ring
  refine ⟨shift, successive, ?_, ?_, ?_⟩
  · intro x
    change _ - (_ - (x.re - x.im) ^ 2 / 4) = _
    simp only [P4207T1DiamondFormula, Zsqrtd.re_add, Zsqrtd.im_add, add_zero]
    have h := shift (x.re - x.im) (-1)
    have he : (x.re - (x.im + 2)) = (x.re - x.im) + 2 * (-1) := by ring
    rw [he, h]
    ring
  · intro a b
    have h := successive (a - b - 1)
    have he : a - b - 1 + 1 = a - b := by ring
    rw [he] at h
    simp only [P4207T1DiamondFormula]
    have he' : a - (b + 1) = a - b - 1 := by ring
    rw [he']
    omega
  · intro a b
    have h := shift (a - b) b
    have he : a - b + 2 * b = a + b := by ring
    rw [he] at h
    have he' : (-a - b) ^ 2 = (a + b) ^ 2 := by ring
    simp only [P4207T1DiamondFormula, Int.natAbs_neg]
    rw [he']
    nlinarith

end ApollonianSuperharmonic

end

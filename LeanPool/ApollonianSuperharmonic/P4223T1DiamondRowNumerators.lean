/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic
public import Mathlib.Algebra.BigOperators.Intervals

-- [TABLET NODE: P4223T1DiamondRowNumerators]

/-!
# P4223T1DiamondRowNumerators

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4223T1DiamondRowNumerators (r : Nat) (y : Int) :
    (∑ j ∈ Finset.range (2 * r),
      let x : GaussianInt := ⟨(j : Int) - (r : Int), y⟩
      P4207T1DiamondFormula (x + 1) - P4207T1DiamondFormula x +
        P4207T1DiamondFormula (x + 1 + ⟨0, 1⟩) -
          P4207T1DiamondFormula (x + ⟨0, 1⟩)) = (r : Int) * (2 * y + 1) ∧
    (∑ j ∈ Finset.range (2 * r),
      let x : GaussianInt := ⟨(j : Int) - (r : Int), y⟩
      P4207T1DiamondFormula (x + ⟨0, 1⟩) - P4207T1DiamondFormula x +
        P4207T1DiamondFormula (x + 1 + ⟨0, 1⟩) -
          P4207T1DiamondFormula (x + 1)) = -(r : Int) * (2 * y + 1) := by
-- BODY
  have add_one (a b : Int) : (⟨a, b⟩ : GaussianInt) + 1 = ⟨a + 1, b⟩ := by
    ext <;> simp
  have add_i (a b : Int) : (⟨a, b⟩ : GaussianInt) + ⟨0, 1⟩ = ⟨a, b + 1⟩ := by
    ext <;> simp
  have telescope (t : Int) :
      (∑ j ∈ Finset.range (2 * r),
        (P4207T1DiamondFormula ⟨(j : Int) - r + 1, t⟩ -
          P4207T1DiamondFormula ⟨(j : Int) - r, t⟩)) = (r : Int) * t := by
    have h := Finset.sum_range_sub
      (fun j : Nat => P4207T1DiamondFormula ⟨(j : Int) - r, t⟩) (2 * r)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_zero, zero_sub] at h
    have he : 2 * (r : Int) - r = r := by ring
    rw [he, P4207T1FloorArithmetic.2.2.2.2] at h
    simp only [show ∀ a : Int, a + 1 - r = a - r + 1 by intro a; ring] at h
    linarith
  constructor
  · calc
      _ = (∑ j ∈ Finset.range (2 * r),
          (P4207T1DiamondFormula ⟨(j : Int) - r + 1, y⟩ -
            P4207T1DiamondFormula ⟨(j : Int) - r, y⟩)) +
          ∑ j ∈ Finset.range (2 * r),
          (P4207T1DiamondFormula ⟨(j : Int) - r + 1, y + 1⟩ -
            P4207T1DiamondFormula ⟨(j : Int) - r, y + 1⟩) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        change _ - _ + _ - _ = _
        rw [add_one, add_i, add_i]
        ring
      _ = _ := by rw [telescope, telescope]; ring
  · have point (a : Int) :
        P4207T1DiamondFormula (⟨a, y⟩ + ⟨0, 1⟩) -
          P4207T1DiamondFormula ⟨a, y⟩ +
          P4207T1DiamondFormula (⟨a, y⟩ + 1 + ⟨0, 1⟩) -
          P4207T1DiamondFormula (⟨a, y⟩ + 1) = a - y := by
      have h0 := P4207T1FloorArithmetic.2.2.2.1 a y
      have h1 := P4207T1FloorArithmetic.2.2.2.1 (a + 1) y
      change _ - _ + _ - _ = _
      rw [add_one, add_i, add_i]
      omega
    simp only [point]
    have total : ∀ n : Nat,
        2 * (∑ j ∈ Finset.range n, ((j : Int) - r - y)) =
          (n : Int) * (n - 1) - 2 * n * ((r : Int) + y) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith only [ih]
    have ht := total (2 * r)
    push_cast at ht
    nlinarith only [ht]

end ApollonianSuperharmonic

end

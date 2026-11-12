/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic

-- [TABLET NODE: P5537T1ScaledDiamondFormula]

/-!
# P5537T1ScaledDiamondFormula

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5537T1ScaledDiamondFormula :
    (∀ a b : Int, 4 * P4207T1DiamondFormula ⟨a,b⟩ =
      2*a^2 - 2*|a| - (a-b)^2 + (a-b)%2) ∧
    (∀ n : Int, 2*(n*(n-1)/2) = n*(n-1)) := by
-- BODY
  have tri (n : Int) : 2*(n*(n-1)/2) = n*(n-1) := by
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · have hn : n = 2*(n/2) := by omega
      rw [hn, show 2*(n/2)*(2*(n/2)-1) =
        2*((n/2)*(2*(n/2)-1)) by ring,
        Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]
    · have hn : n = 2*(n/2)+1 := by omega
      rw [hn, show (2*(n/2)+1)*(2*(n/2)+1-1) =
        2*((2*(n/2)+1)*(n/2)) by ring,
        Int.mul_ediv_cancel_left _ (by norm_num : (2:Int) ≠ 0)]
  have square (n : Int) : 4*(n^2/4) = n^2-n%2 := by
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · have hn : n = 2*(n/2) := by omega
      have hs := P4207T1FloorArithmetic.1 0 (n/2)
      norm_num at hs
      have hf : n^2/4 = (n/2)^2 := by
        conv_lhs => rw [hn]
        exact hs
      rw [hf, h]
      nlinarith only [congrArg (fun t : Int => t^2) hn]
    · have hn : n = 2*(n/2)+1 := by omega
      have hs := P4207T1FloorArithmetic.1 1 (n/2)
      norm_num at hs
      have he : 1+2*(n/2) = 2*(n/2)+1 := by ring
      rw [he] at hs
      have hf : n^2/4 = n/2+(n/2)^2 := by
        conv_lhs => rw [hn]
        exact hs
      rw [hf, h]
      nlinarith only [congrArg (fun t : Int => t^2) hn]
  refine ⟨?_, tri⟩
  intro a b
  have ht := tri (|a|)
  have hs := square (a-b)
  simp only [P4207T1DiamondFormula, Int.natCast_natAbs]
  nlinarith only [ht, hs, sq_abs a]

end ApollonianSuperharmonic

end

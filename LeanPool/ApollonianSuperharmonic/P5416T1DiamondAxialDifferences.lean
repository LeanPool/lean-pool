/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic

-- [TABLET NODE: P5416T1DiamondAxialDifferences]

/-!
# P5416T1DiamondAxialDifferences

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5416T1DiamondAxialDifferences (k : Int) (hk : 2 ≤ k) :
    let Q := P4207T1DiamondFormula
    (Q ⟨1-k,k⟩ - Q ⟨-k,k⟩ = 1 ∧
      Q ⟨-k,k+1⟩ - Q ⟨-k,k⟩ = -k ∧
      Q ⟨-k,k-1⟩ - Q ⟨-k,k⟩ = k) ∧
    (Q ⟨1,0⟩ - Q ⟨0,0⟩ = 0 ∧
      Q ⟨-1,0⟩ - Q ⟨0,0⟩ = 0 ∧
      Q ⟨0,1⟩ - Q ⟨0,0⟩ = 0) ∧
    (Q ⟨k-1,k⟩ - Q ⟨k,k⟩ = 1-k ∧
      Q ⟨k,k+1⟩ - Q ⟨k,k⟩ = 0 ∧
      Q ⟨k,k-1⟩ - Q ⟨k,k⟩ = 0) ∧
    (Q ⟨1,2*k⟩ - Q ⟨0,2*k⟩ = k ∧
      Q ⟨-1,2*k⟩ - Q ⟨0,2*k⟩ = -k ∧
      Q ⟨0,2*k-1⟩ - Q ⟨0,2*k⟩ = k) := by
-- BODY
  have sq0 (t : Int) : (2*t)^2/4 = t^2 := by
    simpa using (P4207T1FloorArithmetic.1 0 t)
  have sqm (t : Int) : (-1-2*t)^2/4 = t^2+t := by
    have h := P4207T1FloorArithmetic.1 (-1) (-t)
    rw [show -1+2*(-t) = -1-2*t by ring] at h
    norm_num at h
    nlinarith only [h]
  have sqp (t : Int) : (1-2*t)^2/4 = t^2-t := by
    have h := P4207T1FloorArithmetic.1 1 (-t)
    rw [show 1+2*(-t) = 1-2*t by ring] at h
    norm_num at h
    nlinarith only [h]
  have ht : k*(k-1)/2 - (k-1)*(k-2)/2 = k-1 := by
    have he : k*(k-1) = (k-1)*(k-2)+(k-1)*2 := by ring
    omega
  have ha : (Int.natAbs (1-k) : Int) = k-1 := by
    rw [Int.natCast_natAbs, abs_of_nonpos (by omega : 1-k ≤ 0)]
    omega
  have hb : (Int.natAbs (-k) : Int) = k := by
    rw [Int.natCast_natAbs, abs_of_nonpos (by omega : -k ≤ 0)]
    omega
  have hc : (Int.natAbs (k-1) : Int) = k-1 := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ k-1)]
  have hd : (Int.natAbs k : Int) = k := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ k)]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [P4207T1DiamondFormula, ha, hb]
    rw [show 1-k-k = 1-2*k by ring, show k-1-1 = k-2 by ring,
      show -k-k = -(2*k) by ring, show -k-(k+1) = -1-2*k by ring,
      show -k-(k-1) = 1-2*k by ring, neg_sq, sq0, sqp, sqm]
    omega
  · norm_num [P4207T1DiamondFormula]
  · norm_num [P4207T1DiamondFormula, hc, hd]
    rw [show k-1-1 = k-2 by ring]
    omega
  · norm_num [P4207T1DiamondFormula]
    rw [sqp, sqm, sq0]
    omega

end ApollonianSuperharmonic

end

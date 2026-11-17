/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5537T1ScaledDiamondFormula

-- [TABLET NODE: P5537T1PredecessorValues]

/-!
# P5537T1PredecessorValues

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5537T1PredecessorValues (k X Y : Int) (_hk : 2 ≤ k) :
    ((1 ≤ X ∧ X ≤ k ∧ 0 ≤ Y ∧ Y ≤ k-1 ∧ X-1 ≤ Y ∧ Y ≤ X) →
      P4207T1DiamondFormula ⟨X-k,Y-(1-k)⟩ + (k-1)*Y -
        P4207T1DiamondFormula ⟨X,Y⟩ = -(k*(k-1)/2)) ∧
    ((1 ≤ X ∧ X ≤ k ∧ k+1 ≤ Y ∧ Y ≤ 2*k ∧ 2*k ≤ X+Y ∧ X+Y ≤ 2*k+1) →
      P4207T1DiamondFormula ⟨X-k,Y-(k+1)⟩ + k*X -
        P4207T1DiamondFormula ⟨X,Y⟩ = k*(k+1)/2) ∧
    ((-k ≤ X ∧ X ≤ -1 ∧ k+1 ≤ Y ∧ Y ≤ 2*k ∧ 2*k ≤ Y-X ∧ Y-X ≤ 2*k+1) →
      P4207T1DiamondFormula ⟨X+k,Y-(k+1)⟩ + X-k*Y -
        P4207T1DiamondFormula ⟨X,Y⟩ = -(k*(k+1)/2)) ∧
    ((-k ≤ X ∧ X ≤ -1 ∧ 0 ≤ Y ∧ Y ≤ k-1 ∧ -1 ≤ X+Y ∧ X+Y ≤ 0) →
      P4207T1DiamondFormula ⟨X+k,Y-(1-k)⟩ + (1-k)*X-Y -
        P4207T1DiamondFormula ⟨X,Y⟩ = k*(k-1)/2) := by
-- BODY
  have hs := P5537T1ScaledDiamondFormula.1 X Y
  have ht := P5537T1ScaledDiamondFormula.2 k
  have htp := P5537T1ScaledDiamondFormula.2 (k+1)
  rw [show k+1-1 = k by ring] at htp
  have htp' : 2*(k*(k+1)/2) = k*(k+1) := by
    simpa only [mul_comm] using htp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hp := P5537T1ScaledDiamondFormula.1 (X-k) (Y-(1-k))
    rw [abs_of_nonneg (by omega : 0 ≤ X)] at hs
    rw [abs_of_nonpos (by omega : X-k ≤ 0)] at hp
    have hd : Y = X-1 ∨ Y = X := by omega
    rcases hd with hd | hd
    · have hm : (X-Y)%2 = 1 ∧ (X-k-(Y-(1-k)))%2 = 0 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, ht]
    · have hm : (X-Y)%2 = 0 ∧ (X-k-(Y-(1-k)))%2 = 1 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, ht]
  · intro h
    have hp := P5537T1ScaledDiamondFormula.1 (X-k) (Y-(k+1))
    rw [abs_of_nonneg (by omega : 0 ≤ X)] at hs
    rw [abs_of_nonpos (by omega : X-k ≤ 0)] at hp
    have hd : Y = 2*k-X ∨ Y = 2*k+1-X := by omega
    rcases hd with hd | hd
    · have hm : (X-Y)%2 = 0 ∧ (X-k-(Y-(k+1)))%2 = 1 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, htp']
    · have hm : (X-Y)%2 = 1 ∧ (X-k-(Y-(k+1)))%2 = 0 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, htp']
  · intro h
    have hp := P5537T1ScaledDiamondFormula.1 (X+k) (Y-(k+1))
    rw [abs_of_nonpos (by omega : X ≤ 0)] at hs
    rw [abs_of_nonneg (by omega : 0 ≤ X+k)] at hp
    have hd : Y = 2*k+X ∨ Y = 2*k+1+X := by omega
    rcases hd with hd | hd
    · have hm : (X-Y)%2 = 0 ∧ (X+k-(Y-(k+1)))%2 = 1 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, htp']
    · have hm : (X-Y)%2 = 1 ∧ (X+k-(Y-(k+1)))%2 = 0 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, htp']
  · intro h
    have hp := P5537T1ScaledDiamondFormula.1 (X+k) (Y-(1-k))
    rw [abs_of_nonpos (by omega : X ≤ 0)] at hs
    rw [abs_of_nonneg (by omega : 0 ≤ X+k)] at hp
    have hd : Y = -X-1 ∨ Y = -X := by omega
    rcases hd with hd | hd
    · have hm : (X-Y)%2 = 1 ∧ (X+k-(Y-(1-k)))%2 = 0 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, ht]
    · have hm : (X-Y)%2 = 0 ∧ (X+k-(Y-(1-k)))%2 = 1 := by omega
      rw [hm.1] at hs
      rw [hm.2] at hp
      rw [hd] at hs hp ⊢
      nlinarith only [hs, hp, ht]

end ApollonianSuperharmonic

end

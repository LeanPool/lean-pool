/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

public import LeanPool.ApollonianSuperharmonic.VectorSquareProduct

-- [TABLET NODE: VectorNonvanishing]

/-!
# VectorNonvanishing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem VectorNonvanishing (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) (i j : Fin 4) (hij : i ≠ j)
    (hpositive : 0 < (q i).1 ∨ 0 < (q j).1) :
    BandVectors.1 (q i) (q j) ≠ 0 := by
-- BODY
  have nonnegative : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 :=
    fun r hr => (SemiProperForestClassification r hr).1
  have hnonneg := nonnegative q hq
  have hsum : 0 < (q i).1 + (q j).1 := by
    rcases hpositive with hi | hj
    · exact add_pos_of_pos_of_nonneg hi (hnonneg j)
    · exact add_pos_of_nonneg_of_pos (hnonneg i) hj
  intro hv
  have hproduct := (VectorSquareProduct q hq i j hij).1
  have hzero : (q j).1 • (q i).2 - (q i).1 • (q j).2 = 0 := by
    rw [← hproduct, hv]
    simp
  have hnorm : Zsqrtd.norm ((q j).1 • (q i).2 - (q i).1 • (q j).2) = 0 := by
    rw [hzero]
    simp
  have hsquare : ((q i).1 + (q j).1) ^ 2 = 0 := by
    rw [← TangencyCoordinateIdentity q hq i j hij]
    exact hnorm
  nlinarith

end ApollonianSuperharmonic

end

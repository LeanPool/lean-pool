/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4780T1HullHalfspaces

-- [TABLET NODE: P4780T1OverlapBound]

/-!
# P4780T1OverlapBound

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1OverlapBound (d : Int × Int) (a b : Real × Real)
    (ha : a ∈ P4715T1Hexagon) (hb : b ∈ P4715T1Hexagon)
    (hab : a = b + ((d.1 : Real), (d.2 : Real))) :
    -1 ≤ d.1 ∧ d.1 ≤ 1 ∧ -1 ≤ d.2 ∧ d.2 ≤ 1 := by
-- BODY
  rw [P4780T1HullHalfspaces] at ha hb
  rcases ha with ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
  rcases hb with ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩
  have he1 := congrArg Prod.fst hab
  have he2 := congrArg Prod.snd hab
  simp only [Prod.fst_add, Prod.snd_add] at he1 he2
  have hx0 : (-2 : Real) < (d.1 : Real) := by linarith
  have hx1 : (d.1 : Real) < 2 := by linarith
  have hy0 : (-2 : Real) < (d.2 : Real) := by linarith
  have hy1 : (d.2 : Real) < 2 := by linarith
  have hx0' : (-2 : Int) < d.1 := by exact_mod_cast hx0
  have hx1' : d.1 < 2 := by exact_mod_cast hx1
  have hy0' : (-2 : Int) < d.2 := by exact_mod_cast hy0
  have hy1' : d.2 < 2 := by exact_mod_cast hy1
  omega

end ApollonianSuperharmonic

end

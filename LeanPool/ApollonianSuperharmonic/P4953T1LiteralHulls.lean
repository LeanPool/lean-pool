/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init


public import LeanPool.ApollonianSuperharmonic.P4909T1ParentPolygon
public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate
public import LeanPool.ApollonianSuperharmonic.P4828T1Step

-- [TABLET NODE: P4953T1LiteralHulls]

/-!
# P4953T1LiteralHulls

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4953T1LiteralHulls (L : ℝ) (q : Fin 4 → CircleCoordinates)
    (l a b : Fin 3) (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hl : (q l.succ).1 = 0) (ha : 0 < (q a.succ).1)
    (hb : 0 < (q b.succ).1) (hx : 0 < (q 0).1) :
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let h := if (q l.succ).2 = -1 then L else L + 2
    let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
    let x := p 0
    let A := p a.succ
    let B := p b.succ
    let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
    P4909T1ParentPolygon L q =
      convexHull ℝ ({A, B, foot A, foot B} : Set ℂ) ∧
    P4909T1ParentPolygon L (s l) = convexHull ℝ ({x, A, B} : Set ℂ) ∧
    P4909T1ParentPolygon L (s a) =
      convexHull ℝ ({x, B, foot x, foot B} : Set ℂ) ∧
    P4909T1ParentPolygon L (s b) =
      convexHull ℝ ({A, x, foot A, foot x} : Set ℂ) ∧
    (∀ c j : Fin 3, s c j.succ =
      if j = 0 then q 0 else q ((j + c).succ)) := by
-- BODY
  classical
  dsimp only
  have hs (c j : Fin 3) : P4828T1Step (P4828T1Rotate q c) j.succ =
      if j = 0 then q 0 else q ((j + c).succ) := by
    fin_cases c <;> fin_cases j <;> rfl
  fin_cases l <;> fin_cases a <;> fin_cases b
  all_goals try (norm_num at hal)
  all_goals try (norm_num at hbl)
  all_goals try (norm_num at hab)
  all_goals dsimp at hl ha hb
  all_goals
    refine ⟨?_, ?_, ?_, ?_, hs⟩
  all_goals
    apply congrArg (convexHull ℝ)
    ext z
    simp [hs,
      Fin.exists_fin_succ, hl, ha, hb, hx, ne_of_gt ha, ne_of_gt hb, ne_of_gt hx]
  all_goals tauto

end ApollonianSuperharmonic

end

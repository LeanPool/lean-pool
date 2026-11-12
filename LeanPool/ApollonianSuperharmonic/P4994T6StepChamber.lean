/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.NormNum

public import LeanPool.ApollonianSuperharmonic.P4994T6Chamber
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent

-- [TABLET NODE: P4994T6StepChamber]

/-!
# P4994T6StepChamber

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6StepChamber (p r : Int × Int)
    (hp : TriangularLatticeAdjacent 0 p)
    (hr : TriangularLatticeAdjacent 0 r)
    (hpr : TriangularLatticeAdjacent p r)
    (hdet : p.1 * r.2 - p.2 * r.1 = -1) :
    ∃ n < 6, P4994T6Chamber n p ∧ P4994T6Chamber n r := by
-- BODY
  simp only [TriangularLatticeAdjacent, sub_zero] at hp hr
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try norm_num at hdet
  all_goals try norm_num [TriangularLatticeAdjacent, Prod.mk_sub_mk] at hpr
  all_goals first
    | (refine ⟨0, by decide, ?_⟩
       norm_num [P4994T6Chamber, P4994T6Rotation]
       done)
    | (refine ⟨1, by decide, ?_⟩
       norm_num [P4994T6Chamber, P4994T6Rotation]
       done)
    | (refine ⟨2, by decide, ?_⟩
       norm_num [P4994T6Chamber, P4994T6Rotation]
       done)
    | (refine ⟨3, by decide, ?_⟩
       norm_num [P4994T6Chamber, P4994T6Rotation]
       done)
    | (refine ⟨4, by decide, ?_⟩
       norm_num [P4994T6Chamber, P4994T6Rotation]
       done)
    | (refine ⟨5, by decide, ?_⟩
       norm_num [P4994T6Chamber, P4994T6Rotation]
       )

end ApollonianSuperharmonic

end

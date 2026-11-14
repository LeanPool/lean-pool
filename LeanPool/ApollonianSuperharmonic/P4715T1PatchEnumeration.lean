/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

public import LeanPool.ApollonianSuperharmonic.P4715T1PatchFaces
public import LeanPool.ApollonianSuperharmonic.P4715T1FaceShift

-- [TABLET NODE: P4715T1PatchEnumeration]

/-!
# P4715T1PatchEnumeration

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1PatchEnumeration (f : PeriodicSubtileFaceIndex) :
    ∃! ki : (Int × Int) × Fin 12,
      P4715T1FaceShift ki.1 (P4715T1PatchFaces ki.2) = f := by
-- BODY
  rcases f with ⟨l, m, n⟩
  cases l
  case' I1 => refine ⟨((m, n), 0), ?_, ?_⟩
  case' I2 => refine ⟨((m + 1, n), 2), ?_, ?_⟩
  case' I3 => refine ⟨((m, n), 8), ?_, ?_⟩
  case' I4 => refine ⟨((m + 1, n), 6), ?_, ?_⟩
  case' J1 => refine ⟨((m + 1, n + 1), 7), ?_, ?_⟩
  case' J2 => refine ⟨((m, n), 11), ?_, ?_⟩
  case' J3 => refine ⟨((m + 1, n + 1), 1), ?_, ?_⟩
  case' J4 => refine ⟨((m + 1, n), 3), ?_, ?_⟩
  case' J5 => refine ⟨((m + 1, n + 1), 4), ?_, ?_⟩
  case' J6 => refine ⟨((m, n - 1), 10), ?_, ?_⟩
  case' J7 => refine ⟨((m, n), 5), ?_, ?_⟩
  case' J8 => refine ⟨((m, n), 9), ?_, ?_⟩
  all_goals first
    | (solve | simp [P4715T1FaceShift, P4715T1PatchFaces])
    | (rintro ⟨⟨p, q⟩, j⟩ h
       fin_cases j <;>
         simp [P4715T1FaceShift, P4715T1PatchFaces,
           PeriodicSubtileFaceIndex.mk.injEq, Prod.ext_iff] at h ⊢; omega)

end ApollonianSuperharmonic

end

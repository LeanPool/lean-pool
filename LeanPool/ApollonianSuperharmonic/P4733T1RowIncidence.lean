/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

public import LeanPool.ApollonianSuperharmonic.P4733T1EdgeRow
public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices

-- [TABLET NODE: P4733T1RowIncidence]

/-!
# P4733T1RowIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1RowIncidence (r : Fin 18) :
    let row := P4733T1EdgeRow r
    AllowedSubtileIncidence row.1.1 row.1.2 ∧ row.2.1 ≠ row.2.2 ∧
      (∃ i, SixSubtileFaceVertices row.2.1 i = row.1.1) ∧
      (∃ i, SixSubtileFaceVertices row.2.1 i = row.1.2) ∧
      (∃ i, SixSubtileFaceVertices row.2.2 i = row.1.1) ∧
      (∃ i, SixSubtileFaceVertices row.2.2 i = row.1.2) := by
-- BODY
  fin_cases r <;> dsimp [P4733T1EdgeRow]
  all_goals refine ⟨?_, by decide, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact AllowedSubtileIncidence.AB 0 0
    | exact AllowedSubtileIncidence.AB01 0 0
    | exact AllowedSubtileIncidence.AB11 0 0
    | exact AllowedSubtileIncidence.AC 0 0
    | exact AllowedSubtileIncidence.AC11 0 0
    | exact AllowedSubtileIncidence.AD 0 0
    | exact AllowedSubtileIncidence.AE01 0 0
    | exact AllowedSubtileIncidence.AF 0 0
    | exact AllowedSubtileIncidence.BC 0 0
    | exact AllowedSubtileIncidence.BDm1m1 0 0
    | exact AllowedSubtileIncidence.BD 0 0
    | exact AllowedSubtileIncidence.BE 0 0
    | exact AllowedSubtileIncidence.BF0m1 0 0
    | exact AllowedSubtileIncidence.CDm10 0 0
    | exact AllowedSubtileIncidence.CEm10 0 0
    | exact AllowedSubtileIncidence.CF 0 0
    | exact AllowedSubtileIncidence.DE 0 0
    | exact AllowedSubtileIncidence.DF10 0 0
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩

end ApollonianSuperharmonic

end

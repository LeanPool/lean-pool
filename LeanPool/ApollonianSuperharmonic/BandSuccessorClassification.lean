/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: BandSuccessorClassification]

/-!
# BandSuccessorClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandSuccessorClassification (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) :
    let s : Fin 4 → CircleCoordinates :=
      ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
          2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
        q 0, q 2, q 3]
    (s 0).1 = 1 ∨
      (ProperBandQuadruple s ∧
        (q 0).1 < (s 0).1 ∧
        (q 2).1 < (s 0).1 ∧
        (q 3).1 < (s 0).1) := by
-- BODY
  have main := SemiProperForestClassification q hq
  dsimp
  rcases main with ⟨nonneg, cases⟩
  rcases cases with root | root | root | proper
  · rcases root with ⟨z, hz⟩
    left
    rw [hz]
    simp
  · rcases root with ⟨z, hz⟩
    right
    refine ⟨?_, ?_, ?_, ?_⟩
    · change SemiProperQuadruple _ ∧ _
      refine ⟨SemiProperQuadruple.successor hq, ?_⟩
      intro j
      fin_cases j <;> rw [hz] <;> simp
    · rw [hz]
      simp
    · rw [hz]
      simp
    · rw [hz]
      simp
  · rcases root with ⟨z, hz⟩
    right
    refine ⟨?_, ?_, ?_, ?_⟩
    · change SemiProperQuadruple _ ∧ _
      refine ⟨SemiProperQuadruple.successor hq, ?_⟩
      intro j
      fin_cases j <;> rw [hz] <;> simp
    · rw [hz]
      simp
    · rw [hz]
      simp
    · rw [hz]
      simp
  · right
    refine ⟨?_, ?_, ?_, ?_⟩
    · change SemiProperQuadruple _ ∧ _
      refine ⟨SemiProperQuadruple.successor proper.1, ?_⟩
      have h0 : (q 1).1 < (q 0).1 := by simpa using proper.2 0
      have h1 : (q 2).1 < (q 0).1 := by simpa using proper.2 1
      have h2 : (q 3).1 < (q 0).1 := by simpa using proper.2 2
      intro j
      fin_cases j
      · have a := nonneg 0
        have b := nonneg 1
        have c := nonneg 2
        have d := nonneg 3
        dsimp
        omega
      · have a := nonneg 0
        have b := nonneg 1
        have c := nonneg 2
        have d := nonneg 3
        dsimp
        omega
      · have a := nonneg 0
        have b := nonneg 1
        have c := nonneg 2
        have d := nonneg 3
        dsimp
        omega
    · have h : (q 1).1 < (q 0).1 := by simpa using proper.2 0
      have a := nonneg 0
      have b := nonneg 1
      have c := nonneg 2
      have d := nonneg 3
      omega
    · have h : (q 1).1 < (q 0).1 := by simpa using proper.2 0
      have a := nonneg 0
      have b := nonneg 1
      have c := nonneg 2
      have d := nonneg 3
      omega
    · have h : (q 1).1 < (q 0).1 := by simpa using proper.2 0
      have a := nonneg 0
      have b := nonneg 1
      have c := nonneg 2
      have d := nonneg 3
      omega

end ApollonianSuperharmonic

end

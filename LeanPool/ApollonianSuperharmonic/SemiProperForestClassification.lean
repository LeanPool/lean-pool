/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple


-- [TABLET NODE: SemiProperForestClassification]

/-!
# SemiProperForestClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SemiProperForestClassification (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) :
    (∀ k : Fin 4, 0 ≤ (q k).1) ∧
      ((∃ z : GaussianInt, q = ![(1, 1 + 2 * z),
          (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (0, 1), (0, -1)]) ∨
        (∃ z : GaussianInt, q = ![(1, 1 + 2 * z),
          (0, 1), (0, -1), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)]) ∨
        (∃ z : GaussianInt, q = ![(1, 1 + 2 * z),
          (0, -1), (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (0, 1)]) ∨
        ProperBandQuadruple q) := by
-- BODY
  induction hq with
  | base z =>
      constructor
      · intro k; fin_cases k <;> simp
      · exact Or.inl ⟨z, rfl⟩
  | rotate hq ih =>
      rcases ih with ⟨nonneg, cases⟩
      constructor
      · intro k; fin_cases k <;> simp_all
      · rcases cases with root | root | root | proper
        · rcases root with ⟨z, hz⟩
          right
          left
          refine ⟨z, ?_⟩
          rw [hz]
          funext k
          fin_cases k <;> rfl
        · rcases root with ⟨z, hz⟩
          right
          right
          left
          refine ⟨z, ?_⟩
          rw [hz]
          funext k
          fin_cases k <;> rfl
        · rcases root with ⟨z, hz⟩
          left
          refine ⟨z, ?_⟩
          rw [hz]
          funext k
          fin_cases k <;> rfl
        · right
          right
          right
          refine ⟨SemiProperQuadruple.rotate proper.1, ?_⟩
          intro j
          fin_cases j
          · simpa using proper.2 1
          · simpa using proper.2 2
          · simpa using proper.2 0
  | @successor r hr ih =>
      rcases ih with ⟨nonneg, cases⟩
      constructor
      · intro k
        rcases cases with root | root | root | proper
        · rcases root with ⟨z, hz⟩
          rw [hz]
          fin_cases k <;> simp
        · rcases root with ⟨z, hz⟩
          rw [hz]
          fin_cases k <;> simp
        · rcases root with ⟨z, hz⟩
          rw [hz]
          fin_cases k <;> simp
        · fin_cases k
          · have h0 : (r 1).1 < (r 0).1 := by simpa using proper.2 0
            have a := nonneg 0
            have b := nonneg 1
            have c := nonneg 2
            have d := nonneg 3
            dsimp
            omega
          · exact nonneg 0
          · exact nonneg 2
          · exact nonneg 3
      · rcases cases with root | root | root | proper
        · rcases root with ⟨z, hz⟩
          left
          refine ⟨z - ⟨0, 1⟩, ?_⟩
          rw [hz]
          funext k
          fin_cases k <;> simp <;> ring
        · rcases root with ⟨z, hz⟩
          right
          right
          right
          change SemiProperQuadruple _ ∧ _
          refine ⟨SemiProperQuadruple.successor hr, ?_⟩
          intro j
          fin_cases j <;> rw [hz] <;> simp
        · rcases root with ⟨z, hz⟩
          right
          right
          right
          refine ⟨SemiProperQuadruple.successor hr, ?_⟩
          intro j
          fin_cases j <;> rw [hz] <;> simp
        · right
          right
          right
          change SemiProperQuadruple _ ∧ _
          refine ⟨SemiProperQuadruple.successor proper.1, ?_⟩
          have h0 : (r 1).1 < (r 0).1 := by simpa using proper.2 0
          have h2 : (r 3).1 < (r 0).1 := by simpa using proper.2 2
          intro j
          fin_cases j
          · dsimp
            have a := nonneg 0
            have b := nonneg 1
            have c := nonneg 2
            have d := nonneg 3
            omega
          · dsimp
            have a := nonneg 0
            have b := nonneg 1
            have c := nonneg 2
            have d := nonneg 3
            omega
          · dsimp
            have a := nonneg 0
            have b := nonneg 1
            have c := nonneg 2
            have d := nonneg 3
            omega

end ApollonianSuperharmonic

end

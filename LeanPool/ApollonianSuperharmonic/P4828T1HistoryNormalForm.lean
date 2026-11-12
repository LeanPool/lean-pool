/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4828T1Evaluate
public import LeanPool.ApollonianSuperharmonic.P4828T1RotationLaws
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: P4828T1HistoryNormalForm]

/-!
# P4828T1HistoryNormalForm

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4828T1HistoryNormalForm (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    ∃ z : GaussianInt, ∃ side : Bool, ∃ word : List (Fin 3), ∃ r : Fin 3,
      q = P4828T1Rotate (P4828T1Evaluate z side word) r := by
-- BODY
  have main : ∀ q : Fin 4 → CircleCoordinates, SemiProperQuadruple q →
      ProperBandQuadruple q →
      ∃ z : GaussianInt, ∃ side : Bool, ∃ word : List (Fin 3), ∃ r : Fin 3,
        q = P4828T1Rotate (P4828T1Evaluate z side word) r := by
    intro q hs
    induction hs with
    | base z =>
        intro hp
        have bad := hp.2 (0 : Fin 3)
        norm_num at bad
    | @rotate q hs ih =>
        intro hp
        have old : ProperBandQuadruple q := by
          refine ⟨hs, ?_⟩
          intro j
          fin_cases j
          · simpa using hp.2 2
          · simpa using hp.2 0
          · simpa using hp.2 1
        obtain ⟨z, side, word, r, hr⟩ := ih old
        refine ⟨z, side, word, 1 + r, ?_⟩
        calc
          ![q 0, q 2, q 3, q 1] = P4828T1Rotate q 1 := by
            funext k; fin_cases k <;> rfl
          _ = P4828T1Rotate (P4828T1Rotate
              (P4828T1Evaluate z side word) r) 1 := by rw [hr]
          _ = _ := P4828T1RotationLaws.2.1 _ _ _
    | @successor q hs ih =>
        intro hp
        rcases (SemiProperForestClassification q hs).2 with root | root | root | proper
        · obtain ⟨z, hz⟩ := root
          have bad := hp.2 (0 : Fin 3)
          simp [hz] at bad
        · obtain ⟨z, hz⟩ := root
          refine ⟨z, false, [], 0, ?_⟩
          rw [P4828T1RotationLaws.1]
          rw [hz]
          funext k
          fin_cases k <;> simp [P4828T1Evaluate, P4828T1Root]; ring
        · obtain ⟨z, hz⟩ := root
          refine ⟨z, true, [], 0, ?_⟩
          rw [P4828T1RotationLaws.1]
          rw [hz]
          funext k
          fin_cases k <;> simp [P4828T1Evaluate, P4828T1Root]; ring
        · obtain ⟨z, side, word, r, hr⟩ := ih proper
          refine ⟨z, side, word ++ [r], 0, ?_⟩
          rw [P4828T1RotationLaws.1]
          change P4828T1Step q = _
          rw [hr]
          simp [P4828T1Evaluate, List.foldl_append]
  exact main q hq.1 hq

end ApollonianSuperharmonic

end

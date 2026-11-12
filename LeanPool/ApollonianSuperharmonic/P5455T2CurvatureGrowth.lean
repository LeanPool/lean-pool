/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification
public import LeanPool.ApollonianSuperharmonic.P4828T1Step

-- [TABLET NODE: P5455T2CurvatureGrowth]

/-!
# P5455T2CurvatureGrowth

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2CurvatureGrowth (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    4 ≤ (q 0).1 ∧ ProperBandQuadruple (P4828T1Step q) ∧
      (q 0).1 < (P4828T1Step q 0).1 := by
-- BODY
  have lower : ∀ p, SemiProperQuadruple p →
      ProperBandQuadruple p → 4 ≤ (p 0).1 := by
    intro p hs
    induction hs with
    | base z =>
        intro hp
        have bad := hp.2 0
        norm_num at bad
    | @rotate p hs ih =>
        intro hp
        apply ih
        refine ⟨hs, ?_⟩
        intro j
        fin_cases j
        · simpa using hp.2 2
        · simpa using hp.2 0
        · simpa using hp.2 1
    | @successor p hs ih =>
        intro hp
        rcases (SemiProperForestClassification p hs).2 with root | root | root | old
        · obtain ⟨z, hz⟩ := root
          have bad := hp.2 0
          simp [hz] at bad
        · obtain ⟨z, hz⟩ := root
          simp [hz]
        · obtain ⟨z, hz⟩ := root
          simp [hz]
        · have bound := ih old
          have strict := old.2 0
          change (p 1).1 < (p 0).1 at strict
          have nonneg := (SemiProperForestClassification p hs).1
          have n2 := nonneg 2
          have n3 := nonneg 3
          dsimp
          omega
  have bound := lower q hq.1 hq
  have strict := hq.2 0
  change (q 1).1 < (q 0).1 at strict
  have nonneg := (SemiProperForestClassification q hq.1).1
  have n2 := nonneg 2
  have n3 := nonneg 3
  have growth : (q 0).1 < (P4828T1Step q 0).1 := by
    dsimp [P4828T1Step]
    omega
  refine ⟨bound, ?_, growth⟩
  rcases BandSuccessorClassification q hq.1 with bad | good
  · change (P4828T1Step q 0).1 = 1 at bad
    omega
  · exact good.1

end ApollonianSuperharmonic

end

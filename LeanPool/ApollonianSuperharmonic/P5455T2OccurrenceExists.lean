/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5455T2CurvatureGrowth
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientationUnique

-- [TABLET NODE: P5455T2OccurrenceExists]

/-!
# P5455T2OccurrenceExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2OccurrenceExists (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (i : Fin 3) (hi : (q i.succ).1 = 1) :
    ∃ o : Bool, UnitOccurrenceOrientation q i o := by
-- BODY
  have main : ∀ p, SemiProperQuadruple p → ProperBandQuadruple p →
      ∀ j : Fin 3, (p j.succ).1 = 1 →
        ∃ o : Bool, UnitOccurrenceOrientation p j o := by
    intro p hs
    induction hs with
    | base z =>
        intro hp
        have bad := hp.2 0
        norm_num at bad
    | @rotate p hs ih =>
        intro hp j hj
        have old : ProperBandQuadruple p := by
          refine ⟨hs, ?_⟩
          intro k
          fin_cases k
          · simpa using hp.2 2
          · simpa using hp.2 0
          · simpa using hp.2 1
        have unit : (p (j + 1).succ).1 = 1 := by
          fin_cases j <;> simpa using hj
        obtain ⟨o, ho⟩ := ih old (j + 1) unit
        refine ⟨o, ?_⟩
        have hr := UnitOccurrenceOrientation.rotate ho
        fin_cases j <;> simpa using hr
    | @successor p hs ih =>
        intro hp j hj
        rcases (SemiProperForestClassification p hs).2 with root | root | root | old
        · obtain ⟨z, hz⟩ := root
          have bad := hp.2 0
          simp [hz] at bad
        · obtain ⟨z, hz⟩ := root
          have eq : P4828T1Step p =
              ![(4, 1 + 8 * z + 4 * ⟨0, 1⟩), (1, 1 + 2 * z),
                (0, -1), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)] := by
            rw [hz]
            funext k
            fin_cases k <;> simp [P4828T1Step]; ring
          change (P4828T1Step p j.succ).1 = 1 at hj
          change ∃ o, UnitOccurrenceOrientation (P4828T1Step p) j o
          rw [eq] at hj ⊢
          fin_cases j
          · exact ⟨true, .leftLower z⟩
          · change (0 : ℤ) = 1 at hj
            omega
          · exact ⟨false, .leftUpper z⟩
        · obtain ⟨z, hz⟩ := root
          have eq : P4828T1Step p =
              ![(4, 7 + 8 * z + 4 * ⟨0, 1⟩), (1, 1 + 2 * z),
                (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (0, 1)] := by
            rw [hz]
            funext k
            fin_cases k <;> simp [P4828T1Step]; ring
          change (P4828T1Step p j.succ).1 = 1 at hj
          change ∃ o, UnitOccurrenceOrientation (P4828T1Step p) j o
          rw [eq] at hj ⊢
          fin_cases j
          · exact ⟨true, .rightUpper z⟩
          · exact ⟨false, .rightLower z⟩
          · change (0 : ℤ) = 1 at hj
            omega
        · have large := (P5455T2CurvatureGrowth p old).1
          fin_cases j
          · simp at hj
            omega
          · have unit : (p 2).1 = 1 := by simpa using hj
            obtain ⟨o, ho⟩ := ih old 1 unit
            by_cases sibling : (p 3).1 = 1
            · have tangent : BandTangency (p 2) (p 3) :=
                ⟨p, hs, 2, 3, by decide, rfl, rfl⟩
              rcases ((PrimitiveVectorOrientationUnique (p 2) (p 3)).2 tangent).2 with
                direction | direction
              · exact ⟨false, .retainSecondToThird old sibling direction.1 ho⟩
              · exact ⟨true, .retainSecondFromThird old sibling direction.1 ho⟩
            · exact ⟨o, .retainSecondOther old sibling ho⟩
          · have unit : (p 3).1 = 1 := by simpa using hj
            obtain ⟨o, ho⟩ := ih old 2 unit
            by_cases sibling : (p 2).1 = 1
            · have tangent : BandTangency (p 2) (p 3) :=
                ⟨p, hs, 2, 3, by decide, rfl, rfl⟩
              rcases ((PrimitiveVectorOrientationUnique (p 2) (p 3)).2 tangent).2 with
                direction | direction
              · exact ⟨true, .retainThirdFromSecond old sibling direction.1 ho⟩
              · exact ⟨false, .retainThirdToSecond old sibling direction.1 ho⟩
            · exact ⟨o, .retainThirdOther old sibling ho⟩
  exact main q hq.1 hq i hi

end ApollonianSuperharmonic

end

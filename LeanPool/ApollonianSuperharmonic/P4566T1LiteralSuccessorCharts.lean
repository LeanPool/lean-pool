/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4566T1UnitPairCharts
public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientationUnique

-- [TABLET NODE: P4566T1LiteralSuccessorCharts]

/-!
# P4566T1LiteralSuccessorCharts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4566T1LiteralSuccessorCharts
    (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p) :
    let q : Fin 4 → CircleCoordinates :=
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]
    (((p 2).1 = 1) → ∀ orientation : Bool,
      UnitOccurrenceOrientation q 1 orientation ↔
        UnitOccurrenceOrientation p 1 orientation) ∧
    (((p 3).1 = 1) → ∀ orientation : Bool,
      UnitOccurrenceOrientation q 2 orientation ↔
        UnitOccurrenceOrientation p 2 orientation) := by
-- BODY
  classical
  dsimp only
  let q : Fin 4 → CircleCoordinates :=
    ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
        2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
      p 0, p 2, p 3]
  have nn := (SemiProperForestClassification p hp.1).1
  have hx : (p 1).1 < (p 0).1 := hp.2 0
  have growth : (p 0).1 < (q 0).1 := by
    have h2 := nn 2
    have h3 := nn 3
    dsimp [q]
    omega
  have hq : ProperBandQuadruple q := by
    rcases BandSuccessorClassification p hp.1 with bad | good
    · have h0 := nn 1
      change 2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1 = 1 at bad
      dsimp [q] at growth
      omega
    · exact good.1
  have direction : PrimitiveVectorOrientation (p 2) (p 3) ∨
      PrimitiveVectorOrientation (p 3) (p 2) := by
    have ht : BandTangency (p 2) (p 3) :=
      ⟨p, hp.1, 2, 3, by decide, rfl, rfl⟩
    rcases (PrimitiveVectorOrientationUnique _ _).2 ht |>.2 with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  constructor
  · intro hunit orientation
    have forward : ∀ b, UnitOccurrenceOrientation p 1 b →
        UnitOccurrenceOrientation q 1 b := by
      intro b hb
      by_cases other : (p 3).1 = 1
      · rcases direction with hd | hd
        · have pair := P4566T1UnitPairCharts p hp 1 2 (by decide) hunit other hd
          have eq := (UnitOccurrenceOrientationUnique.1 p hp 1 hunit).unique hb pair.1
          subst b
          exact UnitOccurrenceOrientation.retainSecondToThird hp other hd pair.1
        · have pair := P4566T1UnitPairCharts p hp 2 1 (by decide) other hunit hd
          have eq := (UnitOccurrenceOrientationUnique.1 p hp 1 hunit).unique hb pair.2
          subst b
          exact UnitOccurrenceOrientation.retainSecondFromThird hp other hd pair.2
      · exact UnitOccurrenceOrientation.retainSecondOther hp other hb
    constructor
    · intro supplied
      obtain ⟨b, hb, _⟩ := UnitOccurrenceOrientationUnique.1 p hp 1 hunit
      have eq := (UnitOccurrenceOrientationUnique.1 q hq 1 hunit).unique
        (forward b hb) supplied
      simpa only [eq] using hb
    · exact forward orientation
  · intro hunit orientation
    have forward : ∀ b, UnitOccurrenceOrientation p 2 b →
        UnitOccurrenceOrientation q 2 b := by
      intro b hb
      by_cases other : (p 2).1 = 1
      · rcases direction with hd | hd
        · have pair := P4566T1UnitPairCharts p hp 1 2 (by decide) other hunit hd
          have eq := (UnitOccurrenceOrientationUnique.1 p hp 2 hunit).unique hb pair.2
          subst b
          exact UnitOccurrenceOrientation.retainThirdFromSecond hp other hd pair.2
        · have pair := P4566T1UnitPairCharts p hp 2 1 (by decide) hunit other hd
          have eq := (UnitOccurrenceOrientationUnique.1 p hp 2 hunit).unique hb pair.1
          subst b
          exact UnitOccurrenceOrientation.retainThirdToSecond hp other hd pair.1
      · exact UnitOccurrenceOrientation.retainThirdOther hp other hb
    constructor
    · intro supplied
      obtain ⟨b, hb, _⟩ := UnitOccurrenceOrientationUnique.1 p hp 2 hunit
      have eq := (UnitOccurrenceOrientationUnique.1 q hq 2 hunit).unique
        (forward b hb) supplied
      simpa only [eq] using hb
    · exact forward orientation

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4566T1LiteralSuccessorCharts
public import LeanPool.ApollonianSuperharmonic.BandOrientedBoundaryParentChain

-- [TABLET NODE: P4566T1StrictRetainedGenealogy]

/-!
# P4566T1StrictRetainedGenealogy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4566T1StrictRetainedGenealogy
    (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hlarge : ¬ (((p 2).1 = 0 ∨ (p 2).1 = 1) ∧
      ((p 3).1 = 0 ∨ (p 3).1 = 1))) :
    (∃ t : Fin 4 → CircleCoordinates,
      ProperBandQuadruple t ∧ t 0 = p 2 ∧ t 1 = p 3 ∧
        (p 3).1 < (p 2).1 ∧
        ∀ orientation : Bool,
          UnitOccurrenceOrientation p 2 orientation →
            (((t 2).1 ≠ 1 → UnitOccurrenceOrientation t 0 orientation) ∧
              ((t 2).1 = 1 →
                ((PrimitiveVectorOrientation (t 1) (t 2) ∧ orientation = false) ∨
                  (PrimitiveVectorOrientation (t 2) (t 1) ∧ orientation = true))))) ∨
    ∃ t : Fin 4 → CircleCoordinates,
      ProperBandQuadruple t ∧ t 0 = p 3 ∧ t 1 = p 2 ∧
        (p 2).1 < (p 3).1 ∧
        ∀ orientation : Bool,
          UnitOccurrenceOrientation p 1 orientation →
            (((t 3).1 ≠ 1 → UnitOccurrenceOrientation t 0 orientation) ∧
              ((t 3).1 = 1 →
                ((PrimitiveVectorOrientation (t 1) (t 3) ∧ orientation = false) ∨
                  (PrimitiveVectorOrientation (t 3) (t 1) ∧ orientation = true)))) := by
-- BODY
  have unit : ∀ {u : Fin 4 → CircleCoordinates} {k : Fin 3} {b : Bool},
      UnitOccurrenceOrientation u k b → (u k.succ).1 = 1 := by
    intro u k b cert
    induction cert with
    | leftLower z => rfl
    | leftUpper z => rfl
    | rightUpper z => rfl
    | rightLower z => rfl
    | @rotate u k b cert ih => fin_cases k <;> simpa using ih
    | retainSecondToThird _ _ _ _ ih => exact ih
    | retainSecondFromThird _ _ _ _ ih => exact ih
    | retainSecondOther _ _ _ ih => exact ih
    | retainThirdFromSecond _ _ _ _ ih => exact ih
    | retainThirdToSecond _ _ _ _ ih => exact ih
    | retainThirdOther _ _ _ ih => exact ih
  let rot (u : Fin 4 → CircleCoordinates) := ![u 0, u 2, u 3, u 1]
  have rot3 (u : Fin 4 → CircleCoordinates) : rot (rot (rot u)) = u := by
    funext k
    fin_cases k <;> rfl
  have rotProper (u : Fin 4 → CircleCoordinates) (hu : ProperBandQuadruple u) :
      ProperBandQuadruple (rot u) := by
    refine ⟨SemiProperQuadruple.rotate hu.1, ?_⟩
    intro k
    fin_cases k
    · exact hu.2 1
    · exact hu.2 2
    · exact hu.2 0
  have unrotate {u : Fin 4 → CircleCoordinates} {k : Fin 3} {b : Bool}
      (cert : UnitOccurrenceOrientation (rot u) (k + 2) b) :
      UnitOccurrenceOrientation u k b := by
    have h := UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rotate cert)
    change UnitOccurrenceOrientation (rot (rot (rot u))) _ b at h
    rw [rot3] at h
    fin_cases k <;> simpa using h
  have forced (u : Fin 4 → CircleCoordinates) (hu : ProperBandQuadruple u)
      (a b : Fin 3) (hab : a ≠ b) (ha : (u a.succ).1 = 1)
      (hb : (u b.succ).1 = 1) (o : Bool) (cert : UnitOccurrenceOrientation u a o) :
      (PrimitiveVectorOrientation (u a.succ) (u b.succ) ∧ o = false) ∨
        (PrimitiveVectorOrientation (u b.succ) (u a.succ) ∧ o = true) := by
    have tangent : BandTangency (u a.succ) (u b.succ) :=
      ⟨u, hu.1, a.succ, b.succ, by simpa using hab, rfl, rfl⟩
    rcases (PrimitiveVectorOrientationUnique _ _).2 tangent |>.2 with hd | hd
    · have pair := P4566T1UnitPairCharts u hu a b hab ha hb hd.1
      exact Or.inl ⟨hd.1, (UnitOccurrenceOrientationUnique.1 u hu a ha).unique cert pair.1⟩
    · have pair := P4566T1UnitPairCharts u hu b a (Ne.symm hab) hb ha hd.1
      exact Or.inr ⟨hd.1, (UnitOccurrenceOrientationUnique.1 u hu a ha).unique cert pair.2⟩
  let Rel (u : Fin 4 → CircleCoordinates) : Prop :=
    (((u 2).1 = 0 ∨ (u 2).1 = 1) ∧ ((u 3).1 = 0 ∨ (u 3).1 = 1)) ∨
    (∃ t : Fin 4 → CircleCoordinates,
      ProperBandQuadruple t ∧ t 0 = u 2 ∧ t 1 = u 3 ∧ (u 3).1 < (u 2).1 ∧
      ∀ o : Bool, UnitOccurrenceOrientation u 2 o →
        (((t 2).1 ≠ 1 → UnitOccurrenceOrientation t 0 o) ∧
          ((t 2).1 = 1 →
            ((PrimitiveVectorOrientation (t 1) (t 2) ∧ o = false) ∨
              (PrimitiveVectorOrientation (t 2) (t 1) ∧ o = true))))) ∨
    ∃ t : Fin 4 → CircleCoordinates,
      ProperBandQuadruple t ∧ t 0 = u 3 ∧ t 1 = u 2 ∧ (u 2).1 < (u 3).1 ∧
      ∀ o : Bool, UnitOccurrenceOrientation u 1 o →
        (((t 3).1 ≠ 1 → UnitOccurrenceOrientation t 0 o) ∧
          ((t 3).1 = 1 →
            ((PrimitiveVectorOrientation (t 1) (t 3) ∧ o = false) ∨
              (PrimitiveVectorOrientation (t 3) (t 1) ∧ o = true))))
  have claim : ∀ u, SemiProperQuadruple u → ProperBandQuadruple u →
      Rel u ∧ Rel (rot u) ∧ Rel (rot (rot u)) := by
    intro u hs
    induction hs with
    | base z =>
        intro hu
        have bad := hu.2 0
        simp at bad
    | @rotate u hs ih =>
        intro hu
        have old : ProperBandQuadruple u := by
          refine ⟨hs, ?_⟩
          intro k
          fin_cases k
          · exact hu.2 2
          · exact hu.2 0
          · exact hu.2 1
        change Rel (rot u) ∧ Rel (rot (rot u)) ∧ Rel (rot (rot (rot u)))
        rw [rot3]
        exact ⟨(ih old).2.1, (ih old).2.2, (ih old).1⟩
    | @successor u hs ih =>
        intro hu
        let s : Fin 4 → CircleCoordinates :=
          ![(2 * (u 0).1 + 2 * (u 2).1 + 2 * (u 3).1 - (u 1).1,
              2 * (u 0).2 + 2 * (u 2).2 + 2 * (u 3).2 - (u 1).2),
            u 0, u 2, u 3]
        change Rel s ∧ Rel (rot s) ∧ Rel (rot (rot s))
        rcases (SemiProperForestClassification u hs).2 with root | root | root | old
        · rcases root with ⟨z, hz⟩
          simp [s, rot, Rel, hz]
        · rcases root with ⟨z, hz⟩
          simp [s, rot, Rel, hz]
        · rcases root with ⟨z, hz⟩
          simp [s, rot, Rel, hz]
        · have charts := P4566T1LiteralSuccessorCharts u old
          have inherited : Rel s := by
            rcases (ih old).1 with small | ⟨t, ht, ht0, ht1, hlt, transport⟩ |
                ⟨t, ht, ht0, ht1, hlt, transport⟩
            · exact Or.inl small
            · refine Or.inr (Or.inl ⟨t, ht, ht0, ht1, hlt, ?_⟩)
              intro o cert
              exact transport o ((charts.2 (unit cert) o).mp cert)
            · refine Or.inr (Or.inr ⟨t, ht, ht0, ht1, hlt, ?_⟩)
              intro o cert
              exact transport o ((charts.1 (unit cert) o).mp cert)
          have second : Rel (rot s) := by
            refine Or.inr (Or.inr ⟨rot (rot u), rotProper _ (rotProper u old),
              rfl, rfl, old.2 2, ?_⟩)
            intro o cert
            have current : UnitOccurrenceOrientation s 2 o :=
              unrotate (k := 2) (by simpa using cert)
            have selected : (u 3).1 = 1 := unit current
            constructor
            · intro hidden
              have previous := (charts.2 selected o).mp current
              have moved := UnitOccurrenceOrientation.rotate
                (UnitOccurrenceOrientation.rotate previous)
              simpa [rot] using moved
            · intro hidden
              exact forced s hu 2 1 (by decide) selected hidden o current
          have third : Rel (rot (rot s)) := by
            refine Or.inr (Or.inl ⟨rot u, rotProper u old,
              rfl, rfl, old.2 1, ?_⟩)
            intro o cert
            have current : UnitOccurrenceOrientation s 1 o := by
              have moved := UnitOccurrenceOrientation.rotate cert
              change UnitOccurrenceOrientation (rot (rot (rot s))) _ o at moved
              rw [rot3] at moved
              simpa [rot] using moved
            have selected : (u 2).1 = 1 := unit current
            constructor
            · intro hidden
              have previous := (charts.1 selected o).mp current
              have moved := UnitOccurrenceOrientation.rotate previous
              simpa using moved
            · intro hidden
              exact forced s hu 1 2 (by decide) selected hidden o current
          exact ⟨inherited, second, third⟩
  rcases (claim p hp.1 hp).1 with small | first | second
  · exact (hlarge small).elim
  · exact Or.inl first
  · exact Or.inr second

end ApollonianSuperharmonic

end

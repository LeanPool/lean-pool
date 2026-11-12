/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrientedBoundaryParentChain
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientation
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientationUnique
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.RecursiveVectorSystem
public import LeanPool.ApollonianSuperharmonic.RecursiveVectorsExistUnique
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientationUnique
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep
public import LeanPool.ApollonianSuperharmonic.P4566T1LiteralSuccessorCharts
public import LeanPool.ApollonianSuperharmonic.P4566T1SmallRetainedSides
public import LeanPool.ApollonianSuperharmonic.P4566T1StrictRetainedGenealogy

-- [TABLET NODE: BandOrientedBoundaryOccurrenceGenealogy]

/-!
# BandOrientedBoundaryOccurrenceGenealogy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrientedBoundaryOccurrenceGenealogy
    (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p) :
    let q : Fin 4 → CircleCoordinates :=
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]
    let r : Fin 4 → CircleCoordinates :=
      ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
          2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
        q 0, q 2, q 3]
    ProperBandQuadruple q ∧
    (p 0).1 < (q 0).1 ∧ (p 2).1 < (q 0).1 ∧ (p 3).1 < (q 0).1 ∧
    ((((p 2).1 = 1) → ∀ orientation : Bool,
        UnitOccurrenceOrientation q 1 orientation →
          UnitOccurrenceOrientation p 1 orientation) ∧
      (((p 3).1 = 1) → ∀ orientation : Bool,
        UnitOccurrenceOrientation q 2 orientation →
          UnitOccurrenceOrientation p 2 orientation)) ∧
    (((((p 2).1 = 0 ∨ (p 2).1 = 1) ∧
          ((p 3).1 = 0 ∨ (p 3).1 = 1)) ∧
        ((PrimitiveVectorOrientation (p 2) (p 3) ∧
            (∀ orientation : Bool,
              UnitOccurrenceOrientation q 1 orientation →
                UnitTriangularStep orientation (BandVectors.1 (p 3) (p 2)) ∧
                ((p 3).1 = 0 ∨ orientation = false)) ∧
            (∀ orientation : Bool,
              UnitOccurrenceOrientation q 2 orientation →
                UnitTriangularStep orientation
                    ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (p 3) (p 2)) ∧
                ((p 2).1 = 0 ∨ orientation = true)) ∧
            ((p 2).1 = 1 → (p 3).1 = 1 →
              UnitOccurrenceOrientation q 1 false ∧
              UnitOccurrenceOrientation q 2 true ∧
              UnitOccurrenceOrientation r 1 false ∧
              UnitOccurrenceOrientation r 2 true)) ∨
          (PrimitiveVectorOrientation (p 3) (p 2) ∧
            (∀ orientation : Bool,
              UnitOccurrenceOrientation q 1 orientation →
                UnitTriangularStep orientation (BandVectors.1 (p 3) (p 2)) ∧
                ((p 3).1 = 0 ∨ orientation = true)) ∧
            (∀ orientation : Bool,
              UnitOccurrenceOrientation q 2 orientation →
                UnitTriangularStep orientation
                    ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (p 3) (p 2)) ∧
                ((p 2).1 = 0 ∨ orientation = false)) ∧
            ((p 2).1 = 1 → (p 3).1 = 1 →
              UnitOccurrenceOrientation q 1 true ∧
              UnitOccurrenceOrientation q 2 false ∧
              UnitOccurrenceOrientation r 1 true ∧
              UnitOccurrenceOrientation r 2 false)))) ∨
      (∃ t : Fin 4 → CircleCoordinates,
        ProperBandQuadruple t ∧ t 0 = p 2 ∧ t 1 = p 3 ∧
          (p 3).1 < (p 2).1 ∧
          ∀ orientation : Bool,
            UnitOccurrenceOrientation p 2 orientation →
              (((t 2).1 ≠ 1 →
                  UnitOccurrenceOrientation t 0 orientation) ∧
                ((t 2).1 = 1 →
                  ((PrimitiveVectorOrientation (t 1) (t 2) ∧
                      orientation = false) ∨
                    (PrimitiveVectorOrientation (t 2) (t 1) ∧
                      orientation = true))))) ∨
      ∃ t : Fin 4 → CircleCoordinates,
        ProperBandQuadruple t ∧ t 0 = p 3 ∧ t 1 = p 2 ∧
          (p 2).1 < (p 3).1 ∧
          ∀ orientation : Bool,
            UnitOccurrenceOrientation p 1 orientation →
              (((t 3).1 ≠ 1 →
                  UnitOccurrenceOrientation t 0 orientation) ∧
                ((t 3).1 = 1 →
                  ((PrimitiveVectorOrientation (t 1) (t 3) ∧
                      orientation = false) ∨
                    (PrimitiveVectorOrientation (t 3) (t 1) ∧
                      orientation = true))))) := by
-- BODY
  classical
  dsimp only
  let q : Fin 4 → CircleCoordinates :=
    ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
        2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
      p 0, p 2, p 3]
  have nn := (SemiProperForestClassification p hp.1).1
  have hx : (p 1).1 < (p 0).1 := hp.2 0
  have h0 := nn 0
  have h2 := nn 2
  have h3 := nn 3
  have growth : (p 0).1 < (q 0).1 ∧
      (p 2).1 < (q 0).1 ∧ (p 3).1 < (q 0).1 := by
    dsimp [q]
    omega
  have hq : ProperBandQuadruple q := by
    refine ⟨SemiProperQuadruple.successor hp.1, ?_⟩
    intro j
    fin_cases j
    · exact growth.1
    · exact growth.2.1
    · exact growth.2.2
  refine ⟨hq, growth.1, growth.2.1, growth.2.2, ?_, ?_⟩
  · have charts := P4566T1LiteralSuccessorCharts p hp
    exact ⟨fun h b hb => (charts.1 h b).mp hb,
      fun h b hb => (charts.2 h b).mp hb⟩
  · by_cases small : ((p 2).1 = 0 ∨ (p 2).1 = 1) ∧
        ((p 3).1 = 0 ∨ (p 3).1 = 1)
    · exact Or.inl ⟨small, P4566T1SmallRetainedSides p hp small.1 small.2⟩
    · exact Or.inr (P4566T1StrictRetainedGenealogy p hp small)

end ApollonianSuperharmonic

end

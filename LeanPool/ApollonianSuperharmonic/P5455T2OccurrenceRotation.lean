/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation
public import LeanPool.ApollonianSuperharmonic.P4828T1RotationLaws

-- [TABLET NODE: P5455T2OccurrenceRotation]

/-!
# P5455T2OccurrenceRotation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2OccurrenceRotation
    (q : Fin 4 → CircleCoordinates) (i r : Fin 3) (o : Bool) :
    UnitOccurrenceOrientation (P4828T1Rotate q r) (i - r) o ↔
      UnitOccurrenceOrientation q i o := by
-- BODY
  have forward : ∀ (p : Fin 4 → CircleCoordinates) (j s : Fin 3) (b : Bool),
      UnitOccurrenceOrientation p j b →
        UnitOccurrenceOrientation (P4828T1Rotate p s) (j - s) b := by
    intro p j s b h
    fin_cases s
    · change UnitOccurrenceOrientation (P4828T1Rotate p 0) (j - 0) b
      simpa only [P4828T1RotationLaws.1, sub_zero] using h
    · have hr := UnitOccurrenceOrientation.rotate h
      have eq : P4828T1Rotate p 1 = ![p 0, p 2, p 3, p 1] := by
        funext k
        fin_cases k <;> rfl
      change UnitOccurrenceOrientation (P4828T1Rotate p 1) (j - 1) b
      rw [eq]
      convert hr using 1; fin_cases j <;> rfl
    · have hr := UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rotate h)
      have eq : P4828T1Rotate p 2 = ![p 0, p 3, p 1, p 2] := by
        funext k
        fin_cases k <;> rfl
      change UnitOccurrenceOrientation (P4828T1Rotate p 2) (j - 2) b
      rw [eq]
      convert hr using 1 <;> fin_cases j <;> rfl
  constructor
  · intro h
    have hr := forward (P4828T1Rotate q r) (i - r) (-r) o h
    rw [P4828T1RotationLaws.2.1, neg_add_cancel,
      P4828T1RotationLaws.1] at hr
    have idx : (i - r) - (-r) = i := by
      fin_cases i <;> fin_cases r <;> rfl
    rwa [idx] at hr
  · exact forward q i r o

end ApollonianSuperharmonic

end

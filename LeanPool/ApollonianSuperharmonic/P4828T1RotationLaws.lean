/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Tactic.FinCases

public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple

-- [TABLET NODE: P4828T1RotationLaws]

/-!
# P4828T1RotationLaws

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4828T1RotationLaws :
    (∀ q : Fin 4 → CircleCoordinates, P4828T1Rotate q 0 = q) ∧
    (∀ (q : Fin 4 → CircleCoordinates) (a b : Fin 3),
      P4828T1Rotate (P4828T1Rotate q a) b = P4828T1Rotate q (b + a)) ∧
    (∀ (q : Fin 4 → CircleCoordinates) (a : Fin 3),
      ProperBandQuadruple q → ProperBandQuadruple (P4828T1Rotate q a)) := by
-- BODY
  refine ⟨?_, ?_, ?_⟩
  · intro q
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp [P4828T1Rotate]
  · intro q a b
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp [P4828T1Rotate, add_assoc]
  · intro q a hq
    have hsemi : SemiProperQuadruple (P4828T1Rotate q a) := by
      fin_cases a
      · convert hq.1 using 1
        funext k
        refine Fin.cases ?_ (fun j => ?_) k
        · rfl
        · simp [P4828T1Rotate]
      · convert SemiProperQuadruple.rotate hq.1 using 1;
          funext k; fin_cases k <;> rfl
      · convert SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1) using 1;
          funext k; fin_cases k <;> rfl
    exact ⟨hsemi, fun j => by simpa [P4828T1Rotate] using hq.2 (j + a)⟩

end ApollonianSuperharmonic

end

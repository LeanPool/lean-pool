/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple

-- [TABLET NODE: BandOrientedBoundaryParentChain]

/-!
# BandOrientedBoundaryParentChain

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrientedBoundaryParentChain
    (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p) :
    (((p 2).1 = 0 ∨ (p 2).1 = 1) ∧
      ((p 3).1 = 0 ∨ (p 3).1 = 1)) ∨
    (∃ t : Fin 4 → CircleCoordinates,
      ProperBandQuadruple t ∧ t 0 = p 2 ∧ t 1 = p 3 ∧
        (p 3).1 < (p 2).1) ∨
    ∃ t : Fin 4 → CircleCoordinates,
      ProperBandQuadruple t ∧ t 0 = p 3 ∧ t 1 = p 2 ∧
        (p 2).1 < (p 3).1 := by
-- BODY
  let Rel (a b : CircleCoordinates) : Prop :=
    ((a.1 = 0 ∨ a.1 = 1) ∧ (b.1 = 0 ∨ b.1 = 1)) ∨
      (∃ t : Fin 4 → CircleCoordinates,
        ProperBandQuadruple t ∧ t 0 = a ∧ t 1 = b ∧ b.1 < a.1) ∨
      ∃ t : Fin 4 → CircleCoordinates,
        ProperBandQuadruple t ∧ t 0 = b ∧ t 1 = a ∧ a.1 < b.1
  have claim : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ProperBandQuadruple r →
      Rel (r 1) (r 2) ∧ Rel (r 2) (r 3) ∧ Rel (r 3) (r 1) := by
    intro r hr
    induction hr with
    | base z =>
        intro hproper
        have hbad := hproper.2 0
        simp at hbad
    | @rotate r hr ih =>
        intro hproper
        have old : ProperBandQuadruple r := by
          refine ⟨hr, ?_⟩
          intro j
          fin_cases j
          · simpa using hproper.2 2
          · simpa using hproper.2 0
          · simpa using hproper.2 1
        rcases ih old with ⟨h12, h23, h31⟩
        exact ⟨by simpa [Rel] using h23,
          by simpa [Rel] using h31,
          by simpa [Rel] using h12⟩
    | @successor r hr ih =>
        intro hproper
        rcases SemiProperForestClassification r hr with ⟨_, cases⟩
        rcases cases with root | root | root | old
        · rcases root with ⟨z, hz⟩
          rw [hz]
          simp [Rel]
        · rcases root with ⟨z, hz⟩
          rw [hz]
          simp [Rel]
        · rcases root with ⟨z, hz⟩
          rw [hz]
          simp [Rel]
        · rcases ih old with ⟨h12, h23, h31⟩
          have rot1 : ProperBandQuadruple ![r 0, r 2, r 3, r 1] := by
            refine ⟨SemiProperQuadruple.rotate old.1, ?_⟩
            intro j
            fin_cases j
            · simpa using old.2 1
            · simpa using old.2 2
            · simpa using old.2 0
          have rot2 : ProperBandQuadruple ![r 0, r 3, r 1, r 2] := by
            refine ⟨SemiProperQuadruple.rotate rot1.1, ?_⟩
            intro j
            fin_cases j
            · simpa using old.2 2
            · simpa using old.2 0
            · simpa using old.2 1
          constructor
          · dsimp
            right
            left
            exact ⟨![r 0, r 2, r 3, r 1], rot1, rfl, rfl,
              by simpa using old.2 1⟩
          constructor
          · simpa [Rel] using h23
          · dsimp
            right
            right
            exact ⟨![r 0, r 3, r 1, r 2], rot2, rfl, rfl,
              by simpa using old.2 2⟩
  exact (claim p hp.1 hp).2.1

end ApollonianSuperharmonic

end

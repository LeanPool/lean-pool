/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple

-- [TABLET NODE: BandParentBoundaryGenealogy]

/-!
# BandParentBoundaryGenealogy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandParentBoundaryGenealogy (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    (((q 1).1 = 1 ∧ (q 2).1 = 0 ∧ (q 3).1 = 1) ∨
      ((q 1).1 = 1 ∧ (q 2).1 = 1 ∧ (q 3).1 = 0) ∨
      ((q 1).1 = 0 ∧ (q 2).1 = 1 ∧ (q 3).1 = 1)) ∨
    (∃ p : Fin 4 → CircleCoordinates,
      ProperBandQuadruple p ∧
        q =
          ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
              2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
            p 0, p 2, p 3] ∧
        p 0 = q 1 ∧ p 2 = q 2 ∧ p 3 = q 3 ∧
        (q 2).1 < (q 1).1 ∧ (q 3).1 < (q 1).1) ∨
    (∃ p : Fin 4 → CircleCoordinates,
      ProperBandQuadruple p ∧
        ![q 0, q 2, q 3, q 1] =
          ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
              2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
            p 0, p 2, p 3] ∧
        p 0 = q 2 ∧ p 2 = q 3 ∧ p 3 = q 1 ∧
        (q 3).1 < (q 2).1 ∧ (q 1).1 < (q 2).1) ∨
    (∃ p : Fin 4 → CircleCoordinates,
      ProperBandQuadruple p ∧
        ![q 0, q 3, q 1, q 2] =
          ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
              2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
            p 0, p 2, p 3] ∧
        p 0 = q 3 ∧ p 2 = q 1 ∧ p 3 = q 2 ∧
        (q 1).1 < (q 3).1 ∧ (q 2).1 < (q 3).1) := by
-- BODY
  have claim : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ProperBandQuadruple r →
      (((r 1).1 = 1 ∧ (r 2).1 = 0 ∧ (r 3).1 = 1) ∨
        ((r 1).1 = 1 ∧ (r 2).1 = 1 ∧ (r 3).1 = 0) ∨
        ((r 1).1 = 0 ∧ (r 2).1 = 1 ∧ (r 3).1 = 1)) ∨
      (∃ p : Fin 4 → CircleCoordinates,
        ProperBandQuadruple p ∧
          r =
            ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
                2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
              p 0, p 2, p 3] ∧
          p 0 = r 1 ∧ p 2 = r 2 ∧ p 3 = r 3 ∧
          (r 2).1 < (r 1).1 ∧ (r 3).1 < (r 1).1) ∨
      (∃ p : Fin 4 → CircleCoordinates,
        ProperBandQuadruple p ∧
          ![r 0, r 2, r 3, r 1] =
            ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
                2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
              p 0, p 2, p 3] ∧
          p 0 = r 2 ∧ p 2 = r 3 ∧ p 3 = r 1 ∧
          (r 3).1 < (r 2).1 ∧ (r 1).1 < (r 2).1) ∨
      (∃ p : Fin 4 → CircleCoordinates,
        ProperBandQuadruple p ∧
          ![r 0, r 3, r 1, r 2] =
            ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
                2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
              p 0, p 2, p 3] ∧
          p 0 = r 3 ∧ p 2 = r 1 ∧ p 3 = r 2 ∧
          (r 1).1 < (r 3).1 ∧ (r 2).1 < (r 3).1) := by
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
        rcases ih old with roots | first | second | third
        · rcases roots with roots | roots | roots
          · left; right; right
            rcases roots with ⟨a, b, c⟩
            exact ⟨by simpa using b, by simpa using c, by simpa using a⟩
          · left; left
            rcases roots with ⟨a, b, c⟩
            exact ⟨by simpa using b, by simpa using c, by simpa using a⟩
          · left; right; left
            rcases roots with ⟨a, b, c⟩
            exact ⟨by simpa using b, by simpa using c, by simpa using a⟩
        · right; right; right
          rcases first with ⟨p, hp, hsucc, h0, h2, h3, h2lt, h3lt⟩
          exact ⟨p, hp, by
            apply Eq.trans ?_ hsucc
            funext i
            fin_cases i <;> rfl,
            h0, h2, h3,
            by simpa using h2lt, by simpa using h3lt⟩
        · right; left
          rcases second with ⟨p, hp, hsucc, h0, h2, h3, h3lt, h1lt⟩
          exact ⟨p, hp, hsucc, h0, h2, h3,
            by simpa using h3lt, by simpa using h1lt⟩
        · right; right; left
          rcases third with ⟨p, hp, hsucc, h0, h2, h3, h1lt, h2lt⟩
          exact ⟨p, hp, by
            apply Eq.trans ?_ hsucc
            funext i
            fin_cases i <;> rfl,
            h0, h2, h3,
            by simpa using h1lt, by simpa using h2lt⟩
    | @successor r hr ih =>
        intro hproper
        have forest := SemiProperForestClassification r hr
        rcases forest with ⟨nonneg, cases⟩
        rcases cases with root | root | root | old
        · rcases root with ⟨z, hz⟩
          have hbad := hproper.2 0
          rw [hz] at hbad
          simp at hbad
        · rcases root with ⟨z, hz⟩
          left
          rw [hz]
          simp
        · rcases root with ⟨z, hz⟩
          left
          rw [hz]
          simp
        · right
          left
          refine ⟨r, old, rfl, ?_, ?_, ?_, ?_, ?_⟩
          · rfl
          · rfl
          · rfl
          · simpa using old.2 1
          · simpa using old.2 2
  exact claim q hq.1 hq

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure

-- [TABLET NODE: P4566T1SmallPairCoordinates]

/-!
# P4566T1SmallPairCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4566T1SmallPairCoordinates
    (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (h2 : (p 2).1 = 0 ∨ (p 2).1 = 1)
    (h3 : (p 3).1 = 0 ∨ (p 3).1 = 1) :
    ∃ z : GaussianInt,
      (p 2 = (0, -1) ∧ p 3 = (1, 1 + 2 * z + 2 * ⟨0, 1⟩)) ∨
      (p 2 = (1, 1 + 2 * z + 2 * ⟨0, 1⟩) ∧ p 3 = (1, 1 + 2 * z)) ∨
      (p 2 = (1, 1 + 2 * z) ∧ p 3 = (0, -1)) ∨
      (p 2 = (1, 1 + 2 * z + 2 * ⟨0, 1⟩) ∧ p 3 = (0, 1)) ∨
      (p 2 = (0, 1) ∧ p 3 = (1, 1 + 2 * z)) ∨
      (p 2 = (1, 1 + 2 * z) ∧ p 3 = (1, 1 + 2 * z + 2 * ⟨0, 1⟩)) := by
-- BODY
  let Rel (a b : CircleCoordinates) : Prop :=
    ((a.1 = 0 ∨ a.1 = 1) ∧ (b.1 = 0 ∨ b.1 = 1)) →
    ∃ z : GaussianInt,
      (a = (0, -1) ∧ b = (1, 1 + 2 * z + 2 * ⟨0, 1⟩)) ∨
      (a = (1, 1 + 2 * z + 2 * ⟨0, 1⟩) ∧ b = (1, 1 + 2 * z)) ∨
      (a = (1, 1 + 2 * z) ∧ b = (0, -1)) ∨
      (a = (1, 1 + 2 * z + 2 * ⟨0, 1⟩) ∧ b = (0, 1)) ∨
      (a = (0, 1) ∧ b = (1, 1 + 2 * z)) ∨
      (a = (1, 1 + 2 * z) ∧ b = (1, 1 + 2 * z + 2 * ⟨0, 1⟩))
  have large (u : Fin 4 → CircleCoordinates) (hu : ProperBandQuadruple u) :
      1 < (u 0).1 := by
    have facts := ProperBandCurvatureStructure u hu
    have h0 := facts.2.1 0
    have h1 := facts.2.1 1
    have l0 := hu.2 0
    have l1 := hu.2 1
    by_contra hn
    have z0 : (u (0 : Fin 3).succ).1 = 0 := by omega
    have z1 : (u (1 : Fin 3).succ).1 = 0 := by omega
    exact (by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)
  have claim : ∀ u, SemiProperQuadruple u → ProperBandQuadruple u →
      Rel (u 1) (u 2) ∧ Rel (u 2) (u 3) ∧ Rel (u 3) (u 1) := by
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
        exact ⟨(ih old).2.1, (ih old).2.2, (ih old).1⟩
    | @successor u hs ih =>
        intro hu
        rcases (SemiProperForestClassification u hs).2 with root | root | root | old
        · rcases root with ⟨z, hz⟩
          have bad := hu.2 0
          simp [hz] at bad
        · rcases root with ⟨z, hz⟩
          rw [hz]
          refine ⟨?_, ?_, ?_⟩
          all_goals intro small
          all_goals exact ⟨z, by simp⟩
        · rcases root with ⟨z, hz⟩
          rw [hz]
          refine ⟨?_, ?_, ?_⟩
          all_goals intro small
          all_goals exact ⟨z, by simp⟩
        · have hl := large u old
          refine ⟨?_, (ih old).2.1, ?_⟩
          · intro small
            have h : (u 0).1 = 0 ∨ (u 0).1 = 1 := small.1
            rcases h with h | h <;> exact (by omega)
          · intro small
            have h : (u 0).1 = 0 ∨ (u 0).1 = 1 := small.2
            rcases h with h | h <;> exact (by omega)
  exact (claim p hp.1 hp).2.1 ⟨h2, h3⟩

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientationUnique
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure

-- [TABLET NODE: P4566T1UnitPairCharts]

/-!
# P4566T1UnitPairCharts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4566T1UnitPairCharts
    (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (i j : Fin 3) (hij : i ≠ j)
    (hi : (p i.succ).1 = 1) (hj : (p j.succ).1 = 1)
    (hd : PrimitiveVectorOrientation (p i.succ) (p j.succ)) :
    UnitOccurrenceOrientation p i false ∧
      UnitOccurrenceOrientation p j true := by
-- BODY
  have noReverse {A B : CircleCoordinates}
      (h : PrimitiveVectorOrientation A B) : ¬ PrimitiveVectorOrientation B A := by
    have ht := (PrimitiveVectorOrientationUnique A B).1 h
    rcases (PrimitiveVectorOrientationUnique A B).2 ht |>.2 with hd | hd
    · exact hd.2
    · exact (hd.2 h).elim
  let Charts (u : Fin 4 → CircleCoordinates) : Prop :=
    ∀ i j : Fin 3, i ≠ j → (u i.succ).1 = 1 → (u j.succ).1 = 1 →
      PrimitiveVectorOrientation (u i.succ) (u j.succ) →
        UnitOccurrenceOrientation u i false ∧ UnitOccurrenceOrientation u j true
  have leftSeed (z : GaussianInt) : Charts
      ![(4, 1 + 8 * z + 4 * ⟨0, 1⟩),
        (1, 1 + 2 * z), (0, -1), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)] := by
    intro a b hab ha hb hd
    fin_cases a <;> fin_cases b
    all_goals simp? at ha hb hd
    all_goals try { exact (hab rfl).elim }
    · exact (noReverse (PrimitiveVectorOrientation.base10 z) hd).elim
    · exact ⟨UnitOccurrenceOrientation.leftUpper z, UnitOccurrenceOrientation.leftLower z⟩
  have rightSeed (z : GaussianInt) : Charts
      ![(4, 7 + 8 * z + 4 * ⟨0, 1⟩),
        (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (0, 1)] := by
    intro a b hab ha hb hd
    fin_cases a <;> fin_cases b
    all_goals simp? at ha hb hd
    all_goals try { exact (hab rfl).elim }
    · exact (noReverse (PrimitiveVectorOrientation.base10 z) hd).elim
    · exact ⟨UnitOccurrenceOrientation.rightLower z, UnitOccurrenceOrientation.rightUpper z⟩
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
  have claim : ∀ u, SemiProperQuadruple u → ProperBandQuadruple u → Charts u := by
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
          · simpa using hu.2 2
          · simpa using hu.2 0
          · simpa using hu.2 1
        intro a b hab ha hb hd
        have hne : a + 1 ≠ b + 1 := by
          fin_cases a <;> fin_cases b <;> simp_all
        have ea : u (a + 1).succ = (![u 0, u 2, u 3, u 1] a.succ) := by
          fin_cases a <;> rfl
        have eb : u (b + 1).succ = (![u 0, u 2, u 3, u 1] b.succ) := by
          fin_cases b <;> rfl
        have pair := ih old (a + 1) (b + 1) hne (by simpa [ea] using ha)
          (by simpa [eb] using hb) (by simpa [ea, eb] using hd)
        constructor
        · have cert := UnitOccurrenceOrientation.rotate pair.1
          fin_cases a <;> simpa using cert
        · have cert := UnitOccurrenceOrientation.rotate pair.2
          fin_cases b <;> simpa using cert
    | @successor u hs ih =>
        intro hu
        rcases (SemiProperForestClassification u hs).2 with root | root | root | old
        · rcases root with ⟨z, hz⟩
          have bad := hu.2 0
          simp [hz] at bad
        · rcases root with ⟨z, hz⟩
          have eq :
              ![(2 * (u 0).1 + 2 * (u 2).1 + 2 * (u 3).1 - (u 1).1,
                  2 * (u 0).2 + 2 * (u 2).2 + 2 * (u 3).2 - (u 1).2),
                u 0, u 2, u 3] =
              ![(4, 1 + 8 * z + 4 * ⟨0, 1⟩),
                (1, 1 + 2 * z), (0, -1), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)] := by
            rw [hz]
            funext k
            fin_cases k <;> simp; ring
          rw [eq]
          exact leftSeed z
        · rcases root with ⟨z, hz⟩
          have eq :
              ![(2 * (u 0).1 + 2 * (u 2).1 + 2 * (u 3).1 - (u 1).1,
                  2 * (u 0).2 + 2 * (u 2).2 + 2 * (u 3).2 - (u 1).2),
                u 0, u 2, u 3] =
              ![(4, 7 + 8 * z + 4 * ⟨0, 1⟩),
                (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (0, 1)] := by
            rw [hz]
            funext k
            fin_cases k <;> simp; ring
          rw [eq]
          exact rightSeed z
        · have hl := large u old
          intro a b hab ha hb hd
          fin_cases a <;> fin_cases b
          all_goals simp at ha hb hd
          all_goals try { exact (hab rfl).elim }
          all_goals try { omega }
          · have pair := ih old 1 2 (by decide) ha hb hd
            exact ⟨UnitOccurrenceOrientation.retainSecondToThird old hb hd pair.1,
              UnitOccurrenceOrientation.retainThirdFromSecond old ha hd pair.2⟩
          · have pair := ih old 2 1 (by decide) ha hb hd
            exact ⟨UnitOccurrenceOrientation.retainThirdToSecond old hb hd pair.1,
              UnitOccurrenceOrientation.retainSecondFromThird old ha hd pair.2⟩
  exact claim p hp.1 hp i j hij hi hj hd

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification
public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: BandGenealogy]

/-!
# BandGenealogy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandGenealogy : ∀ C : BandCircle,
    C.1.1.1 = 1 ∨
    ∃ q : Fin 4 → CircleCoordinates,
      SemiProperQuadruple q ∧ q 0 = C.1.1 ∧
      (∀ j : Fin 3, (q j.succ).1 < C.1.1.1) ∧
      ∀ q' : Fin 4 → CircleCoordinates,
        SemiProperQuadruple q' → q' 0 = C.1.1 →
        (∀ j : Fin 3, (q' j.succ).1 < C.1.1.1) →
        ∀ D : CircleCoordinates,
          (∃ j : Fin 3, q j.succ = D) ↔ ∃ j : Fin 3, q' j.succ = D := by
-- BODY
  intro C
  have genealogy : ∀ (q : Fin 4 → CircleCoordinates),
      SemiProperQuadruple q → ∀ i : Fin 4, 0 < (q i).1 →
        (q i).1 = 1 ∨
        ∃ p : Fin 4 → CircleCoordinates,
          SemiProperQuadruple p ∧ p 0 = q i ∧
          (∀ j : Fin 3, (p j.succ).1 < (q i).1) ∧
          ∀ p' : Fin 4 → CircleCoordinates,
            SemiProperQuadruple p' → p' 0 = q i →
            (∀ j : Fin 3, (p' j.succ).1 < (q i).1) →
            ∀ D : CircleCoordinates,
              (∃ j : Fin 3, p j.succ = D) ↔
                ∃ j : Fin 3, p' j.succ = D := by
    intro q hq
    induction hq with
    | base z =>
        intro i hi
        fin_cases i <;> simp_all
    | rotate hq ih =>
        intro i hi
        fin_cases i
        · exact ih 0 hi
        · exact ih 2 hi
        · exact ih 3 hi
        · exact ih 1 hi
    | @successor q hq ih =>
        let s : Fin 4 → CircleCoordinates :=
          ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
              2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
            q 0, q 2, q 3]
        change ∀ i : Fin 4, 0 < (s i).1 →
          (s i).1 = 1 ∨
          ∃ p : Fin 4 → CircleCoordinates,
            SemiProperQuadruple p ∧ p 0 = s i ∧
            (∀ j : Fin 3, (p j.succ).1 < (s i).1) ∧
            ∀ p' : Fin 4 → CircleCoordinates,
              SemiProperQuadruple p' → p' 0 = s i →
              (∀ j : Fin 3, (p' j.succ).1 < (s i).1) →
              ∀ D : CircleCoordinates,
                (∃ j : Fin 3, p j.succ = D) ↔
                  ∃ j : Fin 3, p' j.succ = D
        have classification :
            (s 0).1 = 1 ∨
              (ProperBandQuadruple s ∧
                (q 0).1 < (s 0).1 ∧
                (q 2).1 < (s 0).1 ∧
                (q 3).1 < (s 0).1) := by
          simpa [s] using BandSuccessorClassification q hq
        intro i hi
        fin_cases i
        · rcases classification with hunit | hproper
          · exact Or.inl (by simpa using hunit)
          · rcases hproper with ⟨hs, h01, h02, h03⟩
            right
            refine ⟨s, hs.1, ?_, ?_, ?_⟩
            · simp [s]
            · intro j
              fin_cases j
              · simpa [s] using h01
              · simpa [s] using h02
              · simpa [s] using h03
            · intro p' hp' hchild hless D
              have hp'proper : ProperBandQuadruple p' :=
                ⟨hp', by simpa [hchild] using hless⟩
              have hsproper : ProperBandQuadruple s := ⟨hs.1, hs.2⟩
              have hchild_rev : s 0 = p' 0 := by simpa using hchild.symm
              obtain ⟨r, hr, _⟩ :=
                BandPredecessorNoCollision s p' hsproper hp'proper hchild_rev
              fin_cases r
              · constructor
                · rintro ⟨j, hj⟩
                  fin_cases j
                  · exact ⟨0, by simpa [Fin.add_def] using (hr 0).trans hj⟩
                  · exact ⟨1, by simpa [Fin.add_def] using (hr 1).trans hj⟩
                  · exact ⟨2, by simpa [Fin.add_def] using (hr 2).trans hj⟩
                · rintro ⟨j, hj⟩
                  fin_cases j
                  · exact ⟨0, by simpa [Fin.add_def] using (hr 0).symm.trans hj⟩
                  · exact ⟨1, by simpa [Fin.add_def] using (hr 1).symm.trans hj⟩
                  · exact ⟨2, by simpa [Fin.add_def] using (hr 2).symm.trans hj⟩
              · constructor
                · rintro ⟨j, hj⟩
                  fin_cases j
                  · exact ⟨2, by simpa [Fin.add_def] using (hr 2).trans hj⟩
                  · exact ⟨0, by simpa [Fin.add_def] using (hr 0).trans hj⟩
                  · exact ⟨1, by simpa [Fin.add_def] using (hr 1).trans hj⟩
                · rintro ⟨j, hj⟩
                  fin_cases j
                  · exact ⟨1, by simpa [Fin.add_def] using (hr 0).symm.trans hj⟩
                  · exact ⟨2, by simpa [Fin.add_def] using (hr 1).symm.trans hj⟩
                  · exact ⟨0, by simpa [Fin.add_def] using (hr 2).symm.trans hj⟩
              · constructor
                · rintro ⟨j, hj⟩
                  fin_cases j
                  · exact ⟨1, by simpa [Fin.add_def] using (hr 1).trans hj⟩
                  · exact ⟨2, by simpa [Fin.add_def] using (hr 2).trans hj⟩
                  · exact ⟨0, by simpa [Fin.add_def] using (hr 0).trans hj⟩
                · rintro ⟨j, hj⟩
                  fin_cases j
                  · exact ⟨2, by simpa [Fin.add_def] using (hr 0).symm.trans hj⟩
                  · exact ⟨0, by simpa [Fin.add_def] using (hr 1).symm.trans hj⟩
                  · exact ⟨1, by simpa [Fin.add_def] using (hr 2).symm.trans hj⟩
        · exact ih 0 hi
        · exact ih 2 hi
        · exact ih 3 hi
  rcases C.1.2.2 with ⟨q, hq, j, hj⟩
  have hpositive : 0 < (q j).1 := by simpa [hj] using C.2
  rcases genealogy q hq j hpositive with hunit | ⟨p, hp, hchild, hless, huniq⟩
  · exact Or.inl (by simpa [hj] using hunit)
  · right
    refine ⟨p, hp, ?_, ?_, ?_⟩
    · simpa [hj] using hchild
    · simpa [hj] using hless
    · intro p' hp' hchild' hless' D
      exact huniq p' hp' (by simpa [hj] using hchild')
        (by simpa [hj] using hless') D

end ApollonianSuperharmonic

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4994T6UnitCoordinates
public import LeanPool.ApollonianSuperharmonic.P4994T6ChamberAdditions
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientationUnique
public import LeanPool.ApollonianSuperharmonic.P4566T1UnitPairCharts

-- [TABLET NODE: P4994T6UnitOccurrenceChamber]

/-!
# P4994T6UnitOccurrenceChamber

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6UnitOccurrenceChamber
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (i : Fin 3) (hunit : (q i.succ).1 = 1)
    (orientation : Bool) (ho : UnitOccurrenceOrientation q i orientation) :
    let u := BandVectors.1 (q ((i + 1).succ)) (q i.succ)
    let v := (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q ((i + 2).succ))
    ∃ n < 6,
      P4994T6Chamber n (P4994T6UnitCoordinates orientation u) ∧
      P4994T6Chamber n (P4994T6UnitCoordinates orientation v) := by
-- BODY
  have second_update (a : Fin 4 → CircleCoordinates) (ha : ProperBandQuadruple a)
      (o : Bool)
      (old : ∃ n < 6,
        P4994T6Chamber n (P4994T6UnitCoordinates o (BandVectors.1 (a 3) (a 2))) ∧
        P4994T6Chamber n (P4994T6UnitCoordinates o
          ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 1)))) :
      ∃ n < 6,
        P4994T6Chamber n (P4994T6UnitCoordinates o (BandVectors.1 (a 3) (a 2))) ∧
        P4994T6Chamber n (P4994T6UnitCoordinates o
          ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 0))) := by
    obtain ⟨n, hn, hp, hr⟩ := old
    have recursion := (VectorRecursionLaws ![a 0, a 2, a 3, a 1]
      (SemiProperQuadruple.rotate ha.1)).2.2.1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at recursion
    have addition : (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 0) =
        BandVectors.1 (a 3) (a 2) +
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 1) := by
      rw [recursion]
      ext <;> simp <;> ring
    rw [addition, map_add]
    exact ⟨n, hn, hp, (P4994T6ChamberAdditions n _ _ hp hr).1⟩
  have third_update (a : Fin 4 → CircleCoordinates) (ha : ProperBandQuadruple a)
      (o : Bool)
      (old : ∃ n < 6,
        P4994T6Chamber n (P4994T6UnitCoordinates o (BandVectors.1 (a 1) (a 3))) ∧
        P4994T6Chamber n (P4994T6UnitCoordinates o
          ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 2)))) :
      ∃ n < 6,
        P4994T6Chamber n (P4994T6UnitCoordinates o (BandVectors.1 (a 0) (a 3))) ∧
        P4994T6Chamber n (P4994T6UnitCoordinates o
          ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 2))) := by
    obtain ⟨n, hn, hp, hr⟩ := old
    have recursion := (VectorRecursionLaws ![a 0, a 3, a 1, a 2]
      (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate ha.1))).2.2.1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at recursion
    have flip : BandVectors.1 (a 0) (a 3) =
        (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 0) := by
      simpa using ((VectorRecursionLaws a ha.1).2.2.2.2 ha 2).1
    have addition : BandVectors.1 (a 0) (a 3) =
        BandVectors.1 (a 1) (a 3) +
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 2) := by
      rw [flip, recursion]
      ext <;> simp <;> ring
    rw [addition, map_add]
    exact ⟨n, hn, (P4994T6ChamberAdditions n _ _ hp hr).1, hr⟩
  revert hq hunit
  induction ho with
  | leftLower z =>
      intro _ _
      have row := (P4994T6UnitRootTable z).1
      dsimp [P4828T1Root] at row
      dsimp only
      simp only [Fin.reduceAdd, Matrix.cons_val_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply]
      rw [row.1, row.2]
      refine ⟨2, by decide, ?_⟩
      norm_num [P4994T6Chamber, P4994T6Rotation, P4994T6UnitCoordinates]
  | leftUpper z =>
      intro _ _
      have row := (P4994T6UnitRootTable z).2.1
      dsimp [P4828T1Root] at row
      dsimp only
      simp only [Fin.reduceAdd, Matrix.cons_val_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply]
      rw [row.1, row.2]
      refine ⟨0, by decide, ?_⟩
      norm_num [P4994T6Chamber, P4994T6Rotation, P4994T6UnitCoordinates]
  | rightUpper z =>
      intro _ _
      have row := (P4994T6UnitRootTable z).2.2.1
      dsimp [P4828T1Root] at row
      dsimp only
      simp only [Fin.reduceAdd, Matrix.cons_val_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply]
      rw [row.1, row.2]
      refine ⟨0, by decide, ?_⟩
      norm_num [P4994T6Chamber, P4994T6Rotation, P4994T6UnitCoordinates]
  | rightLower z =>
      intro _ _
      have row := (P4994T6UnitRootTable z).2.2.2
      dsimp [P4828T1Root] at row
      dsimp only
      simp only [Fin.reduceAdd, Matrix.cons_val_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply]
      rw [row.1, row.2]
      refine ⟨5, by decide, ?_⟩
      norm_num [P4994T6Chamber, P4994T6Rotation, P4994T6UnitCoordinates]
  | @rotate a j o old ih =>
      intro ha hunit
      have previous : ProperBandQuadruple a := by
        refine ⟨?_, ?_⟩
        · have eta : (![a 0, a 1, a 2, a 3] : Fin 4 → CircleCoordinates) = a := by
            funext k
            fin_cases k <;> rfl
          simpa [eta] using SemiProperQuadruple.rotate (SemiProperQuadruple.rotate ha.1)
        · intro k
          fin_cases k
          · simpa using ha.2 (2 : Fin 3)
          · simpa using ha.2 (0 : Fin 3)
          · simpa using ha.2 (1 : Fin 3)
      fin_cases j <;> simpa using ih previous (by simpa using hunit)
  | @retainSecondOther a o ha _ old ih =>
      intro _ hunit
      exact second_update a ha o (by simpa using ih ha (by simpa using hunit))
  | @retainThirdOther a o ha _ old ih =>
      intro _ hunit
      exact third_update a ha o (by simpa using ih ha (by simpa using hunit))
  | @retainSecondToThird a o ha hs hd old ih =>
      intro _ hunit
      have hu : (a 2).1 = 1 := by simpa using hunit
      have expected := (P4566T1UnitPairCharts a ha 1 2 (by decide) hu hs hd).1
      have eqo : o = false := (UnitOccurrenceOrientationUnique.1 a ha 1 hu).unique old expected
      subst o
      exact second_update a ha false (by simpa using ih ha hu)
  | @retainSecondFromThird a o ha hs hd old ih =>
      intro _ hunit
      have hu : (a 2).1 = 1 := by simpa using hunit
      have expected := (P4566T1UnitPairCharts a ha 2 1 (by decide) hs hu hd).2
      have eqo : o = true := (UnitOccurrenceOrientationUnique.1 a ha 1 hu).unique old expected
      subst o
      exact second_update a ha true (by simpa using ih ha hu)
  | @retainThirdFromSecond a o ha hs hd old ih =>
      intro _ hunit
      have hu : (a 3).1 = 1 := by simpa using hunit
      have expected := (P4566T1UnitPairCharts a ha 1 2 (by decide) hs hu hd).2
      have eqo : o = true := (UnitOccurrenceOrientationUnique.1 a ha 2 hu).unique old expected
      subst o
      exact third_update a ha true (by simpa using ih ha hu)
  | @retainThirdToSecond a o ha hs hd old ih =>
      intro _ hunit
      have hu : (a 3).1 = 1 := by simpa using hunit
      have expected := (P4566T1UnitPairCharts a ha 2 1 (by decide) hu hs hd).1
      have eqo : o = false := (UnitOccurrenceOrientationUnique.1 a ha 2 hu).unique old expected
      subst o
      exact third_update a ha false (by simpa using ih ha hu)

end ApollonianSuperharmonic

end

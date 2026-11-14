/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4981T1PrescriptionValue
public import LeanPool.ApollonianSuperharmonic.P4981T1Recursion
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientation

-- [TABLET NODE: P4981T1RootEquations]

/-!
# P4981T1RootEquations

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4981T1RootEquations
    (F : CircleCoordinates × CircleCoordinates → GaussianInt × GaussianInt)
    (rev : ∀ C D, PrimitiveVectorOrientation C D →
      F (D, C) = ((⟨0, 1⟩ : GaussianInt) * (F (C, D)).1,
        -(⟨0, 1⟩ : GaussianInt) * (F (C, D)).2)) :
    ((∀ z : GaussianInt,
      let q : Fin 4 → CircleCoordinates :=
        ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)),
          (0, 1), (0, -1)]
      (F (q 3, q 2)).1 = 0 ∧ (F (q 2, q 1)).1 = -1 ∧
      (F (q 1, q 3)).1 = 1 ∧ (F (q 3, q 2)).2 = 1 ∧
      (F (q 2, q 1)).2 = -1 - z - (⟨0, 1⟩ : GaussianInt) ∧
      (F (q 1, q 3)).2 = z + (⟨0, 1⟩ : GaussianInt)) ∧
    (∀ (z : GaussianInt) (r : Fin 3),
      let p : Fin 3 → CircleCoordinates :=
        ![(1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)), (0, 1), (0, -1)]
      P4981T1Recursion F ![(1, 1 + 2 * z), p r, p (r + 1), p (r + 2)])) ↔
    (F ((0, -1), (0, 1)) = P4981T1PrescriptionValue .line F ∧
      ∀ z, F ((0, 1), (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt))) =
          P4981T1PrescriptionValue (.left z) F ∧
        F ((0, -1), (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt))) =
          P4981T1PrescriptionValue (.right z) F ∧
        F ((1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)), (1, 1 + 2 * z)) =
          P4981T1PrescriptionValue (.unit z) F) := by
-- BODY
  let ii : GaussianInt := ⟨0, 1⟩
  change ∀ U V, PrimitiveVectorOrientation U V →
    F (V, U) = (ii * (F (U, V)).1, -ii * (F (U, V)).2) at rev
  have square : ii * ii = -1 := by decide +kernel
  let X (z : GaussianInt) : CircleCoordinates := (1, 1 + 2 * z)
  let A (z : GaussianInt) : CircleCoordinates := (1, 1 + 2 * z + 2 * ii)
  let B : CircleCoordinates := (0, 1)
  let C : CircleCoordinates := (0, -1)
  have inv (U V : CircleCoordinates) (hp : PrimitiveVectorOrientation U V) :
      F (U, V) = (-ii * (F (V, U)).1, ii * (F (V, U)).2) := by
    rw [rev U V hp]
    simp only [neg_mul, mul_neg, ← mul_assoc, square, neg_neg, one_mul]
  constructor
  · rintro ⟨base, rec⟩
    refine ⟨Prod.ext (base 0).1 (base 0).2.2.2.1, ?_⟩
    intro z
    have ba : F (B, A z) = (-1, -1 - z - ii) :=
      Prod.ext (base z).2.1 (base z).2.2.2.2.1
    have ac : F (A z, C) = (1, z + ii) :=
      Prod.ext (base z).2.2.1 (base z).2.2.2.2.2
    refine ⟨ba, ?_, ?_⟩
    · have ca := inv C (A z) (.base31 z)
      rw [ac] at ca
      change F (C, A z) = (-ii, ii * z - 1)
      rw [ca]
      apply Prod.ext <;> dsimp only
      · ring
      · simp only [mul_add, square]
        ring
    · have equations := rec z 2
      change P4981T1Recursion F ![X z, C, A z, B] at equations
      change F (A z, X z) = (1 + ii, 1 + z - ii * z)
      apply Prod.ext
      · calc
          (F (A z, X z)).1 = (F (A z, C)).1 - ii * (F (B, A z)).1 := equations.1
          _ = 1 + ii := by rw [ac, ba]; dsimp only; ring
      · calc
          (F (A z, X z)).2 = (F (A z, C)).2 + ii * (F (B, A z)).2 := equations.2.2.1
          _ = 1 + z - ii * z := by
            rw [ac, ba]
            dsimp only
            simp only [mul_sub, mul_neg, square, mul_one]
            ring
  · rintro ⟨line, table⟩
    have cb : F (C, B) = (0, 1) := line
    have ba (z) : F (B, A z) = (-1, -1 - z - ii) := (table z).1
    have ca (z) : F (C, A z) = (-ii, ii * z - 1) := (table z).2.1
    have ax (z) : F (A z, X z) = (1 + ii, 1 + z - ii * z) := (table z).2.2
    have ac (z) : F (A z, C) = (1, z + ii) := by
      rw [rev C (A z) (.base31 z), ca z]
      apply Prod.ext <;> dsimp only
      · simp only [mul_neg, square, neg_neg]
      · simp only [neg_mul, mul_sub, ← mul_assoc, square, mul_one]
        ring
    have shift (z) : A (z - ii) = X z := by
      dsimp [A, X]
      congr 1
      ring
    have bx (z) : F (B, X z) = (-1, -1 - z) := by
      have h := ba (z - ii)
      rw [shift] at h
      rw [h]
      congr 1
      ring
    have cx (z) : F (C, X z) = (-ii, ii * z) := by
      have h := ca (z - ii)
      rw [shift] at h
      rw [h]
      congr 1
      simp only [mul_sub, square]
      ring
    have xc (z) : F (X z, C) = (1, z) := by
      have hp : PrimitiveVectorOrientation C (X z) := by
        rw [← shift z]
        exact .base31 (z - ii)
      rw [rev C (X z) hp, cx z]
      apply Prod.ext <;> dsimp only
      · simp only [mul_neg, square, neg_neg]
      · simp only [neg_mul, ← mul_assoc, square, neg_neg, one_mul]
    have xb (z) : F (X z, B) = (-ii, ii + ii * z) := by
      have hp : PrimitiveVectorOrientation B (X z) := by
        rw [← shift z]
        exact .base21 (z - ii)
      rw [rev B (X z) hp, bx z]
      apply Prod.ext <;> dsimp only <;> ring
    have xa (z) : F (X z, A z) = (-1 + ii, -z - ii - ii * z) := by
      rw [rev (A z) (X z) (.base10 z), ax z]
      apply Prod.ext <;> dsimp only
      · simp only [mul_add, square, mul_one]
        ring
      · simp only [neg_mul, mul_sub, mul_add, ← mul_assoc, square, mul_one]
        ring
    constructor
    · intro z
      change (F (C, B)).1 = 0 ∧ (F (B, A z)).1 = -1 ∧
        (F (A z, C)).1 = 1 ∧ (F (C, B)).2 = 1 ∧
        (F (B, A z)).2 = -1 - z - ii ∧ (F (A z, C)).2 = z + ii
      rw [cb, ba z, ac z]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro z r
      change P4981T1Recursion F
        ![X z, ![A z, B, C] r, ![A z, B, C] (r + 1), ![A z, B, C] (r + 2)]
      fin_cases r
      all_goals first
        | change
            (F (B, X z)).1 = (F (B, A z)).1 - ii * (F (C, B)).1 ∧
            (F (X z, C)).1 = (F (A z, C)).1 + ii * (F (C, B)).1 ∧
            (F (B, X z)).2 = (F (B, A z)).2 + ii * (F (C, B)).2 ∧
            (F (X z, C)).2 = (F (A z, C)).2 - ii * (F (C, B)).2
        | change
            (F (C, X z)).1 = (F (C, B)).1 - ii * (F (A z, C)).1 ∧
            (F (X z, A z)).1 = (F (B, A z)).1 + ii * (F (A z, C)).1 ∧
            (F (C, X z)).2 = (F (C, B)).2 + ii * (F (A z, C)).2 ∧
            (F (X z, A z)).2 = (F (B, A z)).2 - ii * (F (A z, C)).2
        | change
            (F (A z, X z)).1 = (F (A z, C)).1 - ii * (F (B, A z)).1 ∧
            (F (X z, B)).1 = (F (C, B)).1 + ii * (F (B, A z)).1 ∧
            (F (A z, X z)).2 = (F (A z, C)).2 + ii * (F (B, A z)).2 ∧
            (F (X z, B)).2 = (F (C, B)).2 - ii * (F (B, A z)).2
      all_goals simp only [cb, ba z, ac z, ax z, bx z, cx z, xc z, xa z, xb z]
      all_goals refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try simp only [mul_add, mul_sub, mul_neg, square, mul_one, mul_zero]
      all_goals ring

end ApollonianSuperharmonic

end

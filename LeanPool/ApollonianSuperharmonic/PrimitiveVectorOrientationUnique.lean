/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandTangency
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientation
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: PrimitiveVectorOrientationUnique]

/-!
# PrimitiveVectorOrientationUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PrimitiveOrientation

private def Good : (Fin 4 → CircleCoordinates) → Prop := fun q =>
  (∀ i j : Fin 4, i ≠ j → q i ≠ q j) ∧
    (∀ i j : Fin 4, i ≠ j →
      PrimitiveVectorOrientation (q i) (q j) ∨
        PrimitiveVectorOrientation (q j) (q i))

private theorem baseGood : ∀ z, Good (![ (1, 1 + 2 * z),
    (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)), (0, 1), (0, -1) ]) := by
  intro z
  constructor
  · intro i j hij hsame
    fin_cases i <;> fin_cases j
    all_goals try { exact (hij rfl).elim }
    all_goals norm_num [Zsqrtd.ext_iff] at hsame
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp only [Int.reduceNeg, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta, or_self]
    · exact (hij rfl).elim
    · exact Or.inr (PrimitiveVectorOrientation.base10 z)
    · convert Or.inr (PrimitiveVectorOrientation.base21 (z - ⟨0, 1⟩)) using 1; ring
    · convert Or.inr (PrimitiveVectorOrientation.base31 (z - ⟨0, 1⟩)) using 1; ring
    · exact Or.inl (PrimitiveVectorOrientation.base10 z)
    · exact (hij rfl).elim
    · exact Or.inr (PrimitiveVectorOrientation.base21 z)
    · exact Or.inr (PrimitiveVectorOrientation.base31 z)
    · convert Or.inl (PrimitiveVectorOrientation.base21 (z - ⟨0, 1⟩)) using 1; ring
    · exact Or.inl (PrimitiveVectorOrientation.base21 z)
    · exact (hij rfl).elim
    · exact Or.inr (PrimitiveVectorOrientation.base32 z)
    · convert Or.inl (PrimitiveVectorOrientation.base31 (z - ⟨0, 1⟩)) using 1; ring
    · exact Or.inl (PrimitiveVectorOrientation.base31 z)
    · exact Or.inl (PrimitiveVectorOrientation.base32 z)
    · exact (hij rfl).elim

private theorem rotateGood : ∀ {q}, Good q → Good (![q 0, q 2, q 3, q 1]) := by
  intro q hq
  rcases hq with ⟨distinct, oriented⟩
  constructor
  · intro i j hij hsame
    fin_cases i <;> fin_cases j
    all_goals try { exact (hij rfl).elim }
    · exact distinct 0 2 (by decide) hsame
    · exact distinct 0 3 (by decide) hsame
    · exact distinct 0 1 (by decide) hsame
    · exact distinct 2 0 (by decide) hsame
    · exact distinct 2 3 (by decide) hsame
    · exact distinct 2 1 (by decide) hsame
    · exact distinct 3 0 (by decide) hsame
    · exact distinct 3 2 (by decide) hsame
    · exact distinct 3 1 (by decide) hsame
    · exact distinct 1 0 (by decide) hsame
    · exact distinct 1 2 (by decide) hsame
    · exact distinct 1 3 (by decide) hsame
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals dsimp
    · exact (hij rfl).elim
    · exact oriented 0 2 (by decide)
    · exact oriented 0 3 (by decide)
    · exact oriented 0 1 (by decide)
    · exact oriented 2 0 (by decide)
    · exact (hij rfl).elim
    · exact oriented 2 3 (by decide)
    · exact oriented 2 1 (by decide)
    · exact oriented 3 0 (by decide)
    · exact oriented 3 2 (by decide)
    · exact (hij rfl).elim
    · exact oriented 3 1 (by decide)
    · exact oriented 1 0 (by decide)
    · exact oriented 1 2 (by decide)
    · exact oriented 1 3 (by decide)
    · exact (hij rfl).elim

private theorem invariant : ∀ q, SemiProperQuadruple q → Good q := by
  intro q hq
  induction hq with
  | base z => exact baseGood z
  | rotate hq ih =>
      exact rotateGood ih
  | @successor q hq ih =>
      rcases ih with ⟨distinct, oriented⟩
      let r := ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
        2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2), q 0, q 2, q 3]
      have classification := SemiProperForestClassification r (SemiProperQuadruple.successor hq)
      change Good r
      rcases classification.2 with root | root | root | proper
      · rcases root with ⟨z, hz⟩
        rw [hz]
        exact baseGood z
      · rcases root with ⟨z, hz⟩
        rw [hz]
        exact rotateGood (baseGood z)
      · rcases root with ⟨z, hz⟩
        rw [hz]
        exact rotateGood (rotateGood (baseGood z))
      · rcases proper with ⟨hs, inequalities⟩
        constructor
        · intro i j hij hsame
          have h0 := inequalities 0
          have h1 := inequalities 1
          have h2 := inequalities 2
          fin_cases i <;> fin_cases j
          all_goals dsimp [r] at h0 h1 h2 hsame
          all_goals try { exact (hij rfl).elim }
          all_goals try { have curv := congrArg Prod.fst hsame; omega }
          · exact distinct 0 2 (by decide) hsame
          · exact distinct 0 3 (by decide) hsame
          · exact distinct 2 0 (by decide) hsame
          · exact distinct 2 3 (by decide) hsame
          · exact distinct 3 0 (by decide) hsame
          · exact distinct 3 2 (by decide) hsame
        · intro i j hij
          fin_cases i <;> fin_cases j
          · exact (hij rfl).elim
          · simpa using (Or.inr (PrimitiveVectorOrientation.parentChild ⟨hs, inequalities⟩ 0))
          · simpa using (Or.inr (PrimitiveVectorOrientation.parentChild ⟨hs, inequalities⟩ 1))
          · simpa using (Or.inr (PrimitiveVectorOrientation.parentChild ⟨hs, inequalities⟩ 2))
          · simpa using (Or.inl (PrimitiveVectorOrientation.parentChild ⟨hs, inequalities⟩ 0))
          · exact (hij rfl).elim
          · exact oriented 0 2 (by decide)
          · exact oriented 0 3 (by decide)
          · simpa using (Or.inl (PrimitiveVectorOrientation.parentChild ⟨hs, inequalities⟩ 1))
          · exact oriented 2 0 (by decide)
          · exact (hij rfl).elim
          · exact oriented 2 3 (by decide)
          · simpa using (Or.inl (PrimitiveVectorOrientation.parentChild ⟨hs, inequalities⟩ 2))
          · exact oriented 3 0 (by decide)
          · exact oriented 3 2 (by decide)
          · exact (hij rfl).elim

private theorem curvature : ∀ {A B : CircleCoordinates},
    PrimitiveVectorOrientation A B → A.1 ≤ B.1 := by
  intro A B h
  cases h with
  | base32 z => omega
  | base21 z => omega
  | base31 z => omega
  | base10 z => omega
  | parentChild hq j => exact le_of_lt (by simpa using hq.2 j)

private theorem equalShape : ∀ {A B : CircleCoordinates},
    PrimitiveVectorOrientation A B → A.1 = B.1 →
      (A = (0, -1) ∧ B = (0, 1)) ∨
        ∃ z : GaussianInt,
          A = (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)) ∧
          B = (1, 1 + 2 * z) := by
  intro A B h equal
  cases h with
  | base32 z => exact Or.inl ⟨rfl, rfl⟩
  | base21 z => omega
  | base31 z => omega
  | base10 z => exact Or.inr ⟨z, rfl, rfl⟩
  | parentChild hq j =>
      have strict := hq.2 j
      omega

private theorem noReverse : ∀ {A B : CircleCoordinates},
    PrimitiveVectorOrientation A B → ¬ PrimitiveVectorOrientation B A := by
  intro A B first second
  have forward := curvature first
  have backward := curvature second
  rcases equalShape first (le_antisymm forward backward) with left | left
  · rcases left with ⟨leftA, leftB⟩
    rcases equalShape second (le_antisymm backward forward) with right | right
    · rcases right with ⟨rightA, rightB⟩
      have bad : ((0 : ℤ), (1 : GaussianInt)) = (0, -1) := leftB.symm.trans rightA
      norm_num at bad
    · rcases right with ⟨z, rightA, rightB⟩
      have bad := congrArg Prod.fst (leftB.symm.trans rightA)
      norm_num at bad
  · rcases left with ⟨z, leftA, leftB⟩
    rcases equalShape second (le_antisymm backward forward) with right | right
    · rcases right with ⟨rightA, rightB⟩
      have bad := congrArg Prod.fst (leftA.symm.trans rightB)
      norm_num at bad
    · rcases right with ⟨w, rightA, rightB⟩
      have e1 := congrArg Prod.snd (leftB.symm.trans rightA)
      have e2 := congrArg Prod.snd (leftA.symm.trans rightB)
      norm_num [Zsqrtd.ext_iff] at e1 e2
      omega

end PrimitiveOrientation

open PrimitiveOrientation

theorem PrimitiveVectorOrientationUnique (C D : CircleCoordinates) :
    (PrimitiveVectorOrientation C D → BandTangency C D) ∧
      (BandTangency C D →
        C ≠ D ∧
          Xor (PrimitiveVectorOrientation C D)
            (PrimitiveVectorOrientation D C)) := by
  constructor
  · intro h
    cases h with
    | base32 z =>
        exact ⟨![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)], ⟨SemiProperQuadruple.base z,
            ⟨3, 2, by decide, rfl, rfl⟩⟩⟩
    | base21 z =>
        exact ⟨![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)], ⟨SemiProperQuadruple.base z,
            ⟨2, 1, by decide, rfl, rfl⟩⟩⟩
    | base31 z =>
        exact ⟨![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)], ⟨SemiProperQuadruple.base z,
            ⟨3, 1, by decide, rfl, rfl⟩⟩⟩
    | base10 z =>
        exact ⟨![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)], ⟨SemiProperQuadruple.base z,
            ⟨1, 0, by decide, rfl, rfl⟩⟩⟩
    | parentChild hq j =>
        exact ⟨_, hq.1, j.succ, 0, by simp, rfl, rfl⟩
  · intro tangency
    rcases tangency with ⟨q, hq, i, j, hij, hi, hj⟩
    have good := invariant q hq
    have distinct := good.1 i j hij
    have directions := good.2 i j hij
    constructor
    · simpa [hi, hj] using distinct
    · rcases directions with forward | backward
      · rw [← hi, ← hj]
        exact Or.inl ⟨forward, noReverse forward⟩
      · rw [← hi, ← hj]
        exact Or.inr ⟨backward, noReverse backward⟩

end ApollonianSuperharmonic

end

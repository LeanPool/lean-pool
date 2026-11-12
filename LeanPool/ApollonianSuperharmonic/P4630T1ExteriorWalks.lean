/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.P4630T1RingIndex
public import Mathlib.LinearAlgebra.Matrix.Notation

-- [TABLET NODE: P4630T1ExteriorWalks]

/-!
# P4630T1ExteriorWalks

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4630T1ExteriorWalks :
    let safe := fun a : PeriodicSubtileIndex =>
      ¬ (a.first = 0 ∧ a.second = 0) ∧
        ∀ i k, a ≠ P4630T1RingIndex i k
    ∀ a, safe a → ∃ f : Nat → PeriodicSubtileIndex,
      Function.Injective f ∧ ∀ n,
        (f n).label = .A ∧ safe (f n) ∧
          Relation.ReflTransGen
            (fun x y => AllowedSubtileIncidence x y ∧ safe x ∧ safe y)
            a (f n) := by
-- BODY
  let safe := fun a : PeriodicSubtileIndex =>
    ¬ (a.first = 0 ∧ a.second = 0) ∧
      ∀ i k, a ≠ P4630T1RingIndex i k
  let E := fun x y => AllowedSubtileIncidence x y ∧ safe x ∧ safe y
  change ∀ a, safe a → ∃ f : Nat → PeriodicSubtileIndex,
    Function.Injective f ∧ ∀ n, (f n).label = .A ∧ safe (f n) ∧
      Relation.ReflTransGen E a (f n)
  have edge {a b} (h : AllowedSubtileIncidence a b)
      (ha : safe a) (hb : safe b) : Relation.ReflTransGen E a b :=
    .single ⟨h, ha, hb⟩
  have attach : ∀ a, safe a → ∃ m n,
      safe ⟨.A, m, n⟩ ∧ Relation.ReflTransGen E a ⟨.A, m, n⟩ := by
    rintro ⟨l, m, n⟩ ha
    by_cases h₁ : m = -1 ∧ n = -1
    · rcases h₁ with ⟨rfl, rfl⟩
      have hb : Relation.ReflTransGen E ⟨.B, -1, -1⟩ ⟨.A, -1, -2⟩ :=
        (edge (.BF0m1 (-1) (-1)) (by decide) (by decide)).trans
          (edge (.symm (.AF (-1) (-2))) (by decide) (by decide))
      have hc : Relation.ReflTransGen E ⟨.C, -1, -1⟩ ⟨.A, -2, -1⟩ :=
        (edge (.CEm10 (-1) (-1)) (by decide) (by decide)).trans
          ((edge (.symm (.BE (-2) (-1))) (by decide) (by decide)).trans
            (edge (.symm (.AB (-2) (-1))) (by decide) (by decide)))
      cases l
      · exact False.elim (ha.2 0 0 rfl)
      · exact ⟨-1, -2, by decide, hb⟩
      · exact ⟨-2, -1, by decide, hc⟩
      · exact False.elim (ha.2 1 3 rfl)
      · exact ⟨-1, -2, by decide,
          (edge (.symm (.BE (-1) (-1))) ha (by decide)).trans hb⟩
      · exact ⟨-2, -1, by decide,
          (edge (.symm (.CF (-1) (-1))) ha (by decide)).trans hc⟩
    by_cases h₂ : m = 0 ∧ n = -1
    · rcases h₂ with ⟨rfl, rfl⟩
      have hb : Relation.ReflTransGen E ⟨.B, 0, -1⟩ ⟨.A, -1, -2⟩ :=
        (edge (.BDm1m1 0 (-1)) (by decide) (by decide)).trans
          (edge (.symm (.AD (-1) (-2))) (by decide) (by decide))
      have hc : Relation.ReflTransGen E ⟨.C, 0, -1⟩ ⟨.A, -1, -2⟩ :=
        (edge (.CEm10 0 (-1)) (by decide) (by decide)).trans
          ((edge (.symm (.BE (-1) (-1))) (by decide) (by decide)).trans
            ((edge (.BF0m1 (-1) (-1)) (by decide) (by decide)).trans
              (edge (.symm (.AF (-1) (-2))) (by decide) (by decide))))
      cases l
      · exact False.elim (ha.2 0 1 rfl)
      · exact ⟨-1, -2, by decide, hb⟩
      · exact ⟨-1, -2, by decide, hc⟩
      · exact ⟨-1, -2, by decide,
          (edge (.symm (.BD 0 (-1))) ha (by decide)).trans hb⟩
      · exact ⟨-1, -2, by decide,
          (edge (.symm (.BE 0 (-1))) ha (by decide)).trans hb⟩
      · exact False.elim (ha.2 2 2 rfl)
    have hA : safe ⟨.A, m, n⟩ := by
      have hz := ha.1
      simp [safe, P4630T1RingIndex, Fin.forall_fin_succ,
        PeriodicSubtileIndex.mk.injEq] at *
      omega
    refine ⟨m, n, hA, ?_⟩
    cases l
    · exact .refl
    · exact edge (.symm (.AB m n)) ha hA
    · exact edge (.symm (.AC m n)) ha hA
    · exact edge (.symm (.AD m n)) ha hA
    · by_cases h₃ : m = 1 ∧ n = 1
      · rcases h₃ with ⟨rfl, rfl⟩
        exact (edge (.symm (.DE 1 1)) ha (by decide)).trans
          (edge (.symm (.AD 1 1)) (by decide) hA)
      · have hB : safe ⟨.B, m, n⟩ := by
          simp [safe, P4630T1RingIndex, Fin.forall_fin_succ,
            PeriodicSubtileIndex.mk.injEq] at *
          omega
        exact (edge (.symm (.BE m n)) ha hB).trans
          (edge (.symm (.AB m n)) hB hA)
    · exact edge (.symm (.AF m n)) ha hA
  intro a ha
  obtain ⟨m, n, hA, hp⟩ := attach a ha
  by_cases east : ((n - m = -1 ∨ n - m = 0) ∧ 0 < m) ∨
      (n - m = 1 ∧ 0 ≤ m)
  · let f : Nat → PeriodicSubtileIndex := fun j => ⟨.A, m + j, n + j⟩
    have hf (j : Nat) : safe (f j) := by
      simp [f, safe, P4630T1RingIndex, Fin.forall_fin_succ,
        PeriodicSubtileIndex.mk.injEq] at hA ⊢
      omega
    have hm (j : Nat) : safe ⟨.B, m + j + 1, n + j + 1⟩ := by
      simp [safe, P4630T1RingIndex, Fin.forall_fin_succ,
        PeriodicSubtileIndex.mk.injEq]
      omega
    refine ⟨f, ?_, fun j => ⟨rfl, hf j, ?_⟩⟩
    · intro j k h
      have he := congrArg PeriodicSubtileIndex.first h
      dsimp [f] at he
      omega
    · induction j with
      | zero => simpa [f] using hp
      | succ j ih =>
        apply ih.trans
        have hstep := (edge (.AB11 (m + j) (n + j)) (hf j) (hm j)).trans
          (edge (.symm (.AB (m + j + 1) (n + j + 1))) (hm j)
            (by simpa [f, Nat.cast_add, Nat.cast_one, add_assoc] using hf (j + 1)))
        simpa [f, Nat.cast_add, Nat.cast_one, add_assoc] using hstep
  · let f : Nat → PeriodicSubtileIndex := fun j => ⟨.A, m - j, n - j⟩
    have hf (j : Nat) : safe (f j) := by
      simp [f, safe, P4630T1RingIndex, Fin.forall_fin_succ,
        PeriodicSubtileIndex.mk.injEq] at hA ⊢
      omega
    have hm (j : Nat) : safe ⟨.B, m - j, n - j⟩ := by
      simp [safe, P4630T1RingIndex, Fin.forall_fin_succ,
        PeriodicSubtileIndex.mk.injEq] at hA ⊢
      omega
    refine ⟨f, ?_, fun j => ⟨rfl, hf j, ?_⟩⟩
    · intro j k h
      have he := congrArg PeriodicSubtileIndex.first h
      dsimp [f] at he
      omega
    · induction j with
      | zero => simpa [f] using hp
      | succ j ih =>
        apply ih.trans
        have he : AllowedSubtileIncidence ⟨.B, m - j, n - j⟩ (f (j + 1)) := by
          convert (AllowedSubtileIncidence.AB11
            (m - (j + 1 : Nat)) (n - (j + 1 : Nat))).symm using 1;
            simp [Nat.cast_add, Nat.cast_one, PeriodicSubtileIndex.mk.injEq];
            omega
        exact (edge (.AB (m - j) (n - j)) (hf j) (hm j)).trans
          (edge he (hm j) (hf (j + 1)))

end ApollonianSuperharmonic

end

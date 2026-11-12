/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence

-- [TABLET NODE: P3055T1ExteriorCentralIncidence]

/-!
# P3055T1ExteriorCentralIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ExteriorCentralProof

private theorem ledger :
    let R : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop := fun a b =>
      ((a.label = .A ∧ b.label = .B ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .A ∧ a.label = .B ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .A ∧ b.label = .B ∧
          b.first = a.first + (0) ∧ b.second = a.second + (1)) ∨
        (b.label = .A ∧ a.label = .B ∧
          a.first = b.first + (0) ∧ a.second = b.second + (1))) ∨
      ((a.label = .A ∧ b.label = .B ∧
          b.first = a.first + (1) ∧ b.second = a.second + (1)) ∨
        (b.label = .A ∧ a.label = .B ∧
          a.first = b.first + (1) ∧ a.second = b.second + (1))) ∨
      ((a.label = .A ∧ b.label = .C ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .A ∧ a.label = .C ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .A ∧ b.label = .C ∧
          b.first = a.first + (1) ∧ b.second = a.second + (1)) ∨
        (b.label = .A ∧ a.label = .C ∧
          a.first = b.first + (1) ∧ a.second = b.second + (1))) ∨
      ((a.label = .A ∧ b.label = .D ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .A ∧ a.label = .D ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .A ∧ b.label = .E ∧
          b.first = a.first + (0) ∧ b.second = a.second + (1)) ∨
        (b.label = .A ∧ a.label = .E ∧
          a.first = b.first + (0) ∧ a.second = b.second + (1))) ∨
      ((a.label = .A ∧ b.label = .F ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .A ∧ a.label = .F ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .B ∧ b.label = .C ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .B ∧ a.label = .C ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .B ∧ b.label = .D ∧
          b.first = a.first + (-1) ∧ b.second = a.second + (-1)) ∨
        (b.label = .B ∧ a.label = .D ∧
          a.first = b.first + (-1) ∧ a.second = b.second + (-1))) ∨
      ((a.label = .B ∧ b.label = .D ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .B ∧ a.label = .D ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .B ∧ b.label = .E ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .B ∧ a.label = .E ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .B ∧ b.label = .F ∧
          b.first = a.first + (0) ∧ b.second = a.second + (-1)) ∨
        (b.label = .B ∧ a.label = .F ∧
          a.first = b.first + (0) ∧ a.second = b.second + (-1))) ∨
      ((a.label = .C ∧ b.label = .D ∧
          b.first = a.first + (-1) ∧ b.second = a.second + (0)) ∨
        (b.label = .C ∧ a.label = .D ∧
          a.first = b.first + (-1) ∧ a.second = b.second + (0))) ∨
      ((a.label = .C ∧ b.label = .E ∧
          b.first = a.first + (-1) ∧ b.second = a.second + (0)) ∨
        (b.label = .C ∧ a.label = .E ∧
          a.first = b.first + (-1) ∧ a.second = b.second + (0))) ∨
      ((a.label = .C ∧ b.label = .F ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .C ∧ a.label = .F ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .D ∧ b.label = .E ∧
          b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
        (b.label = .D ∧ a.label = .E ∧
          a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
      ((a.label = .D ∧ b.label = .F ∧
          b.first = a.first + (1) ∧ b.second = a.second + (0)) ∨
        (b.label = .D ∧ a.label = .F ∧
          a.first = b.first + (1) ∧ a.second = b.second + (0)))
    ∀ a, ∀ b, AllowedSubtileIncidence a b → R a b := by
  classical
  intro R a b h
  induction h with
  | AB m n =>
    exact Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp []⟩)
  | AB01 m n =>
    exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp []⟩))
  | AB11 m n =>
    exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp []⟩)))
  | AC m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp []⟩))))
  | AC11 m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp []⟩)))))
  | AD m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp
        []⟩))))))
  | AE01 m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [],
        by simp []⟩)))))))
  | AF m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl,
        by simp [], by simp []⟩))))))))
  | BC m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl,
        rfl, by simp [], by simp []⟩)))))))))
  | BDm1m1 m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Or.inl ⟨rfl, rfl, by simp [sub_eq_add_neg], by simp [sub_eq_add_neg]⟩))))))))))
  | BD m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp []⟩)))))))))))
  | BE m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp []⟩))))))))))))
  | BF0m1 m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp
        [sub_eq_add_neg]⟩)))))))))))))
  | CDm10 m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [sub_eq_add_neg], by simp
        []⟩))))))))))))))
  | CEm10 m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [sub_eq_add_neg],
        by simp []⟩)))))))))))))))
  | CF m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [], by simp
        []⟩))))))))))))))))
  | DE m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl, by simp [],
        by simp []⟩)))))))))))))))))
  | DF10 m n =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp [],
        by simp []⟩)))))))))))))))))
  | symm _ ih =>
    dsimp only [R] at ih ⊢
    rcases ih with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rcases h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
    · rcases h with h | h
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inl (Or.inl h))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr
          h)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
          h)))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (Or.inr h))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (Or.inl h))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (Or.inr h)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (Or.inl h)))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl (Or.inr h))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl (Or.inl h))))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl (Or.inr h)))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl (Or.inl h)))))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))))))))))))))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))

end ExteriorCentralProof

theorem P3055T1ExteriorCentralIncidence (a b : PeriodicSubtileIndex)
    (ha : a = ⟨.A, -1, -1⟩ ∨
      a = ⟨.A, 0, -1⟩ ∨
      a = ⟨.C, 1, 0⟩ ∨
      a = ⟨.C, 1, 1⟩ ∨
      a = ⟨.E, 0, 1⟩ ∨
      a = ⟨.E, -1, 0⟩ ∨
      a = ⟨.B, 1, 1⟩ ∨
      a = ⟨.B, 0, 1⟩ ∨
      a = ⟨.D, -1, 0⟩ ∨
      a = ⟨.D, -1, -1⟩ ∨
      a = ⟨.F, 0, -1⟩ ∨
      a = ⟨.F, 1, 0⟩)
    (hb : b = ⟨.A, 0, 0⟩ ∨
      b = ⟨.B, 0, 0⟩ ∨
      b = ⟨.C, 0, 0⟩ ∨
      b = ⟨.D, 0, 0⟩ ∨
      b = ⟨.E, 0, 0⟩ ∨
      b = ⟨.F, 0, 0⟩)
    (hinc : AllowedSubtileIncidence a b) :
    (a = ⟨.A, -1, -1⟩ ∧ b = ⟨.B, 0, 0⟩) ∨
    (a = ⟨.A, -1, -1⟩ ∧ b = ⟨.C, 0, 0⟩) ∨
    (a = ⟨.A, 0, -1⟩ ∧ b = ⟨.B, 0, 0⟩) ∨
    (a = ⟨.A, 0, -1⟩ ∧ b = ⟨.E, 0, 0⟩) ∨
    (a = ⟨.C, 1, 0⟩ ∧ b = ⟨.D, 0, 0⟩) ∨
    (a = ⟨.C, 1, 0⟩ ∧ b = ⟨.E, 0, 0⟩) ∨
    (a = ⟨.C, 1, 1⟩ ∧ b = ⟨.A, 0, 0⟩) ∨
    (a = ⟨.E, 0, 1⟩ ∧ b = ⟨.A, 0, 0⟩) ∨
    (a = ⟨.E, -1, 0⟩ ∧ b = ⟨.C, 0, 0⟩) ∨
    (a = ⟨.B, 1, 1⟩ ∧ b = ⟨.A, 0, 0⟩) ∨
    (a = ⟨.B, 1, 1⟩ ∧ b = ⟨.D, 0, 0⟩) ∨
    (a = ⟨.B, 0, 1⟩ ∧ b = ⟨.A, 0, 0⟩) ∨
    (a = ⟨.B, 0, 1⟩ ∧ b = ⟨.F, 0, 0⟩) ∨
    (a = ⟨.D, -1, 0⟩ ∧ b = ⟨.C, 0, 0⟩) ∨
    (a = ⟨.D, -1, 0⟩ ∧ b = ⟨.F, 0, 0⟩) ∨
    (a = ⟨.D, -1, -1⟩ ∧ b = ⟨.B, 0, 0⟩) ∨
    (a = ⟨.F, 0, -1⟩ ∧ b = ⟨.B, 0, 0⟩) ∨
    (a = ⟨.F, 1, 0⟩ ∧ b = ⟨.D, 0, 0⟩) := by
-- BODY
  let R : PeriodicSubtileIndex → PeriodicSubtileIndex → Prop := fun a b =>
    ((a.label = .A ∧ b.label = .B ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .A ∧ a.label = .B ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .A ∧ b.label = .B ∧
        b.first = a.first + (0) ∧ b.second = a.second + (1)) ∨
      (b.label = .A ∧ a.label = .B ∧
        a.first = b.first + (0) ∧ a.second = b.second + (1))) ∨
    ((a.label = .A ∧ b.label = .B ∧
        b.first = a.first + (1) ∧ b.second = a.second + (1)) ∨
      (b.label = .A ∧ a.label = .B ∧
        a.first = b.first + (1) ∧ a.second = b.second + (1))) ∨
    ((a.label = .A ∧ b.label = .C ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .A ∧ a.label = .C ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .A ∧ b.label = .C ∧
        b.first = a.first + (1) ∧ b.second = a.second + (1)) ∨
      (b.label = .A ∧ a.label = .C ∧
        a.first = b.first + (1) ∧ a.second = b.second + (1))) ∨
    ((a.label = .A ∧ b.label = .D ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .A ∧ a.label = .D ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .A ∧ b.label = .E ∧
        b.first = a.first + (0) ∧ b.second = a.second + (1)) ∨
      (b.label = .A ∧ a.label = .E ∧
        a.first = b.first + (0) ∧ a.second = b.second + (1))) ∨
    ((a.label = .A ∧ b.label = .F ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .A ∧ a.label = .F ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .B ∧ b.label = .C ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .B ∧ a.label = .C ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .B ∧ b.label = .D ∧
        b.first = a.first + (-1) ∧ b.second = a.second + (-1)) ∨
      (b.label = .B ∧ a.label = .D ∧
        a.first = b.first + (-1) ∧ a.second = b.second + (-1))) ∨
    ((a.label = .B ∧ b.label = .D ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .B ∧ a.label = .D ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .B ∧ b.label = .E ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .B ∧ a.label = .E ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .B ∧ b.label = .F ∧
        b.first = a.first + (0) ∧ b.second = a.second + (-1)) ∨
      (b.label = .B ∧ a.label = .F ∧
        a.first = b.first + (0) ∧ a.second = b.second + (-1))) ∨
    ((a.label = .C ∧ b.label = .D ∧
        b.first = a.first + (-1) ∧ b.second = a.second + (0)) ∨
      (b.label = .C ∧ a.label = .D ∧
        a.first = b.first + (-1) ∧ a.second = b.second + (0))) ∨
    ((a.label = .C ∧ b.label = .E ∧
        b.first = a.first + (-1) ∧ b.second = a.second + (0)) ∨
      (b.label = .C ∧ a.label = .E ∧
        a.first = b.first + (-1) ∧ a.second = b.second + (0))) ∨
    ((a.label = .C ∧ b.label = .F ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .C ∧ a.label = .F ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .D ∧ b.label = .E ∧
        b.first = a.first + (0) ∧ b.second = a.second + (0)) ∨
      (b.label = .D ∧ a.label = .E ∧
        a.first = b.first + (0) ∧ a.second = b.second + (0))) ∨
    ((a.label = .D ∧ b.label = .F ∧
        b.first = a.first + (1) ∧ b.second = a.second + (0)) ∨
      (b.label = .D ∧ a.label = .F ∧
        a.first = b.first + (1) ∧ a.second = b.second + (0)))
  have ledger : ∀ a b, AllowedSubtileIncidence a b → R a b := ExteriorCentralProof.ledger
  have hr := ledger a b hinc
  dsimp [R] at hr
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

end ApollonianSuperharmonic

end

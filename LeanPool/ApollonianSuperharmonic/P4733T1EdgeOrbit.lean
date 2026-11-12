/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4733T1EdgeRow
public import LeanPool.ApollonianSuperharmonic.P4733T1Coordinates

-- [TABLET NODE: P4733T1EdgeOrbit]

/-!
# P4733T1EdgeOrbit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1EdgeOrbit {u v : GaussianInt} {L : AddSubgroup GaussianInt}
    (D : P4677T2DrawingData u v L) (a b : PeriodicSubtileIndex)
    (hab : AllowedSubtileIncidence a b) :
    ∃ r : Fin 18, ∃ w : L,
      (a = D.shift w (P4733T1EdgeRow r).1.1 ∧
        b = D.shift w (P4733T1EdgeRow r).1.2) ∨
      (a = D.shift w (P4733T1EdgeRow r).1.2 ∧
        b = D.shift w (P4733T1EdgeRow r).1.1) := by
-- BODY
  induction hab with
  | AB m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨0, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | AB01 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨1, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | AB11 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨2, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | AC m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨3, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | AC11 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨4, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | AD m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨5, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | AE01 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨6, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | AF m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨7, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | BC m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨8, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | BDm1m1 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨9, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, sub_eq_add_neg, add_comm]
  | BD m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨10, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | BE m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨11, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | BF0m1 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨12, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, sub_eq_add_neg, add_comm]
  | CDm10 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨13, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, sub_eq_add_neg, add_comm]
  | CEm10 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨14, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, sub_eq_add_neg, add_comm]
  | CF m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨15, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | DE m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨16, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | DF10 m n =>
    obtain ⟨w, hw⟩ := (P4733T1Coordinates D).2 (m, n)
    refine ⟨17, w, Or.inl ?_⟩
    simp [P4733T1EdgeRow, D.shift_eq, hw, add_comm]
  | symm _ ih =>
    obtain ⟨r, w, h | h⟩ := ih
    · exact ⟨r, w, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨r, w, Or.inl ⟨h.2, h.1⟩⟩

end ApollonianSuperharmonic

end

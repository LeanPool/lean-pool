/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

public import LeanPool.ApollonianSuperharmonic.P4715T1VertexShift
public import LeanPool.ApollonianSuperharmonic.P4715T1FaceShift
public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices

-- [TABLET NODE: P4715T1IndexAction]

/-!
# P4715T1IndexAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1IndexAction :
    (∀ a, P4715T1VertexShift 0 a = a) ∧
    (∀ k l a, P4715T1VertexShift (k + l) a =
      P4715T1VertexShift k (P4715T1VertexShift l a)) ∧
    (∀ f, P4715T1FaceShift 0 f = f) ∧
    (∀ k l f, P4715T1FaceShift (k + l) f =
      P4715T1FaceShift k (P4715T1FaceShift l f)) ∧
    (∀ k a b, AllowedSubtileIncidence (P4715T1VertexShift k a)
      (P4715T1VertexShift k b) ↔ AllowedSubtileIncidence a b) ∧
    ∀ k f i, SixSubtileFaceVertices (P4715T1FaceShift k f) i =
      P4715T1VertexShift k (SixSubtileFaceVertices f i) := by
-- BODY
  have vz (a) : P4715T1VertexShift 0 a = a := by
    cases a; simp [P4715T1VertexShift]
  have va (k l a) : P4715T1VertexShift (k + l) a =
      P4715T1VertexShift k (P4715T1VertexShift l a) := by
    simp [P4715T1VertexShift, add_comm, add_left_comm]
  have fz (f) : P4715T1FaceShift 0 f = f := by
    cases f; simp [P4715T1FaceShift]
  have fa (k l f) : P4715T1FaceShift (k + l) f =
      P4715T1FaceShift k (P4715T1FaceShift l f) := by
    simp [P4715T1FaceShift, add_comm, add_left_comm]
  have forward (k : Int × Int) {a b} (h : AllowedSubtileIncidence a b) :
      AllowedSubtileIncidence (P4715T1VertexShift k a)
        (P4715T1VertexShift k b) := by
    induction h with
    | symm _ ih => exact .symm ih
    | AB m n => exact .AB _ _
    | AB01 m n => simpa [P4715T1VertexShift, add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.AB01 (m + k.1) (n + k.2)
    | AB11 m n => simpa [P4715T1VertexShift, add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.AB11 (m + k.1) (n + k.2)
    | AC m n => exact .AC _ _
    | AC11 m n => simpa [P4715T1VertexShift, add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.AC11 (m + k.1) (n + k.2)
    | AD m n => exact .AD _ _
    | AE01 m n => simpa [P4715T1VertexShift, add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.AE01 (m + k.1) (n + k.2)
    | AF m n => exact .AF _ _
    | BC m n => exact .BC _ _
    | BDm1m1 m n => simpa [P4715T1VertexShift, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.BDm1m1 (m + k.1) (n + k.2)
    | BD m n => exact .BD _ _
    | BE m n => exact .BE _ _
    | BF0m1 m n => simpa [P4715T1VertexShift, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.BF0m1 (m + k.1) (n + k.2)
    | CDm10 m n => simpa [P4715T1VertexShift, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.CDm10 (m + k.1) (n + k.2)
    | CEm10 m n => simpa [P4715T1VertexShift, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.CEm10 (m + k.1) (n + k.2)
    | CF m n => exact .CF _ _
    | DE m n => exact .DE _ _
    | DF10 m n => simpa [P4715T1VertexShift, add_assoc, add_comm, add_left_comm]
        using AllowedSubtileIncidence.DF10 (m + k.1) (n + k.2)
  refine ⟨vz, va, fz, fa, ?_, ?_⟩
  · intro k a b
    constructor
    · intro h
      have hh := forward (-k) h
      simpa only [← va, neg_add_cancel, vz] using hh
    · exact forward k
  · rintro k ⟨l, m, n⟩ i
    cases l <;> fin_cases i <;>
      simp [P4715T1FaceShift, P4715T1VertexShift, SixSubtileFaceVertices,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

end ApollonianSuperharmonic

end

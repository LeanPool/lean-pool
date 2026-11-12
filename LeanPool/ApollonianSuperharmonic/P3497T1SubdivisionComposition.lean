/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3475T1BoundarySubdivision
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P3497T1SubdivisionComposition]

/-!
# P3497T1SubdivisionComposition

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3497T1SubdivisionComposition {r m n : Nat}
    {q : P3381T1PolygonBoundary r}
    {v : P3381T1PolygonBoundary m}
    {p : P3381T1PolygonBoundary n}
    (A : P3475T1BoundarySubdivision q v)
    (B : P3475T1BoundarySubdivision v p) :
    Nonempty (P3475T1BoundarySubdivision q p) := by
-- BODY
  classical
  let finish : Fin (m + 3) → Real := fun k =>
    if A.edge (k + 1) = A.edge k then A.parameter (k + 1) else 1
  have finish_gt (k : Fin (m + 3)) : A.parameter k < finish k := by
    rcases A.successor k with h | h
    · simp only [finish, ite_eq_left h.1]
      exact h.2
    · have hne : A.edge (k + 1) ≠ A.edge k := by
        rw [h.1]
        intro heq
        have hone : (1 : Fin (r + 3)) = 0 := add_left_cancel (heq.trans (add_zero _).symm)
        have hval := congrArg Fin.val hone
        simp at hval
      simp only [finish, ite_eq_right hne]
      exact A.parameter_lt_one k
  have finish_le (k : Fin (m + 3)) : finish k ≤ 1 := by
    dsimp [finish]
    split_ifs
    · exact le_of_lt (A.parameter_lt_one _)
    · exact le_rfl
  have endpoint (k : Fin (m + 3)) :
      v.vertex (k + 1) = (1 - finish k) • q.vertex (A.edge k) +
        finish k • q.vertex (A.edge k + 1) := by
    rcases A.successor k with h | h
    · simpa only [finish, ite_eq_left h.1, h.1] using A.vertex_formula (k + 1)
    · have hne : A.edge (k + 1) ≠ A.edge k := by
        rw [h.1]
        intro heq
        have hone : (1 : Fin (r + 3)) = 0 := add_left_cancel (heq.trans (add_zero _).symm)
        have hval := congrArg Fin.val hone
        simp at hval
      simpa only [finish, ite_eq_right hne, h.1, h.2, sub_zero, zero_smul,
        one_smul, add_zero, sub_self, zero_add] using A.vertex_formula (k + 1)
  let t : Fin (n + 3) → Real := fun j =>
    A.parameter (B.edge j) +
      (finish (B.edge j) - A.parameter (B.edge j)) * B.parameter j
  have t_bounds (j : Fin (n + 3)) : 0 ≤ t j ∧ t j < 1 := by
    have h0 := A.parameter_nonneg (B.edge j)
    have h1 := finish_gt (B.edge j)
    have h2 := finish_le (B.edge j)
    have h3 := B.parameter_nonneg j
    have h4 := B.parameter_lt_one j
    dsimp [t]
    constructor <;> nlinarith
  refine ⟨{ start := B.start ∘ A.start
            start_injective := B.start_injective.comp A.start_injective
            edge := A.edge ∘ B.edge
            parameter := t
            parameter_nonneg := fun j => (t_bounds j).1
            parameter_lt_one := fun j => (t_bounds j).2
            edge_start := ?_
            parameter_start := ?_
            vertex_formula := ?_
            successor := ?_
            carrier_eq := B.carrier_eq.trans A.carrier_eq }⟩
  · intro i
    simp only [Function.comp_apply, B.edge_start, A.edge_start]
  · intro i
    simp only [Function.comp_apply, t, B.edge_start, B.parameter_start,
      A.parameter_start, mul_zero, add_zero]
  · intro j
    rw [B.vertex_formula j, A.vertex_formula (B.edge j), endpoint (B.edge j)]
    dsimp [Function.comp_def, t]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> ring
  · intro j
    rcases B.successor j with h | h
    · left
      constructor
      · dsimp [Function.comp_def]
        rw [h.1]
      · dsimp [t]
        rw [h.1]
        have hgt := finish_gt (B.edge j)
        nlinarith [h.2]
    · rcases A.successor (B.edge j) with ha | ha
      · left
        constructor
        · dsimp [Function.comp_def]
          rw [h.1]
          exact ha.1
        · have hb := B.parameter_lt_one j
          have hgt := finish_gt (B.edge j)
          dsimp [t]
          rw [h.1, h.2, mul_zero, add_zero]
          simp only [finish, ite_eq_left ha.1] at hgt ⊢
          nlinarith
      · right
        constructor
        · dsimp [Function.comp_def]
          rw [h.1]
          exact ha.1
        · dsimp [t]
          rw [h.1, h.2, ha.2, mul_zero, add_zero]

end ApollonianSuperharmonic

end

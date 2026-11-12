/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3475T1BoundarySubdivision
public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant
public import LeanPool.ApollonianSuperharmonic.P3497T1SingleStraightDeletion
public import LeanPool.ApollonianSuperharmonic.P3497T1SubdivisionComposition
public import LeanPool.ApollonianSuperharmonic.P3497T1TriangleCornerNonzero

-- [TABLET NODE: P3475T1BoundaryReduction]

/-!
# P3475T1BoundaryReduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3475T1BoundaryReduction {n : Nat}
    (p : P3381T1PolygonBoundary n) :
    ∃ (r : Nat) (q : P3381T1PolygonBoundary r),
      Nonempty (P3475T1BoundarySubdivision q p) ∧
      ∀ i : Fin (r + 3),
        P3381T1TriangleDeterminant (fun j : Fin 3 =>
          q.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_left 3 r)⟩)) ≠ 0 := by
-- BODY
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hcorner : ∀ i : Fin (n + 3),
        P3381T1TriangleDeterminant (fun j : Fin 3 =>
          p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_left 3 n)⟩)) ≠ 0
    · refine ⟨n, p, ?_, hcorner⟩
      refine ⟨{ start := id
                start_injective := fun _ _ h => h
                edge := id
                parameter := fun _ => 0
                parameter_nonneg := fun _ => le_rfl
                parameter_lt_one := fun _ => by norm_num
                edge_start := fun _ => rfl
                parameter_start := fun _ => rfl
                vertex_formula := ?_
                successor := ?_
                carrier_eq := rfl }⟩
      · intro j
        simp
      · intro j
        exact Or.inr ⟨rfl, rfl⟩
    · push Not at hcorner
      obtain ⟨i, hdet⟩ := hcorner
      cases n with
      | zero => exact False.elim (P3497T1TriangleCornerNonzero p i hdet)
      | succ n =>
        obtain ⟨v, _, ⟨B⟩⟩ := P3497T1SingleStraightDeletion p i hdet
        obtain ⟨r, q, ⟨A⟩, hq⟩ := ih n (Nat.lt_succ_self n) v
        exact ⟨r, q, P3497T1SubdivisionComposition A B, hq⟩

end ApollonianSuperharmonic

end

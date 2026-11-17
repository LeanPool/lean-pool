/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3475T1BoundarySubdivision

/-!
# P3523T1SubdivisionExit

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Fin.NatCast

-- [TABLET NODE: P3523T1SubdivisionExit]
theorem P3523T1SubdivisionExit {r n : Nat}
    (q : P3381T1PolygonBoundary r) (p : P3381T1PolygonBoundary n)
    (s : P3475T1BoundarySubdivision q p) :
    (∀ j, s.parameter j = 0 → j = s.start (s.edge j)) ∧
    (∀ j, ∃ k : Nat, k < n + 3 ∧
      s.edge (j + (Nat.cast (k + 1) : Fin (n + 3))) ≠ s.edge j) := by
-- BODY
  let : NeZero (n + 3) := ⟨by omega⟩
  let : NeZero (r + 3) := ⟨by omega⟩
  constructor
  · intro j hz
    apply p.injective
    rw [s.vertex_formula j, s.vertex_formula (s.start (s.edge j)),
      s.edge_start, s.parameter_start, hz]
  · intro j
    classical
    by_contra h
    push Not at h
    have he (k : Nat) (hk : k ≤ n + 3) :
        s.edge (j + (Nat.cast k : Fin (n + 3))) = s.edge j := by
      cases k with
      | zero => simp
      | succ k => exact h k (by omega)
    have hinc (k : Nat) (hk : k < n + 3) :
        s.parameter (j + (Nat.cast k : Fin (n + 3))) <
          s.parameter (j + (Nat.cast (k + 1) : Fin (n + 3))) := by
      rcases s.successor (j + (Nat.cast k : Fin (n + 3))) with hs | hs
      · simpa [Nat.cast_add, add_assoc] using hs.2
      · have hcoarse : s.edge (j + (Nat.cast k : Fin (n + 3))) + 1 =
            s.edge (j + (Nat.cast k : Fin (n + 3))) := by
          have hsame := (he (k + 1) (by omega)).trans (he k (by omega)).symm
          have hadv : s.edge (j + (Nat.cast (k + 1) : Fin (n + 3))) =
              s.edge (j + (Nat.cast k : Fin (n + 3))) + 1 := by
            simpa [Nat.cast_add, add_assoc] using hs.1
          exact hadv.symm.trans hsame
        simp at hcoarse
    have hchain (k : Nat) (hk : k ≤ n + 3) :
        s.parameter j ≤ s.parameter (j + (Nat.cast k : Fin (n + 3))) := by
      induction k with
      | zero => simp
      | succ k ih => exact (ih (by omega)).trans (hinc k (by omega)).le
    have hlast := (hchain (n + 2) (by omega)).trans_lt (hinc (n + 2) (by omega))
    simp at hlast

end ApollonianSuperharmonic

end

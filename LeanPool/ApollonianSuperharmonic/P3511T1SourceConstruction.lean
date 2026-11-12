/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3511T1SourceDissection
public import LeanPool.ApollonianSuperharmonic.P3544T1DiagonalSelection
public import LeanPool.ApollonianSuperharmonic.P3544T1IndexedGluing

-- [TABLET NODE: P3511T1SourceConstruction]

/-!
# P3511T1SourceConstruction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3511T1SourceConstruction :
    ∀ {n : Nat}, ∀ (p : P3381T1PolygonBoundary n), (∀ i : Fin (n + 3),
      P3381T1TriangleDeterminant (fun j : Fin 3 =>
        p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_left 3 n)⟩)) ≠ 0) → (∃ X :
            Set (Real × Real), Nonempty (P3511T1SourceDissection p X)) := by
  intro n p hcorner
-- BODY
  classical
  -- The children may have straight corners, so the induction omits hcorner.
  have construct : ∀ m (q : P3381T1PolygonBoundary m),
      ∃ X : Set (Real × Real), Nonempty (P3511T1SourceDissection q X) ∧
        X = closure (P3544T1RayParity q) ∧
        IsPathConnected (P3544T1RayParity q) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro q
      have hclosure := (P3544T1LocalParity q).1
      cases m with
      | zero =>
        obtain ⟨hdet, hfill, hpath⟩ := P3544T1TriangleRayGeometry q
        let f : Fin 1 → Fin 3 → Fin 3 := fun _ j => j
        refine ⟨convexHull Real (Set.range q.vertex),
          ⟨{ count := 1
             count_pos := by decide
             face := f
             dissection := ?_
             face_injective := ?_
             face_distinct := ?_
             vertex_used := ?_
             nondegenerate := ?_
             cover := ?_
             intersection := ?_
             edge_count := ?_ }⟩,
          hfill.trans hclosure.symm, hpath⟩
        · have hid : (![0, 1, 2] : Fin 3 → Fin 3) = fun j => j := by
            funext j
            fin_cases j <;> rfl
          have ht := P3511T1CyclicDissection.triangle (0 : Fin 3) 1 2
          rw [hid] at ht
          exact ht
        · intro k
          exact Function.injective_id
        · intro k l _
          exact Subsingleton.elim k l
        · intro i
          exact ⟨0, i, rfl⟩
        · intro k
          exact hdet
        · change convexHull Real (Set.range q.vertex) =
            ⋃ _ : Fin 1, convexHull Real (Set.range q.vertex)
          ext x
          constructor
          · intro hx
            exact Set.mem_iUnion.mpr ⟨(0 : Fin 1), hx⟩
          · intro hx
            obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
            exact hk
        · intro k l
          change convexHull Real (Set.range q.vertex) ∩
              convexHull Real (Set.range q.vertex) =
            convexHull Real (q.vertex '' (Set.range (fun j : Fin 3 => j) ∩
              Set.range (fun j : Fin 3 => j)))
          simp
        · intro i j hij
          have hneighbor : j = i + 1 ∨ i = j + 1 := by
            have h : ∀ i j : Fin 3, i ≠ j → j = i + 1 ∨ i = j + 1 := by
              decide
            exact h i j hij
          simp [f, hneighbor]
      | succ m =>
        obtain ⟨S⟩ := P3544T1DiagonalSelection q (Nat.succ_pos m)
        obtain ⟨XL, ⟨L⟩, hL, hcL⟩ := ih S.leftParameter S.left_lt S.left
        obtain ⟨XR, ⟨R⟩, hR, hcR⟩ := ih S.rightParameter S.right_lt S.right
        have hLfill := hL.trans (P3544T1LocalParity S.left).1
        have hRfill := hR.trans (P3544T1LocalParity S.right).1
        obtain ⟨Z, _hfaces, hfill, hpath⟩ :=
          P3544T1IndexedGluing S L R hLfill hRfill hcL hcR
        exact ⟨XL ∪ XR, ⟨Z⟩, hfill.trans hclosure.symm, hpath⟩
  obtain ⟨X, hX, _⟩ := construct n p
  exact ⟨X, hX⟩

end ApollonianSuperharmonic

end

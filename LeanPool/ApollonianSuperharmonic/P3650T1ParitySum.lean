/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3650T1CyclicChildren
public import LeanPool.ApollonianSuperharmonic.P3544T1LocalParity

/-!
# P3650T1ParitySum

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic


-- [TABLET NODE: P3650T1ParitySum]
namespace PolygonParityProof

private theorem cardPred :
    (by
      classical
      exact
        ∀ {k : ℕ}, ∀ (P : Fin k → Prop), ∀ [inst : DecidablePred P], {i : Fin k | P i}.ncard = ∑
            i : Fin k, if P i then (1 : ℕ) else (0 : ℕ) ) := by
  classical
  intro k P typeclassInstance0
  have hset : ({i : Fin k | P i} : Set (Fin k)) =
      ((Finset.univ.filter P : Finset (Fin k)) : Set (Fin k)) := by
    ext i
    simp
  rw [hset, Set.ncard_coe_finset, Finset.card_filter]

private theorem edges_cons :
    (by
      classical
      exact
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        ∀ {A : Type}, ∀ (a : A), ∀ (l : List A), edges (a :: l) = List.zipWith Prod.mk (a :: l)
            (l ++ [a]) ) := by
  classical
  intro edges A a l
  simp [edges]

private theorem path_split :
    (by
      classical
      exact
        ∀ {A : Type}, ∀ (a : A), ∀ (b : A), ∀ (z : A), ∀ (u : List A), ∀ (v : List A),
            List.zipWith Prod.mk (a :: (u ++ b :: v)) (u ++ b :: v ++ [z]) = List.zipWith Prod.mk
            (a :: u) (u ++ [b]) ++ List.zipWith Prod.mk (b :: v) (v ++ [z]) ) := by
  classical
  intro A a b z u v
  induction u generalizing a with
  | nil => simp
  | cons c u ih => simpa using congrArg (fun l => (a, c) :: l) (ih c)

private theorem edges_split :
    (by
      classical
      exact
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        (∀ {A : Type}, ∀ (a : A), ∀ (l : List A), edges (a :: l) = List.zipWith Prod.mk (a :: l)
            (l ++ [a])) → ((∀ {A : Type}, ∀ (a : A), ∀ (b : A), ∀ (z : A), ∀ (u : List A), ∀ (v :
            List A), List.zipWith Prod.mk (a :: (u ++ b :: v)) ((u ++ b :: v) ++ [z]) =
            List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ List.zipWith Prod.mk (b :: v) (v ++ [z]))
            → (∀ {A : Type}, ∀ (a : A), ∀ (b : A), ∀ (u : List A), ∀ (v : List A), edges (a :: (u
            ++ b :: v)) = List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ List.zipWith Prod.mk (b ::
            v) (v ++ [a]))) ) := by
  classical
  intro edges edges_cons path_split A a b u v
  rw [edges_cons, path_split]

private theorem edges_arc :
    (by
      classical
      exact
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        (∀ {A : Type}, ∀ (a : A), ∀ (b : A), ∀ (u : List A), ∀ (v : List A), edges (a :: (u ++ b
            :: v)) = List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ List.zipWith Prod.mk (b :: v) (v
            ++ [a])) → (∀ {A : Type}, ∀ (a : A), ∀ (b : A), ∀ (u : List A), edges (a :: (u ++
            [b])) = List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ [(b, a)]) ) := by
  classical
  intro edges edges_split A a b u
  simpa using edges_split a b u []

private theorem edges_rotate :
    (by
      classical
      exact
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        ∀ {A : Type}, ∀ (l : List A), ∀ (k : ℕ), edges (l.rotate k) = (edges l).rotate k ) := by
  classical
  intro edges A l k
  simp only [edges]
  rw [List.zipWith_rotate_distrib _ _ _ _ (List.length_rotate _ _).symm]
  congr 1
  rw [List.rotate_rotate, List.rotate_rotate, Nat.add_comm]

private theorem edges_ofFn :
    (by
      classical
      exact
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        ∀ {k : ℕ}, ∀ {A : Type}, ∀ (f : Fin (k + (3 : ℕ)) → A), edges (List.ofFn f) = List.ofFn
            fun (i : Fin (k + (3 : ℕ))) => (f i, f (i + (1 : Fin (k + (3 : ℕ))))) ) := by
  classical
  intro edges k A f
  apply List.ext_getElem
  · simp [edges]
  · intro i hi₁ hi₂
    have hi : i < k + 3 := by
      have htmp := hi₁
      simp [edges] at htmp
      omega
    have hzip : i < (List.zipWith Prod.mk (List.ofFn f) ((List.ofFn f).rotate 1)).length := by
      simp only [List.length_zipWith, List.length_ofFn, List.length_rotate]
      omega
    have hrot : i < ((List.ofFn f).rotate 1).length := by
      simp only [List.length_rotate, List.length_ofFn]
      exact hi
    change (List.zipWith Prod.mk (List.ofFn f) ((List.ofFn f).rotate 1))[i]'hzip =
      (List.ofFn fun i : Fin (k + 3) => (f i, f (i + 1)))[i]'hi₂
    rw [List.getElem_zipWith (h := hzip)]
    simp only [List.getElem_ofFn]
    rw [List.getElem_rotate (List.ofFn f) 1 i hrot]
    simp only [List.getElem_ofFn]
    congr 1
    apply congrArg f
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one, List.length_ofFn]

private theorem hsum_ofFn :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        (∀ {k : Nat}, ∀ {A : Type}, ∀ (f : Fin (k + 3) → A), edges (List.ofFn f) = List.ofFn (fun
            i : Fin (k + 3) => (f i, f (i + 1)))) → (
        let edgeWeight (x d : Real × Real) (L : List (Fin (n + 3))) : Nat :=
          ((edges L).map fun e => weight x d e.1 e.2).sum
        ∀ {k : ℕ}, ∀ (f : Fin (k + (3 : ℕ)) → Fin (n + (3 : ℕ))), ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), ∑
            i : Fin (k + (3 : ℕ)), weight x d (f i) (f (i + (1 : Fin (k + (3 : ℕ))))) =
            edgeWeight x d (List.ofFn f)) ) := by
  classical
  intro n p hit weight edges edges_ofFn edgeWeight k f x d
  rw [← List.sum_ofFn]
  simp only [edgeWeight, edges_ofFn, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

private theorem hweight_symm :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3 : ℕ))),
            weight x d i j = weight x d j i ) := by
  classical
  intro n p hit weight x d i j
  simp [weight, hit, segment_symm]

private theorem hleftCount :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        (∀ {k : Nat}, ∀ (P : Fin k → Prop), ∀ [DecidablePred P], Set.ncard {i : Fin k | P i} = ∑
            i : Fin k, if P i then 1 else 0) → (
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        let edgeWeight (x d : Real × Real) (L : List (Fin (n + 3))) : Nat :=
          ((edges L).map fun e => weight x d e.1 e.2).sum
        (∀ {k : Nat}, ∀ (f : Fin (k + 3) → Fin (n + 3)), ∀ (x : Real × Real), ∀ (d : Real ×
            Real), (∑ i : Fin (k + 3), weight x d (f i) (f (i + 1))) = edgeWeight x d (List.ofFn
            f)) → (∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), {i : Fin (C.leftParameter + (3 : ℕ)) | ∃ (t :
                ℝ), (0 :
            ℝ) < t ∧ x + t • d ∈ segment ℝ (C.left.vertex i) (C.left.vertex (i + (1 : Fin
            (C.leftParameter + (3 : ℕ)))))}.ncard = edgeWeight x d (a :: (C.u ++ [b])))) ) := by
  classical
  intro n p a b C hit weight cardPred edges edgeWeight hsum_ofFn x d
  rw [cardPred]
  have h := hsum_ofFn C.il x d
  rw [C.left_order] at h
  calc
    (∑ i : Fin (C.leftParameter + 3),
        if ∃ t : Real, 0 < t ∧ x + t • d ∈
            segment Real (C.left.vertex i) (C.left.vertex (i + 1)) then 1 else 0) =
        ∑ i : Fin (C.leftParameter + 3), weight x d (C.il i) (C.il (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [weight, hit, C.left_vertex]
    _ = edgeWeight x d (a :: (C.u ++ [b])) := h

private theorem hrightCount :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        (∀ {k : Nat}, ∀ (P : Fin k → Prop), ∀ [DecidablePred P], Set.ncard {i : Fin k | P i} = ∑
            i : Fin k, if P i then 1 else 0) → (
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        let edgeWeight (x d : Real × Real) (L : List (Fin (n + 3))) : Nat :=
          ((edges L).map fun e => weight x d e.1 e.2).sum
        (∀ {k : Nat}, ∀ (f : Fin (k + 3) → Fin (n + 3)), ∀ (x : Real × Real), ∀ (d : Real ×
            Real), (∑ i : Fin (k + 3), weight x d (f i) (f (i + 1))) = edgeWeight x d (List.ofFn
            f)) → (∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), {i : Fin (C.rightParameter + (3 : ℕ)) | ∃ (t :
                ℝ), (0 :
            ℝ) < t ∧ x + t • d ∈ segment ℝ (C.right.vertex i) (C.right.vertex (i + (1 : Fin
            (C.rightParameter + (3 : ℕ)))))}.ncard = edgeWeight x d (b :: (C.v ++ [a])))) ) := by
  classical
  intro n p a b C hit weight cardPred edges edgeWeight hsum_ofFn x d
  rw [cardPred]
  have h := hsum_ofFn C.ir x d
  rw [C.right_order] at h
  calc
    (∑ i : Fin (C.rightParameter + 3),
        if ∃ t : Real, 0 < t ∧ x + t • d ∈
            segment Real (C.right.vertex i) (C.right.vertex (i + 1)) then 1 else 0) =
        ∑ i : Fin (C.rightParameter + 3), weight x d (C.ir i) (C.ir (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [weight, hit, C.right_vertex]
    _ = edgeWeight x d (b :: (C.v ++ [a])) := h

private theorem hparentCount :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        (∀ {k : Nat}, ∀ (P : Fin k → Prop), ∀ [DecidablePred P], Set.ncard {i : Fin k | P i} = ∑
            i : Fin k, if P i then 1 else 0) → (
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        let edgeWeight (x d : Real × Real) (L : List (Fin (n + 3))) : Nat :=
          ((edges L).map fun e => weight x d e.1 e.2).sum
        (∀ {k : Nat}, ∀ (f : Fin (k + 3) → Fin (n + 3)), ∀ (x : Real × Real), ∀ (d : Real ×
            Real), (∑ i : Fin (k + 3), weight x d (f i) (f (i + 1))) = edgeWeight x d (List.ofFn
            f)) → (∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), {i : Fin (n + (3 : ℕ)) | ∃ (t : ℝ), (0 : ℝ) < t
            ∧ x + t • d ∈ segment ℝ (p.vertex i) (p.vertex (i + (1 : Fin (n + (3 : ℕ)))))}.ncard
            = edgeWeight x d (List.ofFn fun (i : Fin (n + (3 : ℕ))) => i))) ) := by
  classical
  intro n p hit weight cardPred edges edgeWeight hsum_ofFn x d
  rw [cardPred]
  have h := hsum_ofFn (fun i : Fin (n + 3) => i) x d
  calc
    (∑ i : Fin (n + 3),
        if ∃ t : Real, 0 < t ∧ x + t • d ∈
            segment Real (p.vertex i) (p.vertex (i + 1)) then 1 else 0) =
        ∑ i : Fin (n + 3), weight x d i (i + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    _ = edgeWeight x d (List.ofFn fun i : Fin (n + 3) => i) := h

private theorem hparentOrder :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        (∀ {A : Type}, ∀ (l : List A), ∀ (k : Nat), edges (l.rotate k) = (edges l).rotate k) → (
        let edgeWeight (x d : Real × Real) (L : List (Fin (n + 3))) : Nat :=
          ((edges L).map fun e => weight x d e.1 e.2).sum
        ∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), edgeWeight x d (List.ofFn fun (i : Fin (n + (3 : ℕ))) => i)
            = edgeWeight x d (a :: (C.u ++ b :: C.v))) ) := by
  classical
  intro n p a b C hit weight edges edges_rotate edgeWeight x d
  calc
    edgeWeight x d (List.ofFn (fun i : Fin (n + 3) => i)) =
        edgeWeight x d ((List.ofFn (fun i : Fin (n + 3) => i)).rotate C.rotation) := by
      unfold edgeWeight
      rw [edges_rotate, List.map_rotate]
      exact (List.Perm.sum_eq (List.rotate_perm _ _)).symm
    _ = edgeWeight x d (a :: (C.u ++ b :: C.v)) := by
      rw [C.parent_order]

private theorem hledger :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        (∀ {A : Type}, ∀ (a : A), ∀ (b : A), ∀ (u : List A), ∀ (v : List A), edges (a :: (u ++ b
            :: v)) = List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ List.zipWith Prod.mk (b :: v) (v
            ++ [a])) → ((∀ {A : Type}, ∀ (a : A), ∀ (b : A), ∀ (u : List A), edges (a :: (u ++
            [b])) = List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ [(b, a)]) → (
        let edgeWeight (x d : Real × Real) (L : List (Fin (n + 3))) : Nat :=
          ((edges L).map fun e => weight x d e.1 e.2).sum
        (∀ (x : Real × Real), ∀ (d : Real × Real), ∀ (i : Fin (n + 3)), ∀ (j : Fin (n + 3)),
            weight x d i j = weight x d j i) → (∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), edgeWeight x d (a
            :: (C.u ++ [b])) + edgeWeight x d (b :: (C.v ++ [a])) = edgeWeight x d (a :: (C.u ++
            b :: C.v)) + (2 : ℕ) * weight x d a b))) ) := by
  classical
  intro n p a b C hit weight edges edges_split edges_arc edgeWeight hweight_symm x d
  simp only [edgeWeight, edges_arc, edges_split, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]
  rw [hweight_symm x d b a]
  omega

private theorem hcount :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b),
        let hit (x d : Real × Real) (i j : Fin (n + 3)) : Prop :=
          ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex j)
        let weight (x d : Real × Real) (i j : Fin (n + 3)) : Nat :=
          if hit x d i j then 1 else 0
        let edges {A : Type} (l : List A) : List (A × A) :=
          List.zipWith Prod.mk l (l.rotate 1)
        let edgeWeight (x d : Real × Real) (L : List (Fin (n + 3))) : Nat :=
          ((edges L).map fun e => weight x d e.1 e.2).sum
        (∀ (x : Real × Real), ∀ (d : Real × Real), Set.ncard {i : Fin (C.leftParameter + 3) | ∃ t :
            Real, 0 < t ∧ x + t • d ∈ segment Real (C.left.vertex i) (C.left.vertex (i + 1))} =
            edgeWeight x d (a :: (C.u ++ [b]))) → ((∀ (x : Real × Real), ∀ (d : Real × Real),
            Set.ncard {i : Fin (C.rightParameter + 3) | ∃ t : Real, 0 < t ∧ x + t • d ∈ segment Real
            (C.right.vertex i) (C.right.vertex (i + 1))} = edgeWeight x d (b :: (C.v ++ [a]))) →
            ((∀ (x : Real × Real), ∀ (d : Real × Real), Set.ncard {i : Fin (n + 3) | ∃ t : Real,
            0 < t ∧ x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} = edgeWeight x d
            (List.ofFn (fun i : Fin (n + 3) => i))) → ((∀ (x : Real × Real), ∀ (d : Real × Real),
            edgeWeight x d (List.ofFn (fun i : Fin (n + 3) => i)) = edgeWeight x d (a :: (C.u ++
            b :: C.v))) → ((∀ (x : Real × Real), ∀ (d : Real × Real), edgeWeight x d (a :: (C.u
            ++ [b])) + edgeWeight x d (b :: (C.v ++ [a])) = edgeWeight x d (a :: (C.u ++ b ::
            C.v)) + 2 * weight x d a b) → (∀ (x : ℝ × ℝ), ∀ (d : ℝ × ℝ), {i : Fin
                (C.leftParameter + (3
            : ℕ)) | ∃ (t : ℝ), (0 : ℝ) < t ∧ x + t • d ∈ segment ℝ (C.left.vertex i)
            (C.left.vertex (i + (1 : Fin (C.leftParameter + (3 : ℕ)))))}.ncard + {i : Fin
                (C.rightParameter +
            (3 : ℕ)) | ∃ (t : ℝ), (0 : ℝ) < t ∧ x + t • d ∈ segment ℝ (C.right.vertex i)
            (C.right.vertex (i + (1 : Fin (C.rightParameter + (3 : ℕ)))))}.ncard = {i : Fin (n +
                (3 :
            ℕ)) | ∃ (t : ℝ), (0 : ℝ) < t ∧ x + t • d ∈ segment ℝ (p.vertex i) (p.vertex (i + (1 :
            Fin (n + (3 : ℕ)))))}.ncard + (2 : ℕ) * if ∃ (t : ℝ), (0 : ℝ) < t ∧ x + t • d ∈
            segment ℝ (p.vertex a) (p.vertex b) then (1 : ℕ) else (0 : ℕ)))))) ) := by
  classical
  intro n p a b C hit weight edges edgeWeight hleftCount hrightCount hparentCount hparentOrder
      hledger x d
  rw [hleftCount, hrightCount, hparentCount, hparentOrder]
  simpa [weight, hit, edgeWeight] using hledger x d

private theorem hcommon :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), ∀ x ∉ P3544T1BoundaryCarrier C.left, x
            ∉ P3544T1BoundaryCarrier C.right → ∃ (d : ℝ × ℝ), (∀ (i : Fin (n + (3 : ℕ))), d.1 *
            (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ (0 : ℝ)) ∧ (∀ (i : Fin (n + (3 :
            ℕ))), d.1 * (p.vertex (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).2 - d.2 * (p.vertex
            (i + (1 : Fin (n + (3 : ℕ)))) - p.vertex i).1 ≠ (0 : ℝ)) ∧ (∀ (i : Fin
                (C.leftParameter + (3
            : ℕ))), d.1 * (C.left.vertex i - x).2 - d.2 * (C.left.vertex i - x).1 ≠ (0 : ℝ)) ∧ (∀
            (i : Fin (C.leftParameter + (3 : ℕ))), d.1 * (C.left.vertex (i + (1 : Fin
                (C.leftParameter + (3 :
            ℕ)))) - C.left.vertex i).2 - d.2 * (C.left.vertex (i + (1 : Fin (C.leftParameter + (3 :
            ℕ)))) - C.left.vertex i).1 ≠ (0 : ℝ)) ∧ (∀ (i : Fin (C.rightParameter + (3 : ℕ))), d.1 *
            (C.right.vertex i - x).2 - d.2 * (C.right.vertex i - x).1 ≠ (0 : ℝ)) ∧ ∀ (i : Fin
            (C.rightParameter + (3 : ℕ))), d.1 * (C.right.vertex (i + (1 : Fin (C.rightParameter
                + (3 : ℕ)))) -
            C.right.vertex i).2 - d.2 * (C.right.vertex (i + (1 : Fin (C.rightParameter + (3 :
                ℕ)))) -
            C.right.vertex i).1 ≠ (0 : ℝ) ) := by
  classical
  intro n p a b C x hxL hxR
  have hxParent : x ∉ P3544T1BoundaryCarrier p := by
    have hxChildren : x ∉
        (P3544T1BoundaryCarrier C.left ∪ P3544T1BoundaryCarrier C.right) := by
      intro h
      rcases h with h | h
      · exact hxL h
      · exact hxR h
    have hxBoth : x ∉ (P3544T1BoundaryCarrier p ∪
        segment Real (p.vertex a) (p.vertex b)) := by
      rw [← C.carrier_union]
      exact hxChildren
    exact fun hx => hxBoth (Or.inl hx)
  have finSucc_ne {m : Nat} (i : Fin (m + 3)) : i + 1 ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_add, Fin.val_one] at hv
    by_cases hs : i.val + 1 < m + 3
    · rw [Nat.mod_eq_of_lt hs] at hv
      omega
    · have hi' : i.val + 1 = m + 3 := by omega
      rw [hi'] at hv
      simp at hv
      omega
  let Idx := (Fin (n + 3) × Bool) ⊕
    ((Fin (C.leftParameter + 3) × Bool) ⊕ (Fin (C.rightParameter + 3) × Bool))
  let vec : Idx → Real × Real := fun j =>
    match j with
    | Sum.inl (i, isVertex) =>
        if isVertex then p.vertex i - x else p.vertex (i + 1) - p.vertex i
    | Sum.inr (Sum.inl (i, isVertex)) =>
        if isVertex then C.left.vertex i - x else
          C.left.vertex (i + 1) - C.left.vertex i
    | Sum.inr (Sum.inr (i, isVertex)) =>
        if isVertex then C.right.vertex i - x else
          C.right.vertex (i + 1) - C.right.vertex i
  have hvec : ∀ j : Idx, vec j ≠ 0 := by
    intro j
    rcases j with ⟨i, isVertex⟩ | j
    · by_cases htag : isVertex
      · simp only [htag, ↓reduceIte, ne_eq, vec]
        intro hzero
        have hv : p.vertex i ∈ P3544T1BoundaryCarrier p := by
          exact Set.mem_iUnion.mpr ⟨i, left_mem_segment Real _ _⟩
        exact hxParent ((sub_eq_zero.mp hzero) ▸ hv)
      · simp only [htag, Bool.false_eq_true, ↓reduceIte, ne_eq, vec]
        intro hzero
        apply finSucc_ne i
        apply p.injective
        exact sub_eq_zero.mp hzero
    · rcases j with ⟨i, isVertex⟩ | ⟨i, isVertex⟩
      · by_cases htag : isVertex
        · simp only [htag, ↓reduceIte, ne_eq, vec]
          intro hzero
          have hv : C.left.vertex i ∈ P3544T1BoundaryCarrier C.left := by
            exact Set.mem_iUnion.mpr ⟨i, left_mem_segment Real _ _⟩
          exact hxL ((sub_eq_zero.mp hzero) ▸ hv)
        · simp only [htag, Bool.false_eq_true, ↓reduceIte, ne_eq, vec]
          intro hzero
          apply finSucc_ne i
          apply C.left.injective
          exact sub_eq_zero.mp hzero
      · by_cases htag : isVertex
        · simp only [htag, ↓reduceIte, ne_eq, vec]
          intro hzero
          have hv : C.right.vertex i ∈ P3544T1BoundaryCarrier C.right := by
            exact Set.mem_iUnion.mpr ⟨i, left_mem_segment Real _ _⟩
          exact hxR ((sub_eq_zero.mp hzero) ▸ hv)
        · simp only [htag, Bool.false_eq_true, ↓reduceIte, ne_eq, vec]
          intro hzero
          apply finSucc_ne i
          apply C.right.injective
          exact sub_eq_zero.mp hzero
  let bad : Finset Real := Finset.univ.image fun j : Idx => (vec j).2 / (vec j).1
  have hcard : (bad.card : ENat) < ENat.card Real := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.natCast_lt_top _
  obtain ⟨q, hq⟩ := Finset.exists_notMem_of_card_lt_enatCard hcard
  let d : Real × Real := (1, q)
  have hgeneric : ∀ j : Idx,
      d.1 * (vec j).2 - d.2 * (vec j).1 ≠ 0 := by
    intro j
    have hn := hvec j
    have hnot : q ≠ (vec j).2 / (vec j).1 := by
      intro he
      apply hq
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_univ _, by simp [he]⟩
    intro hz
    have hz' : (vec j).2 - q * (vec j).1 = 0 := by simpa [d] using hz
    by_cases hzero : (vec j).1 = 0
    · have hsecond : (vec j).2 = 0 := by simpa [hzero] using hz'
      exact hn (Prod.ext hzero hsecond)
    · apply hnot
      apply (eq_div_iff hzero).2
      nlinarith [hz']
  refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hgeneric (Sum.inl (i, true))
  · intro i
    exact hgeneric (Sum.inl (i, false))
  · intro i
    exact hgeneric (Sum.inr (Sum.inl (i, true)))
  · intro i
    exact hgeneric (Sum.inr (Sum.inl (i, false)))
  · intro i
    exact hgeneric (Sum.inr (Sum.inr (i, true)))
  · intro i
    exact hgeneric (Sum.inr (Sum.inr (i, false)))

private theorem hxParentAt401 :
    (by
      classical
      exact
        ∀ (n : Nat), ∀ (p : P3381T1PolygonBoundary n), ∀ (a : Fin (n + 3)), ∀ (b : Fin (n +
            3)), ∀ (C : P3650T1CyclicChildren p a b), ∀ (x : ℝ × ℝ), (x ∉
            P3544T1BoundaryCarrier C.left) → ((x ∉ P3544T1BoundaryCarrier C.right) → (x ∉
            P3544T1BoundaryCarrier p)) ) := by
  classical
  intro n p a b C x hxL hxR
  have hxChildren : x ∉
      (P3544T1BoundaryCarrier C.left ∪ P3544T1BoundaryCarrier C.right) := by
    intro h
    rcases h with h | h
    · exact hxL h
    · exact hxR h
  have hxBoth : x ∉ (P3544T1BoundaryCarrier p ∪
      segment Real (p.vertex a) (p.vertex b)) := by
    rw [← C.carrier_union]
    exact hxChildren
  exact fun hx => hxBoth (Or.inl hx)

end PolygonParityProof

theorem P3650T1ParitySum {n : Nat} (p : P3381T1PolygonBoundary n)
    (a b : Fin (n + 3)) (C : P3650T1CyclicChildren p a b) :
    (by
      classical
      exact
        (∀ x d : Real × Real,
          Set.ncard {i : Fin (C.leftParameter + 3) | ∃ t : Real, 0 < t ∧
            x + t • d ∈ segment Real (C.left.vertex i) (C.left.vertex (i + 1))} +
          Set.ncard {i : Fin (C.rightParameter + 3) | ∃ t : Real, 0 < t ∧
            x + t • d ∈ segment Real (C.right.vertex i) (C.right.vertex (i + 1))} =
          Set.ncard {i : Fin (n + 3) | ∃ t : Real, 0 < t ∧
            x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))} +
          2 * (if ∃ t : Real, 0 < t ∧
            x + t • d ∈ segment Real (p.vertex a) (p.vertex b) then 1 else 0)) ∧
        (∀ x, x ∉ P3544T1BoundaryCarrier C.left →
          x ∉ P3544T1BoundaryCarrier C.right →
          (x ∈ P3544T1RayParity p ↔
            (x ∈ P3544T1RayParity C.left ∧ x ∉ P3544T1RayParity C.right) ∨
            (x ∉ P3544T1RayParity C.left ∧ x ∈ P3544T1RayParity C.right)))) := by
-- BODY
  classical
  have cardPred {k : Nat} (P : Fin k → Prop) [DecidablePred P] := PolygonParityProof.cardPred (k
      := k) P
  have edges_cons {A : Type} (a : A) (l : List A) := PolygonParityProof.edges_cons (A := A) a l
  have path_split {A : Type} (a b z : A) (u v : List A) := PolygonParityProof.path_split (A := A)
      a b z u v
  have edges_split {A : Type} (a b : A) (u v : List A) := PolygonParityProof.edges_split
      edges_cons path_split (A := A) a b u v
  have edges_arc {A : Type} (a b : A) (u : List A) := PolygonParityProof.edges_arc edges_split (A
      := A) a b u
  have edges_rotate {A : Type} (l : List A) (k : Nat) := PolygonParityProof.edges_rotate (A := A)
      l k
  have edges_ofFn {k : Nat} {A : Type} (f : Fin (k + 3) → A) := PolygonParityProof.edges_ofFn (k
      := k) (A := A) f
  have hsum_ofFn {k : Nat} (f : Fin (k + 3) → Fin (n + 3)) (x d : Real × Real) :=
      PolygonParityProof.hsum_ofFn n p edges_ofFn (k := k) f x d
  have hweight_symm (x d : Real × Real) (i j : Fin (n + 3)) := PolygonParityProof.hweight_symm n
      p x d i j
  have hleftCount (x d : Real × Real) := PolygonParityProof.hleftCount n p a b C cardPred
      hsum_ofFn x d
  have hrightCount (x d : Real × Real) := PolygonParityProof.hrightCount n p a b C cardPred
      hsum_ofFn x d
  have hparentCount (x d : Real × Real) := PolygonParityProof.hparentCount n p cardPred hsum_ofFn
      x d
  have hparentOrder (x d : Real × Real) := PolygonParityProof.hparentOrder n p a b C edges_rotate
      x d
  have hledger (x d : Real × Real) := PolygonParityProof.hledger n p a b C edges_split edges_arc
      hweight_symm x d
  have hcount (x d : Real × Real) := PolygonParityProof.hcount n p a b C hleftCount hrightCount
      hparentCount hparentOrder hledger x d
  have hcommon (x : Real × Real)
      (hxL : x ∉ P3544T1BoundaryCarrier C.left)
      (hxR : x ∉ P3544T1BoundaryCarrier C.right) := PolygonParityProof.hcommon n p a b C x hxL hxR
  constructor
  · exact hcount
  · intro x hxL hxR
    obtain ⟨d, hpv, hpe, hlv, hle, hrv, hre⟩ := hcommon x hxL hxR
    have hxParent := PolygonParityProof.hxParentAt401 n p a b C x hxL hxR
    have hpar := (P3544T1LocalParity p).2.2.2.2.2.2.1 x d hxParent hpv hpe
    have hleft := (P3544T1LocalParity C.left).2.2.2.2.2.2.1 x d hxL hlv hle
    have hright := (P3544T1LocalParity C.right).2.2.2.2.2.2.1 x d hxR hrv hre
    have hsum := hcount x d
    by_cases hdiag : ∃ t : Real, 0 < t ∧
        x + t • d ∈ segment Real (p.vertex a) (p.vertex b)
    · simp [hdiag] at hsum
      rw [hpar, hleft, hright]
      omega
    · simp [hdiag] at hsum
      rw [hpar, hleft, hright]
      omega

end ApollonianSuperharmonic

end

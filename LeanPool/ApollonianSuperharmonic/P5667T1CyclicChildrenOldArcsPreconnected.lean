/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3650T1CyclicChildren
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology

-- [TABLET NODE: P5667T1CyclicChildrenOldArcsPreconnected]

/-!
# P5667T1CyclicChildrenOldArcsPreconnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OldArcs

private theorem chainUnionPreconnected {X : Type} [TopologicalSpace X] {m : Nat}
      (S : Fin (m + 1) → Set X) (hpre : ∀ i, IsPreconnected (S i))
      (hadj : ∀ i : Fin m, (S i.castSucc ∩ S i.succ).Nonempty) :
      IsPreconnected (⋃ i, S i) := by
  classical
  let R : Fin (m + 1) → Fin (m + 1) → Prop := fun i j => (S i ∩ S j).Nonempty
  have hsymm : ∀ i j, R i j → R j i := by
    intro i j h
    rcases h with ⟨x, hxi, hxj⟩
    exact ⟨x, hxj, hxi⟩
  have hreach : ∀ k : Nat, ∀ hk : k < m + 1,
      Relation.ReflTransGen R (0 : Fin (m + 1)) ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      have hk' : k < m + 1 := by omega
      have hprev := ih hk'
      have hi : k < m := by omega
      let i : Fin m := ⟨k, hi⟩
      let j : Fin (m + 1) := ⟨k + 1, hk⟩
      have hstep : R (⟨k, hk'⟩ : Fin (m + 1)) j := by
        simpa [R, i, j] using hadj i
      simpa [j] using Relation.ReflTransGen.tail hprev hstep
  have hreachSymm : ∀ i j, Relation.ReflTransGen R i j →
      Relation.ReflTransGen R j i := by
    intro i j hij
    induction hij with
    | refl => exact Relation.ReflTransGen.refl
    | @tail k l hkl hs ih =>
      exact (Relation.ReflTransGen.single (hsymm k l hs)).trans ih
  have hconn : ∀ i j : Fin (m + 1), Relation.ReflTransGen R i j := by
    intro i j
    have hi := hreach i.val i.isLt
    have hj := hreach j.val j.isLt
    exact (hreachSymm _ _ hi).trans (by simpa using hj)
  exact IsPreconnected.iUnion_of_reflTransGen hpre hconn

private theorem segmentSdiffPreconnected (a b : Real × Real)
      (z : Set (Real × Real))
      (hdisj : Disjoint (openSegment Real a b) z) :
      IsPreconnected (segment Real a b \ z) := by
  classical
  have hs : IsPreconnected (openSegment Real a b) :=
    (convex_openSegment (𝕜 := Real) a b).isPreconnected
  apply IsPreconnected.subset_closure hs
  · intro x hx
    exact ⟨openSegment_subset_segment Real a b hx,
      fun hxz => Set.disjoint_left.mp hdisj hx hxz⟩
  · intro x hx
    exact (segment_subset_closure_openSegment (𝕜 := Real) (x := a) (y := b)) hx.1

private theorem polygonOldArcPreconnected {m : Nat} (q : P3381T1PolygonBoundary m) :
      IsPreconnected (P3544T1BoundaryCarrier q \
        segment Real (q.vertex 0) (q.vertex (Fin.last (m + 2)))) := by
  classical
  have chainUnionPreconnected {X : Type} [TopologicalSpace X] {m : Nat}
      (S : Fin (m + 1) → Set X) (hpre : ∀ i, IsPreconnected (S i))
      (hadj : ∀ i : Fin m, (S i.castSucc ∩ S i.succ).Nonempty) :
      IsPreconnected (⋃ i, S i) := chainUnionPreconnected (X := X) (m := m) S hpre hadj
  have segmentSdiffPreconnected (a b : Real × Real)
      (z : Set (Real × Real))
      (hdisj : Disjoint (openSegment Real a b) z) :
      IsPreconnected (segment Real a b \ z) := segmentSdiffPreconnected a b z hdisj
  classical
  let last : Fin (m + 3) := Fin.last (m + 2)
  let e : Set (Real × Real) := segment Real (q.vertex last) (q.vertex 0)
  have hlast : last + 1 = (0 : Fin (m + 3)) := by
    apply Fin.ext
    simp [last]
  let edge : Fin (m + 2) → Set (Real × Real) := fun i =>
    segment Real (q.vertex i.castSucc) (q.vertex i.succ)
  have hnext (i : Fin (m + 2)) : i.castSucc + 1 = i.succ := by
    apply Fin.ext
    simp []
  have hcarrier : P3544T1BoundaryCarrier q = (⋃ i, edge i) ∪ e := by
    ext x
    simp only [P3544T1BoundaryCarrier, Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hx⟩
      cases i using Fin.lastCases with
      | last => right; simpa [e, last, hlast] using hx
      | cast j =>
        left
        refine ⟨j, ?_⟩
        simpa [edge, hnext] using hx
    · rintro (⟨i, hx⟩ | hx)
      · exact ⟨i.castSucc, by simpa [edge, hnext] using hx⟩
      · exact ⟨last, by simpa [e, last, hlast] using hx⟩
  have hopenDisjoint (i : Fin (m + 2)) :
      Disjoint (openSegment Real (q.vertex i.castSucc) (q.vertex i.succ)) e := by
    have hidx : i.castSucc ≠ last := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [last] at hv
      omega
    have hlaw := q.edge_intersection i.castSucc last hidx
    rw [hnext, hlast] at hlaw
    apply Set.disjoint_left.mpr
    intro x hxopen hxe
    have hxi : x ∈ segment Real (q.vertex i.castSucc) (q.vertex i.succ) :=
      openSegment_subset_segment Real _ _ hxopen
    have hpair : x ∈ segment Real (q.vertex i.castSucc) (q.vertex i.succ) ∩ e :=
      ⟨hxi, hxe⟩
    rw [hlaw] at hpair
    rcases hpair.1 with hxleft | hxright
    · have heq : q.vertex i.castSucc = q.vertex i.succ :=
        left_mem_openSegment_iff.mp (hxleft ▸ hxopen)
      have hi : i.castSucc = i.succ := q.injective heq
      have hv := congrArg Fin.val hi
      simp [Fin.succ, Fin.castSucc] at hv
    · have heq : q.vertex i.succ = q.vertex i.castSucc :=
        (right_mem_openSegment_iff.mp (hxright ▸ hxopen)).symm
      have hi : i.succ = i.castSucc := q.injective heq
      have hv := congrArg Fin.val hi
      simp [Fin.succ, Fin.castSucc] at hv
  have hpieces (i : Fin (m + 2)) : IsPreconnected (edge i \ e) :=
    segmentSdiffPreconnected (q.vertex i.castSucc) (q.vertex i.succ) e (hopenDisjoint i)
  have hadj (i : Fin (m + 1)) :
      ((edge i.castSucc \ e) ∩ (edge i.succ \ e)).Nonempty := by
    let j : Fin (m + 3) := i.succ.castSucc
    have hidx : j ≠ last := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [j, last] at hv
      omega
    have hnext' : j + 1 = ⟨i.val + 2, by omega⟩ := by
      apply Fin.ext
      have hj : j.val = i.val + 1 := by simp [j]
      have hlt : j.val + 1 < m + 3 := by rw [hj]; omega
      change (j.val + 1) % (m + 3) = i.val + 2
      rw [Nat.mod_eq_of_lt hlt, hj]
    have hlaw := q.edge_intersection j last hidx
    rw [hnext', hlast] at hlaw
    have hnot : q.vertex j ∉ e := by
      intro hx
      have hmem : q.vertex j ∈ segment Real (q.vertex j)
          (q.vertex ⟨i.val + 2, by omega⟩) ∩ e :=
        ⟨left_mem_segment Real _ _, hx⟩
      rw [hlaw] at hmem
      rcases hmem.2 with h | h
      · have heq : j = last := q.injective h
        have hv := congrArg Fin.val heq
        simp [j, last] at hv
        omega
      · have heq : j = 0 := q.injective h
        have hv := congrArg Fin.val heq
        simp [j] at hv
    refine ⟨q.vertex (i.succ.castSucc), ?_, ?_⟩
    · exact ⟨right_mem_segment Real _ _, hnot⟩
    · exact ⟨left_mem_segment Real _ _, hnot⟩
  have hpre : IsPreconnected (⋃ i : Fin (m + 2), edge i \ e) :=
    chainUnionPreconnected (fun i => edge i \ e) hpieces hadj
  have hdecomp : ((⋃ i : Fin (m + 2), edge i) ∪ e) \ e =
      ⋃ i : Fin (m + 2), edge i \ e := by
    ext x
    simp [Set.mem_iUnion]
  have heq : segment Real (q.vertex 0) (q.vertex last) = e :=
    segment_symm Real _ _
  rw [heq, hcarrier, hdecomp]
  exact hpre

end OldArcs

theorem P5667T1CyclicChildrenOldArcsPreconnected {n : Nat} (p : P3381T1PolygonBoundary n)
    (a b : Fin (n + 3)) (C : P3650T1CyclicChildren p a b) :
    IsPreconnected
      (P3544T1BoundaryCarrier C.left \ segment Real (p.vertex a) (p.vertex b)) ∧
    IsPreconnected
      (P3544T1BoundaryCarrier C.right \ segment Real (p.vertex a) (p.vertex b)) := by
-- BODY
  classical
  let e := segment Real (p.vertex a) (p.vertex b)
  let CL := P3544T1BoundaryCarrier C.left
  let CR := P3544T1BoundaryCarrier C.right
  have chainUnionPreconnected {X : Type} [TopologicalSpace X] {m : Nat}
      (S : Fin (m + 1) → Set X) (hpre : ∀ i, IsPreconnected (S i))
      (hadj : ∀ i : Fin m, (S i.castSucc ∩ S i.succ).Nonempty) :
      IsPreconnected (⋃ i, S i) := OldArcs.chainUnionPreconnected (X := X) (m := m) S hpre hadj
  have segmentSdiffPreconnected (a b : Real × Real)
      (z : Set (Real × Real))
      (hdisj : Disjoint (openSegment Real a b) z) :
      IsPreconnected (segment Real a b \ z) := OldArcs.segmentSdiffPreconnected a b z hdisj
  have polygonOldArcPreconnected {m : Nat} (q : P3381T1PolygonBoundary m) :
      IsPreconnected (P3544T1BoundaryCarrier q \
        segment Real (q.vertex 0) (q.vertex (Fin.last (m + 2)))) :=
            OldArcs.polygonOldArcPreconnected (m := m) q
  have leftArcPreconnected : IsPreconnected (CL \ e) := by
    have hfirst : C.il 0 = a := by
      have h := congrArg List.head? C.left_order
      simpa using h
    have hlast : C.il (Fin.last (C.left_n + 2)) = b := by
      have hlast? : (List.ofFn C.il).getLast? = some (C.il (Fin.last _)) := by
        rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
        rw [List.getLast_ofFn_succ]
      have h := congrArg List.getLast? C.left_order
      rw [hlast?] at h
      have hrhs : (a :: (C.u ++ [b])).getLast? = some b := by
        rw [show a :: (C.u ++ [b]) = [a] ++ (C.u ++ [b]) by simp]
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        simp
      rw [hrhs] at h
      exact Option.some.inj h
    have hvfirst : C.left.vertex 0 = p.vertex a := by
      rw [C.left_vertex]
      simpa using congrArg p.vertex hfirst
    have hvlast : C.left.vertex (Fin.last (C.left_n + 2)) = p.vertex b := by
      rw [C.left_vertex]
      simpa using congrArg p.vertex hlast
    have hq := polygonOldArcPreconnected C.left
    have heq : segment Real (C.left.vertex 0)
        (C.left.vertex (Fin.last (C.left_n + 2))) = e := by
      rw [hvfirst, hvlast]
    simpa [CL, e, heq] using hq
  have rightArcPreconnected : IsPreconnected (CR \ e) := by
    have hfirst : C.ir 0 = b := by
      have h := congrArg List.head? C.right_order
      simpa using h
    have hlast : C.ir (Fin.last (C.right_n + 2)) = a := by
      have hlast? : (List.ofFn C.ir).getLast? = some (C.ir (Fin.last _)) := by
        rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
        rw [List.getLast_ofFn_succ]
      have h := congrArg List.getLast? C.right_order
      rw [hlast?] at h
      have hrhs : (b :: (C.v ++ [a])).getLast? = some a := by
        rw [show b :: (C.v ++ [a]) = [b] ++ (C.v ++ [a]) by simp]
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        simp
      rw [hrhs] at h
      exact Option.some.inj h
    have hvfirst : C.right.vertex 0 = p.vertex b := by
      rw [C.right_vertex]
      simpa using congrArg p.vertex hfirst
    have hvlast : C.right.vertex (Fin.last (C.right_n + 2)) = p.vertex a := by
      rw [C.right_vertex]
      simpa using congrArg p.vertex hlast
    have hq := polygonOldArcPreconnected C.right
    have heq : segment Real (C.right.vertex 0)
        (C.right.vertex (Fin.last (C.right_n + 2))) = e := by
      rw [hvfirst, hvlast]
      exact segment_symm Real _ _
    simpa [CR, e, heq] using hq
  exact ⟨leftArcPreconnected, rightArcPreconnected⟩

end ApollonianSuperharmonic

end

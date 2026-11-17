/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3511T1SourceDissection
public import LeanPool.ApollonianSuperharmonic.P3511T1ConvexRealization
public import LeanPool.ApollonianSuperharmonic.P3555T2ParabolaHullFrontier
public import LeanPool.ApollonianSuperharmonic.P3555T2SavedDissectionGeometry

-- [TABLET NODE: P3511T1ConvexComparison]

/-!
# P3511T1ConvexComparison

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3511T1ConvexComparison {n : Nat}
    {p : P3381T1PolygonBoundary n} {X : Set (Real × Real)}
    (s : P3511T1SourceDissection p X) :
    ∃ K : Set (Real × Real), Nonempty (P3511T1ConvexRealization s.face K) := by
-- BODY
  let q : Fin (n + 3) → Real × Real := fun i => ((i.val : Real), (i.val : Real) ^ 2)
  have hq : ∀ i, q i = ((i.val : Real), (i.val : Real) ^ 2) := fun _ => rfl
  obtain ⟨hinjective, _, _⟩ := P3555T2ParabolaSupporting q hq
  obtain ⟨hedges, hconvex, hclosed, hbounded, hinterior, hfrontier⟩ :=
    P3555T2ParabolaHullFrontier q hq
  have hboundary : (List.ofFn (fun i : Fin (n + 3) => i)).Nodup :=
    List.nodup_ofFn_ofInjective Function.injective_id
  have hcyclic : ∃ k : Nat, (List.ofFn (fun i : Fin (n + 3) => i)).Sublist
      ((List.ofFn (fun i : Fin (n + 3) => i)).rotate k) := by
    exact ⟨0, by simp⟩
  obtain ⟨hfaces, _, hcover, hintersection, _⟩ :=
    P3555T2SavedDissectionGeometry q hq _ _ hboundary hcyclic s.dissection
  have hvertices : {i : Fin (n + 3) | i ∈ List.ofFn (fun j : Fin (n + 3) => j)} =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [hvertices, Set.image_univ] at hcover
  have hindexed : (⋃ (f : Fin 3 → Fin (n + 3)) (_ : f ∈ List.ofFn s.face),
      convexHull Real (Set.range (q ∘ f))) =
      ⋃ k, convexHull Real (Set.range (q ∘ s.face k)) := by
    ext z
    simp only [Set.mem_iUnion, List.mem_ofFn]
    constructor
    · rintro ⟨f, ⟨k, rfl⟩, hz⟩
      exact ⟨k, hz⟩
    · rintro ⟨k, hz⟩
      exact ⟨s.face k, ⟨k, rfl⟩, hz⟩
  refine ⟨convexHull Real (Set.range q), ⟨{
    target := q
    parabola := hq
    target_injective := hinjective
    target_edge_intersection := hedges
    target_nondegenerate := ?_
    target_cover := hcover.trans hindexed
    target_intersection := ?_
    target_hull := rfl
    target_convex := hconvex
    target_closed := hclosed
    target_bounded := hbounded
    target_interior := hinterior
    target_frontier := hfrontier }⟩⟩
  · intro k
    exact (hfaces (s.face k) (by simp)).2.2
  · intro k l
    exact hintersection (s.face k) (by simp) (s.face l) (by simp)

end ApollonianSuperharmonic

end

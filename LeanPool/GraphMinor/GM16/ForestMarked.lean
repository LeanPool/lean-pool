/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ForestPacking
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Order.Minimal

/-!
# Marked paths and vertex covers in a forest

For XVI (5.3), page 56, we apply the subtree packing theorem to paths
whose distinct ends are marked and whose internal vertices are unmarked.
Shortest paths to a specified set stop at their first meeting with it.
-/

@[expose] public section
namespace GraphMinor.GM16

open Set SimpleGraph
universe u

/-- A path with distinct marked ends and no marked internal vertex,
as in the family of paths in the proof of XVI (5.3), page 56. -/
structure MarkedPath {V : Type u} (G : SimpleGraph V) (Y : Set V) where
  /-- The initial marked vertex. -/
  start : V
  /-- The terminal marked vertex. -/
  finish : V
  start_mem : start ∈ Y
  finish_mem : finish ∈ Y
  ne : start ≠ finish
  /-- The graph path between the marked ends. -/
  path : G.Path start finish
  marked : ∀ z ∈ path.val.support, z ∈ Y → z = start ∨ z = finish

/-- A path from `a` to a set `X`, staying within a given set `U`, can
be chosen to meet `X` only at its last vertex. Choose one of minimum
length and shorten it at any earlier meeting. -/
theorem exists_path_first_hit {V : Type u} {G : SimpleGraph V} {a b : V}
    {X U : Set V} (p : G.Walk a b) (hb : b ∈ X)
    (hU : ∀ z ∈ p.support, z ∈ U) :
    ∃ x ∈ X, ∃ q : G.Path a x,
      (∀ z ∈ q.val.support, z ∈ U) ∧
      ∀ z ∈ q.val.support, z ∈ X → z = x := by
  classical
  let P : (Σ x, G.Path a x) → Prop := fun q =>
    q.1 ∈ X ∧ ∀ z ∈ q.2.val.support, z ∈ U
  obtain ⟨q, hq⟩ := exists_minimalFor_of_wellFoundedLT P
    (fun q => q.2.val.length)
    ⟨⟨b, p.toPath⟩, hb, fun z hz => hU z (p.support_toPath_subset_support hz)⟩
  refine ⟨q.1, hq.1.1, q.2, hq.1.2, ?_⟩
  intro z hz hzX
  by_contra hne
  let r : G.Path a z := ⟨q.2.val.takeUntil z hz, q.2.isPath.takeUntil hz⟩
  have hr : P ⟨z, r⟩ :=
    ⟨hzX, fun w hw => hq.1.2 w (q.2.val.support_takeUntil_subset_support hz hw)⟩
  have hlt : r.val.length < q.2.val.length := Walk.length_takeUntil_lt_length hz hne
  have hle := hq.2 hr hlt.le
  change q.2.val.length ≤ r.val.length at hle
  omega

/-- A walk between two different marked vertices contains a marked path.
This is also why a cover of marked paths meets every walk between
different marked vertices. -/
theorem exists_markedPath_in_walk {V : Type u} {G : SimpleGraph V} {Y : Set V}
    {a b : V} (p : G.Walk a b) (ha : a ∈ Y) (hb : b ∈ Y) (hne : a ≠ b) :
    ∃ q : MarkedPath G Y, ∀ z ∈ q.path.val.support, z ∈ p.support := by
  obtain ⟨z, ⟨hzY, hza⟩, q, hsub, hhit⟩ :=
    exists_path_first_hit (X := Y \ {a}) (U := {z | z ∈ p.support}) p
      ⟨hb, by simpa using hne.symm⟩ (fun _ h => h)
  refine ⟨⟨a, z, ha, hzY, ?_, q, ?_⟩, hsub⟩
  · exact fun h => hza (mem_singleton_iff.mpr h.symm)
  · intro w hw hwY
    by_cases hwa : w = a
    · exact Or.inl hwa
    · exact Or.inr (hhit w hw ⟨hwY, by simpa using hwa⟩)

/-- The vertices of a walk form a nonempty connected set. -/
theorem walk_isSubtreeSet {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : IsSubtreeSet G {z | z ∈ p.support} := by
  classical
  refine ⟨⟨a, p.start_mem_support⟩, ?_⟩
  intro x hx y hy
  let q := (p.takeUntil x hx).reverse.append (p.takeUntil y hy)
  refine ⟨q.toPath.val, q.toPath.isPath, ?_⟩
  intro z hz
  have hzq := q.support_toPath_subset_support hz
  change z ∈ ((p.takeUntil x hx).reverse.append (p.takeUntil y hy)).support at hzq
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hzq
  rcases hzq with hzq | hzq
  · exact p.support_takeUntil_subset_support hx hzq
  · exact p.support_takeUntil_subset_support hy hzq

/-- A cover of the marked paths meets every walk with distinct marked
ends. Apply the cover to a marked subpath of the walk. -/
theorem marked_cover_meets_walk {V : Type u} {G : SimpleGraph V} {Y X : Set V}
    (hX : ∀ q : MarkedPath G Y, ∃ x ∈ X, x ∈ q.path.val.support)
    {a b : V} (p : G.Walk a b) (ha : a ∈ Y) (hb : b ∈ Y) (hne : a ≠ b) :
    ∃ x ∈ X, x ∈ p.support := by
  obtain ⟨q, hsub⟩ := exists_markedPath_in_walk p ha hb hne
  obtain ⟨x, hxX, hxq⟩ := hX q
  exact ⟨x, hxX, hsub x hxq⟩

/-- A strict initial segment of a path that first meets `X` at its
last vertex avoids `X`. -/
theorem first_hit_prefix_avoids {V : Type u} [DecidableEq V] {G : SimpleGraph V} {X : Set V}
    {a x z : V} (p : G.Path a x)
    (hfirst : ∀ w ∈ p.val.support, w ∈ X → w = x)
    (hz : z ∈ p.val.support) (hzx : z ≠ x) :
    ∀ w ∈ (p.val.takeUntil z hz).support, w ∉ X := by
  intro w hw hwX
  have hwx := hfirst w (p.val.support_takeUntil_subset_support hz hw) hwX
  subst w
  exact Walk.endpoint_notMem_support_takeUntil p.isPath hz hzx.symm hw

/-- In the proof of XVI (5.3), a first-hit path from a marked vertex
to the cover has no marked internal vertex. An earlier marked vertex
would give a marked-to-marked walk avoiding the cover. -/
theorem first_hit_path_marked_only_at_ends
    {V : Type u} {G : SimpleGraph V} {Y X : Set V}
    (hX : ∀ q : MarkedPath G Y, ∃ x ∈ X, x ∈ q.path.val.support)
    {a x : V} (ha : a ∈ Y) (p : G.Path a x)
    (hfirst : ∀ w ∈ p.val.support, w ∈ X → w = x) :
    ∀ z ∈ p.val.support, z ∈ Y → z = a ∨ z = x := by
  classical
  intro z hz hzY
  by_cases hza : z = a
  · exact Or.inl hza
  · by_cases hzx : z = x
    · exact Or.inr hzx
    · obtain ⟨w, hwX, hw⟩ := marked_cover_meets_walk hX
        (p.val.takeUntil z hz) ha hzY (Ne.symm hza)
      exact False.elim (first_hit_prefix_avoids p hfirst hz hzx w hw hwX)

/-- The first-hit paths assigned to the same cover vertex meet only at
that vertex, as in XVI (5.3), page 56. A different meeting would join
their marked starts by a walk avoiding the cover. -/
theorem first_hit_paths_inter_eq
    {V : Type u} {G : SimpleGraph V} {Y X : Set V}
    (hX : ∀ q : MarkedPath G Y, ∃ x ∈ X, x ∈ q.path.val.support)
    {a b x : V} (ha : a ∈ Y) (hb : b ∈ Y) (hab : a ≠ b)
    (p : G.Path a x) (q : G.Path b x)
    (hp : ∀ w ∈ p.val.support, w ∈ X → w = x)
    (hq : ∀ w ∈ q.val.support, w ∈ X → w = x) :
    {z | z ∈ p.val.support} ∩ {z | z ∈ q.val.support} = {x} := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨hzp, hzq⟩
    apply mem_singleton_iff.mpr
    by_contra hzx
    let r := (p.val.takeUntil z hzp).append (q.val.takeUntil z hzq).reverse
    obtain ⟨w, hwX, hw⟩ := marked_cover_meets_walk hX r ha hb hab
    change w ∈ ((p.val.takeUntil z hzp).append (q.val.takeUntil z hzq).reverse).support at hw
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hw
    rcases hw with hw | hw
    · exact first_hit_prefix_avoids p hp hzp hzx w hw hwX
    · exact first_hit_prefix_avoids q hq hzq hzx w hw hwX
  · rintro z rfl
    exact ⟨p.val.end_mem_support, q.val.end_mem_support⟩

end GraphMinor.GM16

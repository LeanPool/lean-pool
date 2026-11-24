/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM09.Section2c
import Mathlib.Combinatorics.Pigeonhole

/-!
# Paths between marked vertices in XVI (5.3)

The assumption on components supplies a path from each marked vertex to
another marked vertex. Stopping at the first other marked vertex gives a
path with no marked internal vertex. The counting argument groups marked
vertices by the vertex at which their paths meet a finite set.
-/

public section
namespace GraphMinor.GM16

open Set Graph GraphMinor.Surface GraphMinor.GM09

universe u v

private theorem exists_walk_of_adj_reachable
    {α : Type u} {β : Type v} {G : Graph α β} {a b : α}
    (ha : a ∈ V(G)) (h : Relation.ReflTransGen G.Adj a b) :
    Nonempty (GraphWalk G a b) := by
  induction h with
  | refl => exact ⟨.nil ha⟩
  | @tail b c _ hadj ih =>
    obtain ⟨W⟩ := ih
    obtain ⟨e, he⟩ := hadj
    exact ⟨W.append (.cons he (.nil he.right_mem))⟩

/-- In the setting of XVI (5.3), page 56, each marked vertex has a path
to a different marked vertex with no marked internal vertex. Stop a path
to another marked vertex at its first meeting with `Y \ {y}`. -/
theorem exists_path_to_other_marked_vertex
    {α : Type u} {β : Type v} {G : Graph α β} {Y : Set α}
    (hYG : Y ⊆ V(G))
    (hcomp : ∀ y ∈ Y, ∃ y' ∈ Y, y' ≠ y ∧ Relation.ReflTransGen G.Adj y y')
    {y : α} (hy : y ∈ Y) :
    ∃ z ∈ Y, z ≠ y ∧ ∃ P : Graph α β,
      IsGraphPathWithEnds G P y z ∧ V(P) ∩ Y = {y, z} := by
  obtain ⟨y', hy', hne, hreach⟩ := hcomp y hy
  obtain ⟨W⟩ := exists_walk_of_adj_reachable (hYG hy) hreach
  obtain ⟨P, hP, _, _⟩ := exists_isGraphPathWithEnds_of_walk W
  obtain ⟨z, ⟨_, hzY, hzy⟩, Q, _, hQ, hhit, _⟩ :=
    hP.exists_first_hit (S := Y \ {y})
      ⟨y', hP.right_mem, hy', by simpa using hne⟩
  have hQG := hQ.mono hP.le
  have hzy' : z ≠ y := by simpa using hzy
  refine ⟨z, hzY, hzy', Q, hQG, subset_antisymm ?_ ?_⟩
  · rintro x ⟨hxQ, hxY⟩
    by_cases hxy : x = y
    · exact Or.inl hxy
    · have : x ∈ ({z} : Set α) :=
        hhit ▸ ⟨hxQ, hxY, by simpa using hxy⟩
      exact Or.inr this
  · rintro x (rfl | hx)
    · exact ⟨hQG.left_mem, hy⟩
    · have hxz : x = z := mem_singleton_iff.mp hx
      subst x
      exact ⟨hQG.right_mem, hzY⟩

/-- The pigeonhole step in XVI (5.3), page 56. If each marked vertex
is assigned a vertex of `X`, and `|Y| > τ * |X|`, then at least `τ + 1`
marked vertices have the same assigned vertex. -/
theorem exists_many_marked_vertices_at_one_vertex
    {α : Type u} {X Y : Set α} {τ : ℕ} {f : α → α}
    (hX : X.Finite) (hY : Y.Finite) (hf : ∀ y ∈ Y, f y ∈ X)
    (hcard : τ * X.ncard < Y.ncard) :
    ∃ x ∈ X, ∃ Y' ⊆ Y, τ + 1 ≤ Y'.ncard ∧ ∀ y ∈ Y', f y = x := by
  classical
  have hmaps : ∀ y ∈ hY.toFinset, f y ∈ hX.toFinset := by
    intro y hy
    exact hX.mem_toFinset.mpr (hf y (hY.mem_toFinset.mp hy))
  have hcount : hX.toFinset.card * τ < hY.toFinset.card := by
    rw [← ncard_eq_toFinset_card _ hX, ← ncard_eq_toFinset_card _ hY]
    simpa only [Nat.mul_comm] using hcard
  obtain ⟨x, hx, hlarge⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcount
  let A := hY.toFinset.filter (fun y => f y = x)
  refine ⟨x, hX.mem_toFinset.mp hx, (A : Set α), ?_, ?_, ?_⟩
  · intro y hy
    exact hY.mem_toFinset.mp (Finset.mem_filter.mp hy).1
  · rw [Set.ncard_coe_finset]
    exact hlarge
  · intro y hy
    exact (Finset.mem_filter.mp hy).2

/-- Graph Minors XVI, (5.3), the case `μ = 1`. A nonempty marked set
and the component hypothesis give a single path of the first outcome. -/
theorem theorem_5_3_one
    {α : Type u} {β : Type v} {G : Graph α β} {Y : Set α}
    (hY : Y.Finite) (hYG : Y ⊆ V(G))
    (hcomp : ∀ y ∈ Y, ∃ y' ∈ Y, y' ≠ y ∧ Relation.ReflTransGen G.Adj y y')
    (hcard : 0 < Y.ncard) :
    ∃ (P : Fin 1 → Graph α β) (s t : Fin 1 → α),
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      ∀ i, s i ∈ Y ∧ t i ∈ Y ∧ s i ≠ t i ∧
        IsGraphPathWithEnds G (P i) (s i) (t i) ∧ V(P i) ∩ Y = {s i, t i} := by
  obtain ⟨y, hy⟩ := (ncard_pos hY).mp hcard
  obtain ⟨z, hz, hzy, P, hP, hinter⟩ :=
    exists_path_to_other_marked_vertex hYG hcomp hy
  refine ⟨fun _ => P, fun _ => y, fun _ => z, ?_, ?_⟩
  · intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  · intro _
    exact ⟨hy, hz, hzy.symm, hP, hinter⟩

end GraphMinor.GM16

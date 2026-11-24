/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.Section5Degree
import LeanPool.GraphMinor.GM16.Section5Connections
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Unions of hair graphs in XVI (6.3)

Each truncated hair meets the embedded drawing at its own near end.
Thus a drawing vertex in their union has at most one neighbor. For the
second application of (5.3), joining all full hair paths to a connected
subgraph containing their far ends gives a connected graph.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
universe u v

/-- Adjacency in a union of subgraphs comes from one of its members. -/
theorem subgraphSUnion_adj_iff
    {α : Type u} {β : Type v} {G : Graph α β} {F : Set (Graph α β)}
    (hF : ∀ R ∈ F, R ≤ G) {x y : α} :
    (subgraphSUnion G F).Adj x y ↔ ∃ R ∈ F, R.Adj x y := by
  constructor
  · rintro ⟨e, he⟩
    have heE := he.edge_mem
    rw [edgeSet_subgraphSUnion hF] at heE
    obtain ⟨R, hR, heR⟩ := mem_iUnion₂.mp heE
    exact ⟨R, hR, e, ((hF R hR).isLink_iff heR).mpr (he.mono (subgraphSUnion_le hF))⟩
  · rintro ⟨R, hR, e, he⟩
    exact ⟨e, he.mono (le_subgraphSUnion hF hR)⟩

/-- The old-graph vertices in the union of truncated hairs have at most
one neighbor. Each belongs to just its own truncated hair. This is the
degree assertion in XVI (6.3), Claim (2), page 60. -/
theorem hair_union_old_neighbors_subsingleton
    {α : Type u} {β : Type v} {ι : Type*} {G H : Graph α β}
    {P Q : ι → Graph α β} {a b : ι → α}
    (hP : ∀ i, IsGraphPathWithEnds G (P i) (a i) (b i))
    (hQP : ∀ i, Q i ≤ P i) (hQH : ∀ i, V(Q i) ∩ V(H) = {a i})
    (ha : Function.Injective a) {x : α} (hx : x ∈ V(H)) :
    {z | (subgraphSUnion G (range Q)).Adj x z}.Subsingleton := by
  have hF : ∀ R ∈ range Q, R ≤ G := by
    rintro R ⟨i, rfl⟩
    exact (hQP i).trans (hP i).le
  intro z hz w hw
  obtain ⟨R, ⟨i, rfl⟩, e, he⟩ := (subgraphSUnion_adj_iff hF).mp hz
  obtain ⟨R, ⟨j, rfl⟩, f, hf⟩ := (subgraphSUnion_adj_iff hF).mp hw
  have hxi : x = a i := mem_singleton_iff.mp ((hQH i).subset ⟨he.left_mem, hx⟩)
  have hxj : x = a j := mem_singleton_iff.mp ((hQH j).subset ⟨hf.left_mem, hx⟩)
  have hij : i = j := ha (hxi.symm.trans hxj)
  subst j
  subst x
  exact path_start_neighbors_subsingleton (hP i) ⟨e, he.mono (hQP i)⟩ ⟨f, hf.mono (hQP i)⟩

/-- A graph path is connected. -/
theorem graphPath_isGraphConnected
    {α : Type u} {β : Type v} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : IsGraphConnected P := by
  refine ⟨⟨a, hP.left_mem⟩, ?_⟩
  intro x hx y hy
  obtain ⟨R, _, hR, _⟩ := hP.exists_subpath hx hy
  exact graphPath_exists_walk hR

/-- A union of connected subgraphs, each meeting a connected core,
is connected. This is the graph `G₂` in XVI (6.3), page 61. -/
theorem connected_union_of_core
    {α : Type u} {β : Type v} {ι : Type*} {G C : Graph α β} {P : ι → Graph α β}
    (hCG : C ≤ G) (hC : IsGraphConnected C)
    (hPG : ∀ i, P i ≤ G) (hP : ∀ i, IsGraphConnected (P i))
    (hmeet : ∀ i, (V(C) ∩ V(P i)).Nonempty) :
    IsGraphConnected (subgraphSUnion G ({C} ∪ range P)) := by
  let J := subgraphSUnion G ({C} ∪ range P)
  have hF : ∀ R ∈ ({C} : Set (Graph α β)) ∪ range P, R ≤ G := by
    rintro R (hR | ⟨i, rfl⟩)
    · exact (mem_singleton_iff.mp hR) ▸ hCG
    · exact hPG i
  have hCJ : C ≤ J := le_subgraphSUnion hF (Or.inl (mem_singleton C))
  have hPJ : ∀ i, P i ≤ J := fun i => le_subgraphSUnion hF (Or.inr ⟨i, rfl⟩)
  obtain ⟨b, hb⟩ := hC.1
  have htoB : ∀ a ∈ V(J), Nonempty (GraphWalk J a b) := by
    intro a ha
    obtain ⟨R, hR, haR⟩ := mem_iUnion₂.mp ha
    rcases hR with hR | ⟨i, rfl⟩
    · have hRC : R = C := mem_singleton_iff.mp hR
      subst R
      obtain ⟨W⟩ := hC.2 a haR b hb
      obtain ⟨W', _, _⟩ := exists_walk_up_of_le hCJ W
      exact ⟨W'⟩
    · obtain ⟨c, hcC, hcP⟩ := hmeet i
      obtain ⟨W₁⟩ := (hP i).2 a haR c hcP
      obtain ⟨W₂⟩ := hC.2 c hcC b hb
      obtain ⟨W₁', _, _⟩ := exists_walk_up_of_le (hPJ i) W₁
      obtain ⟨W₂', _, _⟩ := exists_walk_up_of_le hCJ W₂
      exact ⟨W₁'.append W₂'⟩
  refine ⟨⟨b, hCJ.vertexSet_mono hb⟩, ?_⟩
  intro a ha c hc
  obtain ⟨W₁⟩ := htoB a ha
  obtain ⟨W₂⟩ := htoB c hc
  exact ⟨W₁.append W₂.reverse⟩

end GraphMinor.GM16

/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card

/-!
# Breadth-first levels and spanning trees of graphs

For a simple graph `G` and finite vertex sets `X ⊆ Y` such that every vertex of `Y` can be
reached from `X` by a walk inside `Y`, the *level* `lev X Y v` of a vertex `v ∈ Y` is its
distance from `X` inside `Y` (`PlanarSeparator.lev`), computed by breadth-first search. Vertices
at level zero are those of `X`, every other vertex of `Y` has a neighbour in `Y` one level
lower, and the levels of adjacent vertices of `Y` differ by at most one.

From a breadth-first search inside a connected vertex set `C` from a root `r`, followed by a
breadth-first search from `C` in the whole (connected) graph, we obtain a spanning tree of `G`
whose restriction to `C` is a breadth-first tree of `C` (`PlanarSeparator.GTree.ofLevels`).
-/

@[expose] public section

namespace PlanarSeparator

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vertices of `Y` at distance at most `k` from `X` inside `Y`. -/
def ball (X Y : Finset V) : ℕ → Finset V
  | 0 => X
  | k + 1 => ball X Y k ∪ Y.filter fun v => ∃ u ∈ ball X Y k, G.Adj u v

variable {G} {X Y : Finset V}

lemma ball_mono {k l : ℕ} (h : k ≤ l) : ball G X Y k ⊆ ball G X Y l := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans subset_union_left

lemma ball_subset (hXY : X ⊆ Y) (k : ℕ) : ball G X Y k ⊆ Y := by
  induction k with
  | zero => exact hXY
  | succ k ih => exact union_subset ih (filter_subset _ _)

lemma mem_ball_succ {k : ℕ} {u v : V} (hu : u ∈ ball G X Y k) (hv : v ∈ Y) (huv : G.Adj u v) :
    v ∈ ball G X Y (k + 1) :=
  mem_union_right _ (mem_filter.2 ⟨hv, u, hu, huv⟩)

/-- Every vertex of `Y` reachable from `X` inside `Y` lies in some ball. -/
lemma exists_mem_ball {x y : V} (hx : x ∈ X)
    (h : Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ Y) x y) : ∃ k, y ∈ ball G X Y k := by
  induction h with
  | refl => exact ⟨0, hx⟩
  | tail _ hab ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, mem_ball_succ hk hab.2 hab.1⟩

variable (G X Y) in
/-- The level of a vertex: its distance from `X` inside `Y` (and `0` for unreachable vertices). -/
noncomputable def lev (v : V) : ℕ :=
  open Classical in if h : ∃ k, v ∈ ball G X Y k then Nat.find h else 0

lemma mem_ball_lev {v : V} (h : ∃ k, v ∈ ball G X Y k) : v ∈ ball G X Y (lev G X Y v) := by
  classical
  rw [lev, dite_eq_left h]
  exact Nat.find_spec h

lemma lev_le {v : V} {k : ℕ} (h : v ∈ ball G X Y k) : lev G X Y v ≤ k := by
  classical
  rw [lev, dite_eq_left ⟨k, h⟩]
  exact Nat.find_min' _ h

lemma mem_ball_iff {v : V} (h : ∃ k, v ∈ ball G X Y k) {k : ℕ} :
    v ∈ ball G X Y k ↔ lev G X Y v ≤ k :=
  ⟨lev_le, fun hk => ball_mono hk (mem_ball_lev h)⟩

/-- `X ⊆ Y`, and every vertex of `Y` is reachable from `X` inside `Y`. -/
def Reaches (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  X ⊆ Y ∧ ∀ y ∈ Y, ∃ x ∈ X, Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ Y) x y

lemma Reaches.exists_ball (h : Reaches G X Y) {y : V} (hy : y ∈ Y) : ∃ k, y ∈ ball G X Y k := by
  obtain ⟨x, hx, hxy⟩ := h.2 y hy
  exact exists_mem_ball hx hxy

lemma Reaches.lev_eq_zero_iff (h : Reaches G X Y) {v : V} (hv : v ∈ Y) :
    lev G X Y v = 0 ↔ v ∈ X := by
  rw [← Nat.le_zero, ← mem_ball_iff (h.exists_ball hv)]
  rfl

/-- The levels of adjacent vertices differ by at most one. -/
lemma Reaches.lev_le_lev_add_one (h : Reaches G X Y) {u v : V} (hu : u ∈ Y) (hv : v ∈ Y)
    (huv : G.Adj u v) : lev G X Y v ≤ lev G X Y u + 1 :=
  lev_le (mem_ball_succ (mem_ball_lev (h.exists_ball hu)) hv huv)

/-- Every vertex of `Y` outside `X` has a neighbour in `Y` one level lower. -/
lemma Reaches.exists_parent (h : Reaches G X Y) {v : V} (hv : v ∈ Y) (hv0 : v ∉ X) :
    ∃ u ∈ Y, G.Adj v u ∧ lev G X Y u + 1 = lev G X Y v := by
  have hb := h.exists_ball hv
  obtain ⟨k, hk⟩ : ∃ k, lev G X Y v = k + 1 := by
    rcases Nat.exists_eq_succ_of_ne_zero (fun h0 => hv0 ((h.lev_eq_zero_iff hv).1 h0)) with
      ⟨k, hk⟩
    exact ⟨k, hk⟩
  have hvk : v ∈ ball G X Y (k + 1) := (mem_ball_iff hb).2 hk.le
  have hvk' : v ∉ ball G X Y k := fun h' => by
    have := lev_le h'
    omega
  rcases mem_union.1 hvk with h' | h'
  · exact absurd h' hvk'
  obtain ⟨-, u, hu, huv⟩ := mem_filter.1 h'
  have huY : u ∈ Y := ball_subset h.1 k hu
  refine ⟨u, huY, huv.symm, ?_⟩
  have h1 := lev_le hu
  by_contra hne
  have h2 : lev G X Y u + 1 ≤ k := by omega
  exact hvk' (ball_mono h2 (mem_ball_succ (mem_ball_lev ⟨k, hu⟩) hv huv))

/-- A spanning tree of a graph, given by the parents of the vertices other than the root; the
height decreases from a vertex to its parent. -/
structure GTree (G : SimpleGraph V) where
  /-- The root. -/
  root : V
  /-- The parent of a vertex. -/
  parent : V → V
  /-- A height function decreasing towards the root. -/
  height : V → ℕ
  adj : ∀ v, v ≠ root → G.Adj v (parent v)
  height_lt : ∀ v, v ≠ root → height (parent v) < height v

namespace GTree

variable [Fintype V] {C : Finset V} {r : V} (hC : Reaches G {r} C) (hG : Reaches G C univ)

/-- The spanning tree obtained from a breadth-first search inside `C` from `r`, continued by a
breadth-first search from `C` in the whole graph. -/
noncomputable def ofLevels : GTree G where
  root := r
  parent v :=
    if h : v ∈ C ∧ v ≠ r then (hC.exists_parent h.1 (by simpa using h.2)).choose
    else if h' : v ∉ C then (hG.exists_parent (mem_univ v) h').choose else v
  height v := if v ∈ C then lev G {r} C v else C.sup (lev G {r} C) + 1 + lev G C univ v
  adj v hv := by
    by_cases h : v ∈ C
    · rw [dite_eq_left ⟨h, hv⟩]
      exact (hC.exists_parent h (by simpa using hv)).choose_spec.2.1
    · rw [dite_eq_right (fun h' => h h'.1), dite_eq_left h]
      exact (hG.exists_parent (mem_univ v) h).choose_spec.2.1
  height_lt v hv := by
    by_cases h : v ∈ C
    · rw [dite_eq_left ⟨h, hv⟩]
      obtain ⟨h1, -, h3⟩ := (hC.exists_parent h (by simpa using hv)).choose_spec
      rw [ite_eq_left h1, ite_eq_left h]
      omega
    · rw [dite_eq_right (fun h' => h h'.1), dite_eq_left h]
      obtain ⟨-, -, h3⟩ := (hG.exists_parent (mem_univ v) h).choose_spec
      rw [ite_eq_right h]
      split_ifs with h4
      · have := le_sup (f := lev G {r} C) h4
        omega
      · omega

lemma ofLevels_root : (ofLevels hC hG).root = r := rfl

/-- Inside `C` the tree is a breadth-first tree: the parent of a vertex of `C` other than the
root lies in `C`, one level lower. -/
lemma ofLevels_parent {v : V} (hv : v ∈ C) (hvr : v ≠ r) :
    (ofLevels hC hG).parent v ∈ C ∧
      lev G {r} C ((ofLevels hC hG).parent v) + 1 = lev G {r} C v := by
  have hp : (ofLevels hC hG).parent v = (hC.exists_parent hv (by simpa using hvr)).choose :=
    dite_eq_left ⟨hv, hvr⟩
  rw [hp]
  obtain ⟨h1, -, h3⟩ := (hC.exists_parent hv (by simpa using hvr)).choose_spec
  exact ⟨h1, h3⟩

end GTree

end PlanarSeparator

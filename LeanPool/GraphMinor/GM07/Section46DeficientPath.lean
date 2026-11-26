/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Forest

/-!
# The maximal path of VII (4.6), pages 228-229

This is the graph part of the argument. Take a forest with a set `B` of vertices, such that each
vertex outside `B` that has an edge has a second edge. A longest path must then have both
of its ends in `B`. A shortest path with distinct ends in `B` has no other vertex in `B`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.Surface.GraphWalk

universe u v

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- A simple walk has at most as many edges as the graph has vertices. -/
theorem IsSimple.length_le {x y : α} {W : GraphWalk G x y} (hW : W.IsSimple)
    (hV : G.vertexSet.Finite) : W.length ≤ G.vertexSet.ncard := by
  classical
  have hlen := GM11.length_support W
  have hcard : W.support.toFinset.card = W.support.length := List.toFinset_card_of_nodup hW
  have hsub : (↑W.support.toFinset : Set α) ⊆ G.vertexSet := by
    intro z hz
    exact W.mem_vertexSet_of_mem_support (List.mem_toFinset.mp hz)
  have := Set.ncard_le_ncard hsub hV
  rw [Set.ncard_coe_finset] at this
  unfold GraphWalk.length at hlen ⊢
  omega

/-- An end of a longest path has one edge, or else the path can be made longer or closed up. -/
private theorem longest_start_mem {B : Set α} (hforest : Surface.IsGraphForest G)
    (hdeg : ∀ u ∈ G.vertexSet, u ∉ B → ∀ e x, G.IsLink e u x → ∃ e' x', e' ≠ e ∧ G.IsLink e' u x')
    {x y : α} {W : GraphWalk G x y} (hW : W.IsSimple) (hpos : 0 < W.length)
    (hmax : ∀ (a b : α) (X : GraphWalk G a b), X.IsSimple → X.length ≤ W.length) : x ∈ B := by
  by_contra hx
  cases W with
  | nil h => simp at hpos
  | @cons _ m _ e hl r =>
    obtain ⟨e', x', hne, hl'⟩ := hdeg x hl.left_mem hx e m hl
    by_cases hmem : x' ∈ (GraphWalk.cons hl r).support
    · obtain ⟨W₁, W₂, heq⟩ := (GraphWalk.cons hl r).exists_append_of_mem hmem
      have hs₁ : W₁.IsSimple := by
        have h := hW
        unfold GraphWalk.IsSimple at h ⊢
        rw [heq, support_append] at h
        exact (List.nodup_append.mp h).1
      have hne' : e' ∉ W₁.edges := by
        intro hin
        have he : e' ∈ (GraphWalk.cons hl r).edges := by
          rw [heq, edges_append]
          exact List.mem_append_left _ hin
        rcases List.mem_cons.mp he with h | h
        · exact hne h
        · exact (List.nodup_cons.mp hW).1 (r.left_mem_support_of_mem_edges h hl')
      have hclosed : (GraphWalk.cons hl'.symm W₁).IsSimpleClosed :=
        ⟨by simpa using (show W₁.support.Nodup from hs₁), by simpa using ⟨hne', hs₁.edges_nodup⟩⟩
      have := hforest _ _ hclosed
      simp at this
    · have hs : (GraphWalk.cons hl'.symm (GraphWalk.cons hl r)).IsSimple :=
        List.nodup_cons.mpr ⟨hmem, hW⟩
      have := hmax _ _ _ hs
      simp at this

/-- A shortest walk between distinct points of `B` has no other point in `B`. -/
private theorem exists_shortest_between {B : Set α} {x y : α} (W : GraphWalk G x y)
    (hW : W.IsSimple) (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) :
    ∃ (a b : α) (X : GraphWalk G a b), a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ X.IsSimple ∧
      ∀ z ∈ X.support, z ∈ B → z = a ∨ z = b := by
  classical
  have hex : ∃ n, ∃ (a b : α) (X : GraphWalk G a b), a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ X.IsSimple ∧
      X.length = n := ⟨_, x, y, W, hx, hy, hxy, hW, rfl⟩
  obtain ⟨a, b, X, ha, hb, hab, hX, hn⟩ := Nat.find_spec hex
  refine ⟨a, b, X, ha, hb, hab, hX, fun z hz hzB => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨X₁, X₂, heq⟩ := X.exists_append_of_mem hz
  have hs₁ : X₁.IsSimple := by
    have h := hX
    unfold GraphWalk.IsSimple at h ⊢
    rw [heq, support_append] at h
    exact (List.nodup_append.mp h).1
  have hlen : X₁.length < X.length := by
    rw [heq, length_append]
    have : 0 < X₂.length := Nat.pos_of_ne_zero fun h =>
      hne.2 (eq_of_length_eq_zero h)
    omega
  exact Nat.find_min hex (hn ▸ hlen) ⟨a, z, X₁, ha, hzB, hne.1.symm, hs₁, rfl⟩

/-- The maximal path argument of VII (4.6), pages 228-229. A forest with an edge, in which each
vertex outside `B` that has an edge has a second edge, contains a path between two points of `B`
with no other vertex in `B`. -/
theorem exists_path_between_of_forest {B : Set α} (hV : G.vertexSet.Finite)
    (hforest : Surface.IsGraphForest G)
    (hdeg : ∀ u ∈ G.vertexSet, u ∉ B → ∀ e x, G.IsLink e u x → ∃ e' x', e' ≠ e ∧ G.IsLink e' u x')
    {e : β} {p q : α} (hl : G.IsLink e p q) :
    ∃ (a b : α) (X : GraphWalk G a b), a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ X.IsSimple ∧
      ∀ z ∈ X.support, z ∈ B → z = a ∨ z = b := by
  classical
  have hpq : p ≠ q := by
    rintro rfl
    have hclosed : (GraphWalk.cons hl (GraphWalk.nil hl.left_mem)).IsSimpleClosed :=
      ⟨by simp, by simp⟩
    have := hforest _ _ hclosed
    simp at this
  let P : ℕ → Prop := fun n => ∃ (a b : α) (X : GraphWalk G a b), X.IsSimple ∧ X.length = n
  have hP : P 1 := ⟨p, q, GraphWalk.cons hl (GraphWalk.nil hl.right_mem),
    List.nodup_cons.mpr ⟨by simpa using hpq, by simp⟩, by simp⟩
  have hbound : ∀ n, P n → n ≤ G.vertexSet.ncard := by
    rintro n ⟨a, b, X, hX, rfl⟩
    exact IsSimple.length_le hX hV
  have hne : 1 ≤ G.vertexSet.ncard := hbound 1 hP
  have hgr := Nat.findGreatest_spec hne hP
  obtain ⟨x, y, W, hW, hn⟩ := hgr
  have hge : 1 ≤ W.length := by
    rw [hn]
    exact Nat.le_findGreatest hne hP
  have hmax : ∀ (a b : α) (X : GraphWalk G a b), X.IsSimple → X.length ≤ W.length := by
    intro a b X hX
    rw [hn]
    exact Nat.le_findGreatest (hbound _ ⟨a, b, X, hX, rfl⟩) ⟨a, b, X, hX, rfl⟩
  have hx : x ∈ B := longest_start_mem hforest hdeg hW hge hmax
  have hy : y ∈ B := longest_start_mem hforest hdeg (W := W.reverse) hW.reverse
    (by rwa [length_reverse]) (by rw [length_reverse]; exact hmax)
  have hxy : x ≠ y := by
    rintro rfl
    have := hW.length_eq_zero
    omega
  exact exists_shortest_between W hW hx hy hxy

end GraphMinor.GM07

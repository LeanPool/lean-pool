/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Patterns.CutGraft

/-!
# Tree surgery at a non-root DFS position

Combinatorial helpers for the proofs of Lemmas `lem:S_rary`(ii), `lem:C_rary` and `lem:C_lh`
(source lines 2670–2753, 2768–2792, 3190–3236; inventory P19, P21, P25), in which a fringe
subtree `T_{u_{ℓ+1}}` at a non-root DFS position `ℓ ≥ 1` is cut out and replaced.

A non-root DFS position of `node ts` lies in exactly one child: writing `ts = pre ++ t :: post`,
the positions of the vertices of `t` are `forestSize pre + q + 1` with `q < |t|`, where
`forestSize pre` is the total size of the preceding children (the DFS bookkeeping of the paper).

* `exists_append_of_lt_forestSize`: every position `i < forestSize ts` of the forest `ts` is of
  the form `forestSize pre + q` with `ts = pre ++ t :: post`, `q < |t|`;
* `fringeAt_node_append`: at that position the fringe subtree of `node ts` is `fringeAt t q`;
* `replaceAt_node_append`: replacing it by `S` replaces the child `t` by `replaceAt t q S`;
* `sum_range_forestSize`: a sum over the positions of a forest splits over its trees;
* `graft_cut_eq_replaceAt`: `Cut_ℓ(T)[S]` is `T` with `T_{u_{ℓ+1}}` replaced by `S`.
-/

@[expose] public section

namespace PoissonDeclumping.PlaneTree

open Lukasiewicz

/-- The total number of vertices `∑_i |t_i|` of a forest `(t_1, …, t_m)`. -/
def forestSize (ts : List PlaneTree) : ℕ := (ts.map vertexCount).sum

@[simp] theorem forestSize_nil : forestSize [] = 0 := rfl

@[simp] theorem forestSize_cons (t : PlaneTree) (ts : List PlaneTree) :
    forestSize (t :: ts) = t.vertexCount + forestSize ts := by
  simp [forestSize]

theorem forestSize_append (ts us : List PlaneTree) :
    forestSize (ts ++ us) = forestSize ts + forestSize us := by
  simp [forestSize]

theorem vertexCount_node_eq (ts : List PlaneTree) :
    (node ts).vertexCount = forestSize ts + 1 := vertexCount_node ts

theorem length_flatMap_fringeTrees (ts : List PlaneTree) :
    (ts.flatMap fringeTrees).length = forestSize ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.flatMap_cons, ih, vertexCount]

theorem length_forestSeq (ts : List PlaneTree) : (forestSeq ts).length = forestSize ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [forestSeq_cons, ih, length_dfsSeq]

theorem forestSeq_append' (ts us : List PlaneTree) :
    forestSeq (ts ++ us) = forestSeq ts ++ forestSeq us := by
  simp [forestSeq]

/-- The fringe subtree at DFS index `i` fits inside `T`: `i + |T_{u_{i+1}}| ≤ |T|`. -/
theorem add_vertexCount_fringeAt_le {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) :
    i + (fringeAt T i).vertexCount ≤ T.vertexCount := by
  have := congrArg List.length (dfsSeq_eq_append_fringeAt T h)
  simp only [List.length_append, length_dfsSeq, length_take_dfsSeq h] at this
  omega

/-- Every position of a forest lies in exactly one of its trees. -/
theorem exists_append_of_lt_forestSize : ∀ (ts : List PlaneTree) (i : ℕ), i < forestSize ts →
    ∃ pre t post q, ts = pre ++ t :: post ∧ q < t.vertexCount ∧ i = forestSize pre + q
  | [], i, h => by simp at h
  | t :: ts, i, h => by
    by_cases hi : i < t.vertexCount
    · exact ⟨[], t, ts, i, rfl, hi, by simp⟩
    · obtain ⟨pre, t', post, q, h1, h2, h3⟩ :=
        exists_append_of_lt_forestSize ts (i - t.vertexCount) (by simp at h; omega)
      exact ⟨t :: pre, t', post, q, by simp [h1], h2, by simp; omega⟩

/-- At the DFS position `forestSize pre + q + 1` of `node (pre ++ t :: post)` sits the vertex of
DFS index `q` of the child `t`. -/
theorem fringeAt_node_append (pre post : List PlaneTree) (t : PlaneTree) {q : ℕ}
    (hq : q < t.vertexCount) :
    fringeAt (node (pre ++ t :: post)) (forestSize pre + q + 1) = fringeAt t q := by
  rw [fringeAt, fringeAt, fringeTrees_node, List.getD_cons_succ, List.flatMap_append,
    List.flatMap_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_flatMap_fringeTrees]; omega),
    length_flatMap_fringeTrees, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [← vertexCount]; exact hq)]

/-- Replacing the fringe subtree at the DFS position `forestSize pre + q + 1` of
`node (pre ++ t :: post)` replaces the child `t` by `replaceAt t q S`. -/
theorem replaceAt_node_append (pre post : List PlaneTree) (t : PlaneTree) {q : ℕ}
    (hq : q < t.vertexCount) (S : PlaneTree) :
    replaceAt (node (pre ++ t :: post)) (forestSize pre + q + 1) S =
      node (pre ++ replaceAt t q S :: post) := by
  have hT : forestSize pre + q + 1 < (node (pre ++ t :: post)).vertexCount := by
    rw [vertexCount_node_eq, forestSize_append, forestSize_cons]
    omega
  have hle := add_vertexCount_fringeAt_le hq
  have hpre := length_forestSeq pre
  have hdt := length_dfsSeq t
  apply dfsSeq_injective
  rw [dfsSeq_replaceAt hT, fringeAt_node_append pre post t hq, dfsSeq_node, dfsSeq_node,
    forestSeq_append', forestSeq_append', forestSeq_cons, forestSeq_cons, dfsSeq_replaceAt hq]
  simp only [List.length_append, List.length_cons]
  rw [show forestSize pre + q + 1 + (fringeAt t q).vertexCount =
      (forestSize pre + (q + (fringeAt t q).vertexCount)) + 1 by omega,
    List.take_succ_cons, List.drop_succ_cons, ← hpre, List.take_append, List.drop_append,
    List.take_of_length_le (by omega), List.drop_of_length_le (by omega),
    Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
    List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  simp only [List.nil_append, List.append_assoc, List.cons_append]

/-- A sum over the positions `0 ≤ i < forestSize ts` of a forest splits into the sums over the
positions of its trees. -/
theorem sum_range_forestSize {M : Type*} [AddCommMonoid M] :
    ∀ (ts : List PlaneTree) (f : ℕ → M) (g : PlaneTree → ℕ → M),
      (∀ pre t post q, ts = pre ++ t :: post → q < t.vertexCount →
        f (forestSize pre + q) = g t q) →
      ∑ q ∈ Finset.range (forestSize ts), f q =
        (ts.map fun t => ∑ q ∈ Finset.range t.vertexCount, g t q).sum
  | [], f, g, _ => by simp
  | t :: ts, f, g, h => by
    rw [forestSize_cons, Finset.sum_range_add, List.map_cons, List.sum_cons]
    congr 1
    · refine Finset.sum_congr rfl fun q hq => ?_
      simpa using h [] t ts q rfl (Finset.mem_range.1 hq)
    · refine sum_range_forestSize ts (fun q => f (t.vertexCount + q)) g
        fun pre t' post q h1 h2 => ?_
      have := h (t :: pre) t' post q (by simp [h1]) h2
      simpa [add_assoc] using this

/-- Replacement below the root preserves a declumped mark `Ĝ = 1{k_∅ ∈ B} 1{∃ child c, G(T_c)}`
as soon as replacement inside the witnessing child preserves `G`: the root degree is unchanged,
and a witnessing child either does not contain the replaced vertex or is modified only inside.
(This is the common step of the proofs of Lemmas `lem:C_rary` and `lem:C_lh`.) -/
theorem declumpedMark_replaceAt {B : Set ℕ} {G : PlaneTree → Prop} {T : PlaneTree} {ℓ : ℕ}
    (S : PlaneTree) (hT : declumpedMark B G T) (hℓ : 1 ≤ ℓ) (hℓT : ℓ < T.vertexCount)
    (hG : ∀ (t : PlaneTree) (q : ℕ), G t → q < t.vertexCount → fringeAt t q = fringeAt T ℓ →
      G (replaceAt t q S)) :
    declumpedMark B G (replaceAt T ℓ S) := by
  obtain ⟨ts⟩ := T
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  rw [vertexCount_node_eq] at hℓT
  obtain ⟨pre, t, post, q, rfl, hq, rfl⟩ := exists_append_of_lt_forestSize ts ℓ (by omega)
  rw [fringeAt_node_append pre post t hq] at hG
  rw [replaceAt_node_append pre post t hq]
  obtain ⟨hB, U, hU, hGU⟩ := hT
  refine ⟨by simpa using hB, ?_⟩
  simp only [children_node] at hU ⊢
  rcases List.mem_append.1 hU with hU | hU
  · exact ⟨U, List.mem_append_left _ hU, hGU⟩
  rcases List.mem_cons.1 hU with rfl | hU
  · exact ⟨replaceAt U q S, by simp, hG U q hGU hq rfl⟩
  · exact ⟨U, by simp [hU], hGU⟩

/-- `Cut_ℓ(T)[S]` is the tree `T` with its fringe subtree `T_{u_{ℓ+1}}` replaced by `S`. -/
theorem graft_cut_eq_replaceAt {ℓ : ℕ} {T : PlaneTree} (h : ℓ < T.vertexCount)
    (S : PlaneTree) : (cut ℓ T).graft S = replaceAt T ℓ S := by
  rw [MarkedTree.graft, cut_tree h, cut_pos h, replaceAt_replaceAt h]

end PoissonDeclumping.PlaneTree

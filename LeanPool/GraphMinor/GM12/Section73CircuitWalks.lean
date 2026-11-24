/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks

/-!
# Reading a circuit at a chosen vertex

For XII (7.3), Claim (1), page 262, read the new circuit from the
merged hub. Removing its first and last edge leaves a simple path.
The elementary walk lemmas here rotate a simple closed walk,
separate its final edge, and close a simple path through a new
vertex. They also cover a path with no edges, which occurs for a
two-edge circuit with parallel edges.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph

/-- Rotate a simple closed walk to any vertex of its support,
preserving its simplicity, length, and the sets of vertices and
edges. This reads the circuit at the hub in XII (7.3), Claim (1). -/
theorem exists_simpleClosed_walk_at_vertex
    {α β : Type*} {G : Graph α β} {a v : α} (W : GraphWalk G a a)
    (hW : W.IsSimpleClosed) (hv : v ∈ W.support) :
    ∃ V : GraphWalk G v v, V.IsSimpleClosed ∧ V.length = W.length ∧
      (∀ x, x ∈ V.support ↔ x ∈ W.support) ∧
      (∀ e, e ∈ V.edges ↔ e ∈ W.edges) := by
  obtain ⟨P, Q, rfl⟩ := W.exists_append_of_mem hv
  refine ⟨Q.append P, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h₁ : (P.append Q).support.tail = P.support.tail ++ Q.support.tail := by
      rw [GraphWalk.support_append, P.support_eq_cons]
      simp
    have h₂ : (Q.append P).support.tail = Q.support.tail ++ P.support.tail := by
      rw [GraphWalk.support_append, Q.support_eq_cons]
      simp
    rw [h₂]
    have hnd := hW.1
    rw [h₁] at hnd
    exact List.perm_append_comm.nodup_iff.mp hnd
  · rw [GraphWalk.edges_append]
    have hnd := hW.2
    rw [GraphWalk.edges_append] at hnd
    exact List.perm_append_comm.nodup_iff.mp hnd
  · rw [GraphWalk.length_append, GraphWalk.length_append]
    exact Nat.add_comm _ _
  · intro x
    rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append, or_comm]
  · intro e
    rw [GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append, or_comm]

/-- Separate the final edge of a positive-length walk. This
exposes the two spokes at the hub in XII (7.3), Claim (1). -/
theorem exists_walk_last_edge
    {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b) (hpos : 0 < W.length) :
    ∃ (y : α) (e : β) (h : G.IsLink e y b) (P : GraphWalk G a y),
      W = P.append (.cons h (.nil h.right_mem)) := by
  induction W with
  | nil h => exact (Nat.lt_irrefl 0 hpos).elim
  | @cons x y z e h R ih =>
    cases hcase : R with
    | nil hz => exact ⟨x, e, h, .nil h.left_mem, rfl⟩
    | cons h' R' =>
      have hR : 0 < R.length := by rw [hcase, GraphWalk.length_cons]; exact Nat.zero_lt_succ _
      obtain ⟨w, f, hf, P, hP⟩ := ih hR
      exact ⟨w, f, hf, .cons h P, congrArg (GraphWalk.cons h) (hcase.symm.trans hP)⟩

/-- Closing a simple path through a vertex outside its support
gives a simple closed walk, provided its two new edges differ.
The zero-edge path case gives a two-edge circuit. This constructs
the old circuit in XII (7.3), Claim (1), page 262. -/
theorem isSimpleClosed_close_path
    {α β : Type*} {G : Graph α β} {a b v : α} {e f : β}
    (he : G.IsLink e v a) (hf : G.IsLink f b v) (P : GraphWalk G a b)
    (hP : P.IsSimple) (hv : v ∉ P.support) (hef : e ≠ f) :
    (GraphWalk.cons he (P.append (.cons hf (.nil hf.right_mem)))).IsSimpleClosed := by
  have heP : e ∉ P.edges := fun h => hv (P.left_mem_support_of_mem_edges h he)
  have hfP : f ∉ P.edges := fun h => hv (P.left_mem_support_of_mem_edges h hf.symm)
  constructor
  · change (P.append (.cons hf (.nil hf.right_mem))).support.Nodup
    rw [GraphWalk.support_append]
    change (P.support ++ [v]).Nodup
    exact List.nodup_append.mpr ⟨hP, by simp, fun x hx y hy hxy => by
      have hyv : y = v := List.mem_singleton.mp hy
      exact hv (hxy.trans hyv ▸ hx)⟩
  · rw [GraphWalk.edges_cons, GraphWalk.edges_append]
    change (e :: (P.edges ++ [f])).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_append.mpr ⟨hP.edges_nodup, by simp, ?_⟩⟩
    · intro hem
      rcases List.mem_append.mp hem with hem | hem
      · exact heP hem
      · exact hef (List.mem_singleton.mp hem)
    · intro x hx y hy hxy
      have hyf : y = f := List.mem_singleton.mp hy
      exact hfP (hxy.trans hyf ▸ hx)

end GraphMinor.GM12

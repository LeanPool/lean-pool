/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# The finite subdivision graph

XII (4.5), page 252, replaces an original edge with as many new
edges as it has crossings. Keep the original vertices and add the
internal cut vertices of each edge. A new edge joins two consecutive
cuts on its original edge. The first and last cuts are identified
with the two original endpoints.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Graph

/-- The original vertices and the internal cut vertices of the
subdivision graph in XII (4.5), page 252. -/
abbrev SubdivisionVertex (m n : ℕ) (k : Fin n → ℕ) := Fin m ⊕ (Σ e : Fin n, Fin (k e - 1))

/-- The vertex at a cut on an original edge. The endpoint cuts
are the original vertices, as in XII (4.5), page 252. -/
def subdivisionVertexAt {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (e : Fin n) (i : Fin (k e + 1)) : SubdivisionVertex m n k :=
  if hzero : i.val = 0 then Sum.inl (κ (e, false)) else
    if hlast : i.val = k e then Sum.inl (κ (e, true)) else
      Sum.inr ⟨e, ⟨i.val - 1, by have := i.isLt; omega⟩⟩

/-- The graph obtained by replacing every original edge by its
chain of consecutive cut intervals, in XII (4.5), page 252. -/
def subdivisionGraph {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) :
    Graph (SubdivisionVertex m n k) (Σ e : Fin n, Fin (k e)) where
  vertexSet := univ
  edgeSet := univ
  IsLink e x y :=
    (x = subdivisionVertexAt κ k e.1 e.2.castSucc ∧ y = subdivisionVertexAt κ k e.1 e.2.succ) ∨
      (x = subdivisionVertexAt κ k e.1 e.2.succ ∧ y = subdivisionVertexAt κ k e.1 e.2.castSucc)
  isLink_symm := by
    intro e _
    refine ⟨fun x y h => ?_⟩
    exact h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact Or.inl rfl | exact Or.inr rfl
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨_, _, Or.inl ⟨rfl, rfl⟩⟩, fun _ => mem_univ e⟩
  left_mem_of_isLink := by intro e x y _; exact mem_univ x

/-- The first cut on an edge is its original first endpoint. -/
theorem subdivisionVertexAt_zero {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (e : Fin n) : subdivisionVertexAt κ k e 0 = Sum.inl (κ (e, false)) := by
  simp only [subdivisionVertexAt, Fin.val_zero, ↓reduceDIte]

/-- The last cut on a nonempty edge chain is its original last endpoint. -/
theorem subdivisionVertexAt_last {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (e : Fin n) (hk : 0 < k e) :
    subdivisionVertexAt κ k e (Fin.last (k e)) = Sum.inl (κ (e, true)) := by
  simp only [subdivisionVertexAt, Fin.val_last, Nat.ne_of_gt hk, ↓reduceDIte]

/-- An internal cut is the corresponding new vertex. -/
theorem subdivisionVertexAt_internal {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (e : Fin n) (j : Fin (k e - 1)) :
    subdivisionVertexAt κ k e ⟨j.val + 1, by have := j.isLt; omega⟩ = Sum.inr ⟨e, j⟩ := by
  have hzero : j.val + 1 ≠ 0 := by omega
  have hlast : j.val + 1 ≠ k e := by have := j.isLt; omega
  simp only [subdivisionVertexAt, hzero, hlast, ↓reduceDIte, Nat.add_sub_cancel]

/-- Each new edge joins the two consecutive cuts that define it. -/
theorem subdivisionGraph_isLink {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (e : Fin n) (i : Fin (k e)) :
    (subdivisionGraph κ k).IsLink ⟨e, i⟩
      (subdivisionVertexAt κ k e i.castSucc) (subdivisionVertexAt κ k e i.succ) :=
  Or.inl ⟨rfl, rfl⟩

end GraphMinor.GM12

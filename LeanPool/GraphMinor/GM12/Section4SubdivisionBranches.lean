/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionIncidence

/-!
# The branches contracting a subdivision

XII (4.5), page 252, uses that the subdivided graph has the
original clique as a minor. Assign every internal vertex of an
original edge to its right endpoint. Keep the first new edge to
represent the original edge. The branches are disjoint and each
later cut on an edge belongs to the branch of its right endpoint.
-/

public section

namespace GraphMinor.GM12

open Set Graph

/-- The branch at an original vertex, containing all internal
vertices assigned from right ends in the subdivision of XII (4.5), page 252. -/
@[expose] def subdivisionBranch {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (v : Fin m) : Set (SubdivisionVertex m n k) :=
  {x | match x with
    | Sum.inl w => w = v
    | Sum.inr ⟨e, _⟩ => κ (e, true) = v}

/-- The first new edge represents the original edge after the
remaining edges are contracted, in XII (4.5), page 252. -/
@[expose] def subdivisionFirstEdge {n : ℕ} (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (e : Fin n) : Σ f : Fin n, Fin (k f) := ⟨e, ⟨0, hk e⟩⟩

theorem mem_subdivisionBranch_original {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (v w : Fin m) : Sum.inl w ∈ subdivisionBranch κ k v ↔ w = v := Iff.rfl

theorem mem_subdivisionBranch_internal {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (v : Fin m) (e : Fin n) (i : Fin (k e - 1)) :
    Sum.inr ⟨e, i⟩ ∈ subdivisionBranch κ k v ↔ κ (e, true) = v := Iff.rfl

/-- Every contraction branch contains its original vertex. -/
theorem subdivisionBranch_nonempty {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (v : Fin m) : (subdivisionBranch κ k v).Nonempty := ⟨Sum.inl v, rfl⟩

/-- Distinct original vertices have disjoint subdivision branches. -/
theorem subdivisionBranch_disjoint {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    {v w : Fin m} (hvw : v ≠ w) : Disjoint (subdivisionBranch κ k v) (subdivisionBranch κ k w) := by
  apply disjoint_left.mpr
  intro x hx hy
  cases x with
  | inl z => exact hvw (hx.symm.trans hy)
  | inr q => exact hvw (hx.symm.trans hy)

/-- Every positive cut belongs to the branch of its edge's right
endpoint, including the last cut. -/
theorem mem_subdivisionBranch_vertexAt_pos {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) (v : Fin m) (e : Fin n)
    (i : Fin (k e + 1)) (hi : 0 < i.val) :
    subdivisionVertexAt κ k e i ∈ subdivisionBranch κ k v ↔ κ (e, true) = v := by
  unfold subdivisionVertexAt
  split_ifs with hzero hlast
  · omega
  · rfl
  · rfl

/-- The first cut belongs to the branch of its original left endpoint. -/
theorem mem_subdivisionBranch_vertexAt_zero {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) (v : Fin m) (e : Fin n) :
    subdivisionVertexAt κ k e 0 ∈ subdivisionBranch κ k v ↔ κ (e, false) = v := by
  rw [subdivisionVertexAt_zero]
  rfl

/-- Different original edges keep different first edges. -/
theorem subdivisionFirstEdge_injective {n : ℕ} (k : Fin n → ℕ) (hk : ∀ e, 0 < k e) :
    Function.Injective (subdivisionFirstEdge k hk) := by
  intro e f hef
  exact congrArg Sigma.fst hef

/-- A later edge of a subdivision chain is not a representing
first edge. Thus it remains available within its contraction branch. -/
theorem subdivisionEdge_not_mem_firstEdges {n : ℕ} (k : Fin n → ℕ) (hk : ∀ e, 0 < k e)
    (e : Fin n) (i : Fin (k e)) (hi : 0 < i.val) :
    (⟨e, i⟩ : Σ f : Fin n, Fin (k f)) ∉ range (subdivisionFirstEdge k hk) := by
  rintro ⟨f, hf⟩
  have hval := congrArg (fun q : Σ f : Fin n, Fin (k f) => q.2.val) hf
  change 0 = i.val at hval
  omega

end GraphMinor.GM12

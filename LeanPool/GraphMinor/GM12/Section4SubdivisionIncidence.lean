/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionGraph

/-!
# Vertices and incidences of the subdivision graph

In XII (4.5), page 252, consecutive cuts are the ends of a new
edge. The cut map on one original edge is injective when its
original endpoints are distinct. Consequently the subdivision
has no loops. Its incidence relation is exactly the pair of
consecutive cut vertices used to define each edge.
-/

public section

namespace GraphMinor.GM12

open Set Graph

private def localCutIndex {m n : ℕ} (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (e : Fin n) : SubdivisionVertex m n k → ℕ
  | Sum.inl v => if v = κ (e, false) then 0 else k e
  | Sum.inr ⟨_, j⟩ => j.val + 1

private theorem localCutIndex_vertexAt {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) (e : Fin n)
    (hκ : κ (e, false) ≠ κ (e, true)) (i : Fin (k e + 1)) :
    localCutIndex κ k e (subdivisionVertexAt κ k e i) = i.val := by
  unfold subdivisionVertexAt
  split_ifs with hzero hlast
  · simp only [localCutIndex, ↓reduceIte]
    exact hzero.symm
  · simp only [localCutIndex, Ne.symm hκ, ↓reduceIte]
    exact hlast.symm
  · change i.val - 1 + 1 = i.val
    omega

/-- Different cuts on one loopless original edge give different
subdivision vertices, as used in XII (4.5), page 252. -/
theorem subdivisionVertexAt_injective {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) (e : Fin n)
    (hκ : κ (e, false) ≠ κ (e, true)) : Function.Injective (subdivisionVertexAt κ k e) := by
  intro i j hij
  have hidx := congrArg (localCutIndex κ k e) hij
  rw [localCutIndex_vertexAt κ k e hκ, localCutIndex_vertexAt κ k e hκ] at hidx
  exact Fin.ext hidx

/-- A new subdivision edge is incident exactly with its two
consecutive cut vertices. -/
theorem subdivisionGraph_inc_iff {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (e : Fin n) (i : Fin (k e)) (x : SubdivisionVertex m n k) :
    (subdivisionGraph κ k).Inc ⟨e, i⟩ x ↔
      x = subdivisionVertexAt κ k e i.castSucc ∨ x = subdivisionVertexAt κ k e i.succ := by
  constructor
  · rintro ⟨y, hxy⟩
    exact hxy.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · rintro (rfl | rfl)
    · exact (subdivisionGraph_isLink κ k e i).inc_left
    · exact (subdivisionGraph_isLink κ k e i).inc_right

/-- Subdividing loopless edges leaves a loopless graph, as in
XII (4.5), page 252. -/
theorem subdivisionGraph_loopless {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ)
    (hκ : ∀ e, κ (e, false) ≠ κ (e, true)) :
    ∀ e x, ¬ (subdivisionGraph κ k).IsLink e x x := by
  rintro ⟨e, i⟩ x hx
  have hend : subdivisionVertexAt κ k e i.castSucc = subdivisionVertexAt κ k e i.succ :=
    hx.elim (fun h => h.1.symm.trans h.2) (fun h => h.2.symm.trans h.1)
  have hi := congrArg Fin.val (subdivisionVertexAt_injective κ k e (hκ e) hend)
  change i.val = i.val + 1 at hi
  omega

end GraphMinor.GM12

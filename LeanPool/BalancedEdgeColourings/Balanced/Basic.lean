/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Vizing.Kempe

/-!
# Balanced edge colourings: basic notions

Balister, Kostochka, Li and Schelp, *Balanced edge colorings*, JCTB 90 (2004) 3–20, §2.

For a proper colouring `c` of all edges of `G` with colours `Fin k` (`Total c`):
* `colSet c v` is `S(v)`, the set of colours on the edges at `v`;
* `cnt c S` is `n_S`, the number of vertices `v` with `S(v) = S`;
* `cost c = Σ_S n_S²`; a colouring is *optimal* if its cost is least among total colourings.

A Kempe change on the `(a, b)`-chain of `x` replaces `S(v)` by its image under the transposition
`(a b)` for every vertex `v` of the chain (`colSet_kempeSwap_of_reachable`), and keeps it
otherwise.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Balanced

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

/-- `c` colours every edge. -/
def Total (c : PEC G (Fin k)) : Prop := ∀ u v, G.Adj u v → c.col u v ≠ none

open Classical in
/-- `S(v)`: the colours present at `v`. -/
noncomputable def colSet (c : PEC G (Fin k)) (v : V) : Finset (Fin k) :=
  univ.filter fun θ => ¬ c.IsFree v θ

open Classical in
/-- `n_S`: the number of vertices with colour set `S`. -/
noncomputable def cnt (c : PEC G (Fin k)) (S : Finset (Fin k)) : ℕ :=
  #(univ.filter fun v => colSet c v = S)

/-- `Σ_S n_S²`. -/
noncomputable def cost (c : PEC G (Fin k)) : ℕ := ∑ S : Finset (Fin k), cnt c S ^ 2

/-- An optimal `k`-colouring: total, of least cost. -/
def IsOptimal (c : PEC G (Fin k)) : Prop :=
  Total c ∧ ∀ c' : PEC G (Fin k), Total c' → cost c ≤ cost c'

/-- The involution `i_ab` on colour sets. -/
def swapSet (a b : Fin k) (S : Finset (Fin k)) : Finset (Fin k) :=
  S.map (Equiv.swap a b).toEmbedding

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem mem_colSet {c : PEC G (Fin k)} {v : V} {θ : Fin k} :
    θ ∈ colSet c v ↔ ¬ c.IsFree v θ := by
  classical
  simp [colSet]
theorem mem_swapSet {a b θ : Fin k} {S : Finset (Fin k)} :
    θ ∈ swapSet a b S ↔ Equiv.swap a b θ ∈ S := by
  simp only [swapSet, mem_map_equiv, Equiv.symm_swap]

theorem swapSet_swapSet (a b : Fin k) (S : Finset (Fin k)) :
    swapSet a b (swapSet a b S) = S := by
  ext θ
  simp [mem_swapSet]

theorem card_swapSet (a b : Fin k) (S : Finset (Fin k)) : #(swapSet a b S) = #S := by
  simp [swapSet]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem colSet_kempeSwap_of_reachable [Finite V] (c : PEC G (Fin k)) (a b : Fin k) {x v : V}
    (hv : (c.kempeGraph a b).Reachable x v) :
    colSet (c.kempeSwap a b x) v = swapSet a b (colSet c v) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  ext θ
  rw [mem_colSet, mem_swapSet, mem_colSet, isFree_kempeSwap_of_reachable c a b hv]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem colSet_kempeSwap_of_not_reachable [Finite V] (c : PEC G (Fin k)) (a b : Fin k) {x v : V}
    (hv : ¬ (c.kempeGraph a b).Reachable x v) :
    colSet (c.kempeSwap a b x) v = colSet c v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  ext θ
  rw [mem_colSet, mem_colSet, isFree_kempeSwap_of_not_reachable c a b hv]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem Total.kempeSwap {c : PEC G (Fin k)} (h : Total c) (a b : Fin k) (x : V) :
    Total (c.kempeSwap a b x) := by
  classical
  exact fun u v huv => extends_kempeSwap c a b x u v (h u v huv)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- `Σ_S n_S² = Σ_v n_{S(v)}`. -/
theorem cost_eq_sum (c : PEC G (Fin k)) : cost c = ∑ v, cnt c (colSet c v) := by
  classical
  unfold cost
  rw [← Finset.sum_fiberwise_of_maps_to (g := colSet c) (t := univ) (fun v _ => mem_univ _)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_congr rfl (fun v hv => by rw [(mem_filter.1 hv).2]), sum_const, smul_eq_mul, sq]
  rfl
end Balanced

end LeanPool.BalancedEdgeColourings

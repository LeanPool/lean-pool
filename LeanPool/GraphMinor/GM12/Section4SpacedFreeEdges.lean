/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
public import LeanPool.GraphMinor.GM11.Defs
public import LeanPool.GraphMinor.GM10.Defs
import LeanPool.GraphMinor.GM12.Section4DistantEdges
import LeanPool.GraphMinor.GM12.Section4PathExists
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM12.Section4FreePathEdge
import LeanPool.GraphMinor.GM12.Section4PathThreshold
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Walks

/-!
# Choosing mutually distant free edges

XII (4.3), claims (3)--(4), page 250, chooses the first path
edges at thresholds `(k + 7)i`, for `1 ≤ i ≤ t`. Each first
crossing overshoots by at most three, so the chosen edges are at
pairwise distance at least `k + 4`. Their thresholds leave a gap
of two from both end edges, making them free by claim (1).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 GM14

/-- The family of free edges chosen after claims (3)--(4) in
Graph Minors XII (4.3), page 250. -/
theorem exists_spaced_free_edges_on_path
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ k t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hθ : 5 + t * (k + 7) ≤ θ)
    {x y : S} (W : GraphWalk Γ.toGraph x y) (hW : W.IsSimple)
    {g h : Set S} (hg : g ∈ Γ.E) (hh : h ∈ Γ.E)
    (hx : x ∈ closure g) (hy : y ∈ closure h) (hfar : θ ≤ d g h) :
    ∃ (f : Fin t → Set S) (a b : Fin t → S),
      (∀ i, f i ∈ W.edges ∧ Γ.toGraph.IsLink (f i) (a i) (b i) ∧
        a i ≠ b i ∧ IsFreeSet Γ.toHypergraph T θ {a i, b i}) ∧
      (∀ i j, i ≠ j → k + 4 ≤ d (f i) (f j)) := by
  classical
  let n : Fin t → ℕ := fun i => (k + 7) * (i.val + 1)
  have hn : ∀ i, 2 ≤ n i ∧ n i + 5 ≤ θ := by
    intro i
    have hlow := Nat.mul_le_mul_left (k + 7) (show 1 ≤ i.val + 1 by omega)
    have hhigh := Nat.mul_le_mul_left (k + 7) (Nat.succ_le_of_lt i.isLt)
    dsimp only [n]
    rw [Nat.mul_one] at hlow
    rw [Nat.mul_comm (k + 7) t] at hhigh
    change (k + 7) * (i.val + 1) ≤ t * (k + 7) at hhigh
    omega
  have hex : ∀ i : Fin t, ∃ f ∈ W.edges, n i ≤ d g f ∧ d g f ≤ n i + 3 := by
    intro i
    obtain ⟨p, f, q, heq, _, hlo, hhi⟩ := exists_first_path_threshold_edge hS hm W hg hh hx hy
      (show 1 ≤ n i by have h := (hn i).1; omega)
      (show n i + 4 ≤ d g h by have h := (hn i).2; omega)
    exact ⟨f, heq ▸ List.mem_append_right p List.mem_cons_self, hlo, hhi⟩
  choose f hf hlo hhi using hex
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hsym := h91.2.2.2.1
  have htri := h91.2.2.2.2.1
  have hfA : ∀ i, f i ∈ Γ.A := by
    intro i
    exact Or.inl (Or.inr ((walkDrawing_isSubdrawing Γ W).2
      ((walkDrawing_E Γ W).symm ▸ hf i)))
  have hgA : g ∈ Γ.A := Or.inl (Or.inr hg)
  have hhA : h ∈ Γ.A := Or.inl (Or.inr hh)
  have hfree : ∀ i, ∃ a b, Γ.toGraph.IsLink (f i) a b ∧ a ≠ b ∧
      IsFreeSet Γ.toHypergraph T θ {a, b} := by
    intro i
    have hdist := htri g hgA (f i) (hfA i) h hhA
    rw [hsym (f i) (hfA i) h hhA] at hdist
    have hi := hn i
    have hi' := hhi i
    exact free_path_edge_of_metric_distant_ends hS hm (by omega) W hW hg hh hx hy (hf i)
      (hi.1.trans (hlo i)) (by omega)
  choose a b hl hab hfree using hfree
  refine ⟨f, a, b, fun i => ⟨hf i, hl i, hab i, hfree i⟩, ?_⟩
  have hordered : ∀ i j : Fin t, i.val < j.val → k + 4 ≤ d (f i) (f j) := by
    intro i j hij
    have hgap := Nat.mul_le_mul_left (k + 7)
      (show (i.val + 1) + 1 ≤ j.val + 1 by omega)
    rw [Nat.mul_add, Nat.mul_one] at hgap
    have ht := htri g hgA (f i) (hfA i) (f j) (hfA j)
    have hi := hhi i
    have hj := hlo j
    change (k + 7) * (i.val + 1) + (k + 7) ≤ (k + 7) * (j.val + 1) at hgap
    change d g (f i) ≤ (k + 7) * (i.val + 1) + 3 at hi
    change (k + 7) * (j.val + 1) ≤ d g (f j) at hj
    omega
  intro i j hij
  rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hij' | hij'
  · exact hordered i j hij'
  · rw [hsym (f i) (hfA i) (f j) (hfA j)]
    exact hordered j i hij'

/-- The free-edge family needed for XII (4.3), page 250, with the
two distant edges and their connecting path supplied by the tangle. -/
theorem exists_spaced_free_edges
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ k t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hθ : 5 + t * (k + 7) ≤ θ) :
    ∃ (f : Fin t → Set S) (a b : Fin t → S),
      (∀ i, f i ∈ Γ.E ∧ Γ.toGraph.IsLink (f i) (a i) (b i) ∧
        a i ≠ b i ∧ IsFreeSet Γ.toHypergraph T θ {a i, b i}) ∧
      (∀ i j, i ≠ j → k + 4 ≤ d (f i) (f j)) := by
  obtain ⟨g, hg, h, hh, hdist⟩ := exists_two_edges_at_tangle_order_distance hS hm (by omega)
  obtain ⟨x, x', hlx⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet hg
  obtain ⟨y, y', hly⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet hh
  have hx : x ∈ closure g := by
    have h : x ∈ closure g ∩ Γ.V := by rw [hlx.2.2.2]; simp
    exact h.1
  have hy : y ∈ closure h := by
    have h : y ∈ closure h ∩ Γ.V := by rw [hly.2.2.2]; simp
    exact h.1
  obtain ⟨W₀⟩ := exists_walk_of_open_disc_regions hS hm.1.1.2 hlx.left_mem hly.left_mem
  obtain ⟨W, hW, _, _⟩ := GM09.exists_isSimple_subwalk W₀
  obtain ⟨f, a, b, hf, hsep⟩ := exists_spaced_free_edges_on_path hS hm hθ W hW hg hh hx hy
    (by rw [hdist])
  refine ⟨f, a, b, ?_, hsep⟩
  intro i
  exact ⟨(hf i).2.1.edge_mem, (hf i).2⟩

end GraphMinor.GM12

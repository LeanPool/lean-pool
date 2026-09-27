/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the AX1 packing gap: the low-degree core reduction and the residual `CoreGapResidual`

`Nibble.AX1.NibbleGapResidual` (`Nibble.DenseGapAX1`) is the last assumed atom of AX1: the packing
gap `ν₃* − ν₃ ≤ ε|V|²` for graphs that fail the density threshold (some vertex of degree `< θ|V|`)
but are triangle-rich.  This file does two things.

* It **removes the density threshold entirely** by a genuine graph-theoretic reduction — the
  low-degree *core*.  Repeatedly deleting all edges at a vertex of positive degree below `t` costs
  at most `t` edges per step and permanently isolates the chosen vertex, so after at most `|V|`
  steps one is left with a spanning subgraph `G'` in which every vertex is isolated or has degree
  at least `t`, at a total cost of at most `t·|V|` edges (`Nibble.AX1.exists_core`).  Deleting `k`
  edges moves `ν₃*` by at most `k` (`Nibble.AX1.nu3star_le_add_deleted`) and can only decrease `ν₃`
  (`Nibble.AX1.nu3_mono`), so the packing gap is stable under the passage to the core
  (`Nibble.AX1.gap_le_core_gap`).  Taking `t = (ε/4)|V|` this reduces `NibbleGapResidual` to the
  packing gap for graphs whose vertices are all isolated or of degree `≥ δ|V|`.

* It **proves that residual outright in the whole range `δ ∈ [1 − μ(ε)/2, 1)`**: this is the dense
  branch, but now tolerating isolated vertices, which the original `Nibble.AX1.nibbleGap_dense`
  does not.  The point is that the triangle hypergraph lives on the EDGES of `G`, so isolated
  vertices are invisible to it: all degree and codegree estimates may be taken relative to the
  support `Nibble.AX1.posDeg G` instead of `V` (`Nibble.AX1.triangleSub_degree_le_support`,
  `Nibble.AX1.triangleSub_degree_ge_support`), and the nibble is then run at scale
  `d = |support|`.

## The statements

* `Nibble.AX1.CoreGapAt ε δ` — the packing gap `ν₃* − ν₃ ≤ ε|V|²` for large graphs in which every
  vertex is isolated or has degree `≥ δ|V|`, and which are fractionally rich (`ν₃* > ε|V|²`; without
  this the conclusion is trivial).
* `Nibble.AX1.CoreGapResidual` — `∀ ε > 0, ∀ δ > 0, CoreGapAt ε δ`.
* `Nibble.AX1.nibbleGapResidual_of_coreGapResidual`,
  `Nibble.AX1.nibbleGapHyp_of_coreGapResidual`, `Nibble.AX1.ax1_of_coreGapResidual` — the machine
  checked reductions `CoreGapResidual → NibbleGapResidual → NibbleGapHyp → AX1Statement`.
* `Nibble.AX1.coreGapResidual_of_nibbleGapResidual` — the converse: the two residuals are
  equivalent, so nothing has been lost (or smuggled in) by the reformulation.
* `Nibble.AX1.coreGapAt_dense` — **unconditional**: for every `ε > 0` there is `θ < 1` with
  `CoreGapAt ε θ`; with `Nibble.AX1.CoreGapAt.mono_delta` this proves `CoreGapAt ε δ` for every
  `δ ≥ θ(ε)`.
* `Nibble.AX1.coreGapAt_of_third` — `CoreGapAt ε δ` is trivially true for `ε ≥ 1/3`.

So the *only* open instances are `CoreGapAt ε δ` with `ε < 1/3` and `0 < δ < θ(ε)`; see
`RESIDUAL.md`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.DenseGapAX1

/-! # CoreGapAX1 -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Monotonicity of the packing numbers under edge deletion -/

/-- The triangle hypergraph is monotone in the graph. -/
theorem triangleHypergraphE_mono (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G' ≤ G) : triangleHypergraphE G' ⊆ triangleHypergraphE G := by
  unfold triangleHypergraphE
  exact Finset.image_subset_image (SimpleGraph.cliqueFinset_mono G h)

/-- **`ν₃` is monotone.**  Every edge-disjoint triangle packing of a spanning subgraph is one of the
graph itself. -/
theorem nu3_mono (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj] (h : G' ≤ G) :
    nu3 G' ≤ nu3 G := by
  classical
  unfold nu3
  refine Finset.sup_le ?_
  intro M hM
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  exact nu3_ge G ⟨hM.2.subset.trans (triangleHypergraphE_mono G G' h), hM.2.disjoint⟩

/-- A triangle of `G` that is not a triangle of the spanning subgraph `G'` has one of its three
edges among the deleted ones. -/
theorem exists_deleted_edge (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE G)
    (hT' : T ∉ triangleHypergraphE G') :
    ∃ e ∈ G.cliqueFinset 2 \ G'.cliqueFinset 2, e ∈ T := by
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  by_contra hcon
  push Not at hcon
  refine hT' ?_
  rw [triangleHypergraphE, Finset.mem_image]
  refine ⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, ht.card_eq⟩, rfl⟩
  intro a ha b hb hab
  have hmem : ({a, b} : Finset V) ∈ t.powersetCard 2 := by
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair hab⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h2 : ({a, b} : Finset V) ∈ G.cliqueFinset 2 :=
    powersetCard_two_subset_cliqueFinset G ht hmem
  have hin : ({a, b} : Finset V) ∈ G'.cliqueFinset 2 := by
    by_contra hc
    exact hcon _ (Finset.mem_sdiff.mpr ⟨h2, hc⟩) hmem
  rw [SimpleGraph.mem_cliqueFinset_iff] at hin
  exact hin.1 (by simp) (by simp) hab

/-- **`ν₃*` is stable under edge deletion.**  Deleting a set `D` of edges decreases the fractional
triangle packing number by at most `|D|`: the weight carried by the triangles that are destroyed is
at most the total edge load of `D`, which is at most `|D|`. -/
theorem nu3star_le_add_deleted (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) :
    nu3star G ≤ nu3star G' + ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) := by
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨hnn, hzero, hcon⟩ := hw
  set D : Finset (Finset V) := G.cliqueFinset 2 \ G'.cliqueFinset 2 with hD
  set H : Finset (Finset (Finset V)) := triangleHypergraphE G with hH
  set H' : Finset (Finset (Finset V)) := triangleHypergraphE G' with hH'
  have hsub : H' ⊆ H := triangleHypergraphE_mono G G' hle
  set w' : Finset (Finset V) → ℝ := fun T => if T ∈ H' then w T else 0 with hw'def
  have hw'nn : ∀ T, 0 ≤ w' T := by
    intro T
    dsimp only [w', hw'def]
    split
    · exact hnn T
    · exact le_refl 0
  have hw' : IsFracPacking G' w' := by
    refine ⟨hw'nn, ?_, ?_⟩
    · intro T hT
      dsimp only [w', hw'def]
      rw [ite_eq_right hT]
    · intro e
      calc ∑ T ∈ H'.filter (fun T => e ∈ T), w' T
          = ∑ T ∈ H'.filter (fun T => e ∈ T), w T := by
            refine Finset.sum_congr rfl (fun T hT => ?_)
            dsimp only [w', hw'def]
            rw [ite_eq_left (Finset.mem_filter.mp hT).1]
        _ ≤ ∑ T ∈ H.filter (fun T => e ∈ T), w T :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset_filter _ hsub) (fun T _ _ => hnn T)
        _ ≤ 1 := hcon e
  have hval : ∑ T ∈ H', w' T ≤ nu3star G' := le_csSup (nu3star_bddAbove G') ⟨w', hw', rfl⟩
  have heq : ∑ T ∈ H', w' T = ∑ T ∈ H', w T :=
    Finset.sum_congr rfl (fun T hT => by dsimp only [w', hw'def]; rw [ite_eq_left hT])
  have hsplit : ∑ T ∈ H \ H', w T + ∑ T ∈ H', w T = ∑ T ∈ H, w T := Finset.sum_sdiff hsub
  have hkey : ∑ T ∈ H \ H', w T ≤ (D.card : ℝ) := by
    have step1 : ∀ T ∈ H \ H', w T ≤ ∑ e ∈ D, (if e ∈ T then w T else 0) := by
      intro T hT
      rw [Finset.mem_sdiff] at hT
      obtain ⟨e, heD, heT⟩ := exists_deleted_edge G G' hT.1 hT.2
      calc w T = (if e ∈ T then w T else 0) := by rw [ite_eq_left heT]
        _ ≤ ∑ e ∈ D, (if e ∈ T then w T else 0) := by
            refine Finset.single_le_sum (f := fun e => if e ∈ T then w T else 0) ?_ heD
            intro i _
            split
            · exact hnn T
            · exact le_refl 0
    calc ∑ T ∈ H \ H', w T ≤ ∑ T ∈ H \ H', ∑ e ∈ D, (if e ∈ T then w T else 0) :=
          Finset.sum_le_sum step1
      _ = ∑ e ∈ D, ∑ T ∈ H \ H', (if e ∈ T then w T else 0) := Finset.sum_comm
      _ = ∑ e ∈ D, ∑ T ∈ (H \ H').filter (fun T => e ∈ T), w T := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [Finset.sum_filter]
      _ ≤ ∑ e ∈ D, ∑ T ∈ H.filter (fun T => e ∈ T), w T := by
          refine Finset.sum_le_sum (fun e _ => ?_)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset_filter _ Finset.sdiff_subset) (fun T _ _ => hnn T)
      _ ≤ ∑ _e ∈ D, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hcon e)
      _ = (D.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith only [hsplit, heq, hval, hkey]

/-- **The packing gap is stable under edge deletion.** -/
theorem gap_le_core_gap (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G' ≤ G) :
    nu3star G - (nu3 G : ℝ)
      ≤ (nu3star G' - (nu3 G' : ℝ)) + ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) := by
  have h1 := nu3star_le_add_deleted G G' hle
  have h2 : (nu3 G' : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast nu3_mono G G' hle
  linarith

/-! ### The low-degree core -/

/-- `G` with every edge at a vertex of `K` deleted. -/
def restrictAway (G : SimpleGraph V) (K : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ K ∧ y ∉ K
  symm := ⟨by rintro x y ⟨h1, h2, h3⟩; exact ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

instance instDecidableRelRestrictAway (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) :
    DecidableRel (restrictAway G K).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ x ∉ K ∧ y ∉ K))

omit [Fintype V] [DecidableEq V] in
theorem restrictAway_le (G : SimpleGraph V) (K : Finset V) : restrictAway G K ≤ G :=
  fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] in
theorem restrictAway_mono (G : SimpleGraph V) {K K' : Finset V} (h : K ⊆ K') :
    restrictAway G K' ≤ restrictAway G K :=
  fun _ _ hx => ⟨hx.1, fun hc => hx.2.1 (h hc), fun hc => hx.2.2 (h hc)⟩

theorem cliqueFinset_two_restrictAway_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    (restrictAway G ∅).cliqueFinset 2 = G.cliqueFinset 2 := by
  ext e
  simp only [SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · rintro ⟨hc, hcard⟩
    exact ⟨fun a ha b hb hab => (hc ha hb hab).1, hcard⟩
  · rintro ⟨hc, hcard⟩
    exact ⟨fun a ha b hb hab => ⟨hc ha hb hab, by simp, by simp⟩, hcard⟩

theorem restrictAway_degree_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj] {K : Finset V} {v : V}
    (hv : v ∈ K) : (restrictAway G K).degree v = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
  rintro ⟨-, h, -⟩
  exact h hv

/-- Isolating one more vertex destroys at most `deg v` edges. -/
theorem deleted_insert_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (v : V) :
    ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2).card
      ≤ (restrictAway G K).degree v := by
  have hsub : ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2)
      ⊆ ((restrictAway G K).neighborFinset v).image (fun u => ({v, u} : Finset V)) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨he1, he2⟩ := he
    rw [SimpleGraph.mem_cliqueFinset_iff] at he1
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he1.card_eq
    have hadj : (restrictAway G K).Adj a b := he1.1 (by simp) (by simp) hab
    have hnadj : ¬ (restrictAway G (insert v K)).Adj a b := by
      intro hc
      refine he2 (SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, Finset.card_pair hab⟩)
      intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hc
      · exact hc.symm
      · exact absurd rfl hxy
    have hv : a = v ∨ b = v := by
      by_contra hcon
      push Not at hcon
      exact hnadj ⟨hadj.1, by simp [hadj.2.1, hcon.1], by simp [hadj.2.2, hcon.2]⟩
    rw [Finset.mem_image]
    rcases hv with rfl | rfl
    · exact ⟨b, by rw [SimpleGraph.mem_neighborFinset]; exact hadj, rfl⟩
    · exact ⟨a, by rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm, by rw [Finset.pair_comm]⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_image_le ?_
  rw [SimpleGraph.card_neighborFinset_eq_degree]

/-- The support of `G`: its non-isolated vertices. -/
def posDeg (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun x => 0 < G.degree x)

omit [DecidableEq V] in
theorem mem_posDeg_iff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    x ∈ posDeg G ↔ 0 < G.degree x := by
  simp only [posDeg, Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq V] in
theorem card_posDeg_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    (posDeg G).card ≤ Fintype.card V := Finset.card_le_univ _

/-- **The core.**  Iteratively isolating the vertices of positive degree below `t` produces a
spanning subgraph in which every vertex is isolated or has degree at least `t`, at a cost of at
most `t·m` deleted edges, where `m` bounds the number of non-isolated vertices. -/
theorem exists_core_aux (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℝ} (ht : 0 ≤ t) :
    ∀ (m : ℕ) (K : Finset V), (posDeg (restrictAway G K)).card ≤ m →
    ∃ K' : Finset V, K ⊆ K' ∧
      (∀ x, (restrictAway G K').degree x = 0 ∨ t ≤ ((restrictAway G K').degree x : ℝ)) ∧
      (((restrictAway G K).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2).card : ℝ)
        ≤ t * m := by
  intro m
  induction m with
  | zero =>
      intro K hK
      refine ⟨K, Finset.Subset.refl _, ?_, by simp⟩
      intro x
      left
      by_contra hc
      have hx : x ∈ posDeg (restrictAway G K) := by
        rw [mem_posDeg_iff]
        omega
      have := Finset.card_pos.mpr ⟨x, hx⟩
      omega
  | succ m ih =>
      intro K hK
      by_cases hgood : ∀ x, (restrictAway G K).degree x = 0 ∨
          t ≤ ((restrictAway G K).degree x : ℝ)
      · refine ⟨K, Finset.Subset.refl _, hgood, ?_⟩
        simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
        positivity
      push Not at hgood
      obtain ⟨v, hv0, hvt⟩ := hgood
      have hvpos : 0 < (restrictAway G K).degree v := Nat.pos_of_ne_zero hv0
      have hvmem : v ∈ posDeg (restrictAway G K) := (mem_posDeg_iff _ v).mpr hvpos
      have hcard : (posDeg (restrictAway G (insert v K))).card ≤ m := by
        have hsub : posDeg (restrictAway G (insert v K)) ⊆
            (posDeg (restrictAway G K)).erase v := by
          intro x hx
          rw [mem_posDeg_iff] at hx
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · rintro rfl
            rw [restrictAway_degree_eq_zero G (Finset.mem_insert_self x K)] at hx
            omega
          · rw [mem_posDeg_iff]
            exact lt_of_lt_of_le hx
              (SimpleGraph.degree_le_of_le (restrictAway_mono G (Finset.subset_insert v K)))
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hvmem] at hle
        omega
      obtain ⟨K', hKK', hprop, hdel⟩ := ih (insert v K) hcard
      refine ⟨K', Finset.Subset.trans (Finset.subset_insert v K) hKK', hprop, ?_⟩
      have hsplit : ((restrictAway G K).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2)
          ⊆ ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2)
            ∪ ((restrictAway G (insert v K)).cliqueFinset 2 \
                (restrictAway G K').cliqueFinset 2) := by
        intro e he
        rw [Finset.mem_sdiff] at he
        rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
        by_cases hc : e ∈ (restrictAway G (insert v K)).cliqueFinset 2
        · exact Or.inr ⟨hc, he.2⟩
        · exact Or.inl ⟨he.1, hc⟩
      have hc1 := deleted_insert_card_le G K v
      have hcard2 : (((restrictAway G K).cliqueFinset 2 \
          (restrictAway G K').cliqueFinset 2).card : ℝ)
          ≤ ((restrictAway G K).degree v : ℝ) +
            (((restrictAway G (insert v K)).cliqueFinset 2 \
              (restrictAway G K').cliqueFinset 2).card : ℝ) := by
        have h1 := Finset.card_le_card hsplit
        have h2 := Finset.card_union_le
          ((restrictAway G K).cliqueFinset 2 \ (restrictAway G (insert v K)).cliqueFinset 2)
          ((restrictAway G (insert v K)).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2)
        have h3 : ((restrictAway G K).cliqueFinset 2 \ (restrictAway G K').cliqueFinset 2).card
            ≤ (restrictAway G K).degree v +
              ((restrictAway G (insert v K)).cliqueFinset 2 \
                (restrictAway G K').cliqueFinset 2).card := by omega
        exact_mod_cast h3
      push_cast
      nlinarith only [hdel, hcard2, hvt]

/-- **The core, unpacked.**  Every graph has a spanning subgraph in which every vertex is isolated
or of degree at least `t`, obtained by deleting at most `t·|V|` edges. -/
theorem exists_core (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : Finset V,
      (∀ x, (restrictAway G K).degree x = 0 ∨ t ≤ ((restrictAway G K).degree x : ℝ)) ∧
      ((G.cliqueFinset 2 \ (restrictAway G K).cliqueFinset 2).card : ℝ)
        ≤ t * (Fintype.card V : ℝ) := by
  obtain ⟨K, -, hprop, hdel⟩ :=
    exists_core_aux G ht (Fintype.card V) ∅ (card_posDeg_le (restrictAway G ∅))
  refine ⟨K, hprop, ?_⟩
  rwa [cliqueFinset_two_restrictAway_empty G] at hdel

/-! ### The dense branch in the presence of isolated vertices -/

omit [DecidableEq V] in
theorem neighborFinset_subset_posDeg (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    G.neighborFinset u ⊆ posDeg G := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy
  rw [mem_posDeg_iff, ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
  exact ⟨u, by rw [SimpleGraph.mem_neighborFinset]; exact hy.symm⟩

theorem edgeV_pair (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    ∃ u v : V, u ≠ v ∧ E.val = ({u, v} : Finset V) := by
  have h2 := (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq
  obtain ⟨u, v, huv, h⟩ := Finset.card_eq_two.mp h2
  exact ⟨u, v, huv, h⟩

/-- **Support ceiling.**  Every edge lies in at most `|support|` triangles. -/
theorem triangleSub_degree_le_support (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G) :
    (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ ((posDeg G).card : ℝ) := by
  obtain ⟨u, v, -, hE⟩ := edgeV_pair G E
  rw [triangleSub_degree_eq_inter G E u v hE]
  have h : (G.neighborFinset u ∩ G.neighborFinset v).card ≤ (posDeg G).card :=
    Finset.card_le_card
      (Finset.Subset.trans Finset.inter_subset_left (neighborFinset_subset_posDeg G u))
  exact_mod_cast h

/-- **Support floor.**  If every non-isolated vertex has degree at least `D`, then every edge lies
in at least `2D − |support|` triangles: the two neighbourhoods live inside the support. -/
theorem triangleSub_degree_ge_support (G : SimpleGraph V) [DecidableRel G.Adj] (E : EdgeV G)
    {D : ℕ} (hD : ∀ x : V, 0 < G.degree x → D ≤ G.degree x) :
    2 * (D : ℝ) - ((posDeg G).card : ℝ)
      ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
  obtain ⟨u, v, huv, hE⟩ := edgeV_pair G E
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp E.2
  rw [hE] at hclique
  have hadj : G.Adj u v := hclique.1 (by simp) (by simp) huv
  have hdu : 0 < G.degree u := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨v, by rw [SimpleGraph.mem_neighborFinset]; exact hadj⟩
  have hdv : 0 < G.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨u, by rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm⟩
  rw [triangleSub_degree_eq_inter G E u v hE]
  have hunion : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ (posDeg G).card :=
    Finset.card_le_card (Finset.union_subset (neighborFinset_subset_posDeg G u)
      (neighborFinset_subset_posDeg G v))
  have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have h1 := hD u hdu
  have h2 := hD v hdv
  have hnat : 2 * D ≤ (posDeg G).card + (G.neighborFinset u ∩ G.neighborFinset v).card := by omega
  have hR : (2 * D : ℝ) ≤ ((posDeg G).card : ℝ)
      + ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) := by exact_mod_cast hnat
  linarith

theorem cliqueFinset_two_eq_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : (posDeg G).card = 0) : G.cliqueFinset 2 = ∅ := by
  rw [Finset.card_eq_zero] at h
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [SimpleGraph.mem_cliqueFinset_iff] at he
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp he.card_eq
  have hadj : G.Adj u v := he.1 (by simp) (by simp) huv
  have hu : u ∈ posDeg G := by
    rw [mem_posDeg_iff, ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨v, by rw [SimpleGraph.mem_neighborFinset]; exact hadj⟩
  rw [h] at hu
  exact absurd hu (Finset.notMem_empty u)

/-- A graph with no edges has zero packing gap. -/
theorem gap_le_of_no_edges (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ} (hc : 0 ≤ c)
    (h : (posDeg G).card = 0) : nu3star G - (nu3 G : ℝ) ≤ c := by
  have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  rw [cliqueFinset_two_eq_empty G h] at h1
  simp only [Finset.card_empty, Nat.cast_zero, zero_div] at h1
  have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The dense branch, tolerating isolated vertices.**  For every `ε > 0` there is a density
threshold `θ < 1` and a size threshold `n₀` such that every graph on at least `n₀` vertices all of
whose vertices are isolated or of degree at least `θ|V|` satisfies `ν₃* − ν₃ ≤ ε|V|²`.

The triangle hypergraph lives on the edges, so the isolated vertices are invisible to it: run the
nibble at the scale `d = |support|`, at which the hypergraph is near-`d`-regular with an *empty*
exceptional set. -/
theorem nibbleGap_denseCore (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (∀ x : V, G.degree x = 0 ∨ θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ :=
    nibbleTheoremMostCeil_holds 3 (by norm_num) (3 * ε) (by linarith)
  have hmpos : 0 < min μ 1 := lt_min hμ one_pos
  have hm1 : min μ 1 ≤ 1 := min_le_right _ _
  have hmμ : min μ 1 ≤ μ := min_le_left _ _
  have hθ0 : (0 : ℝ) < 1 - min μ 1 / 2 := by linarith
  have hθ1 : (1 : ℝ) - min μ 1 / 2 < 1 := by linarith
  refine ⟨1 - min μ 1 / 2, hθ0, hθ1,
    ⌈max d₀ (max (1 / μ) 1) / (1 - min μ 1 / 2)⌉₊, ?_⟩
  intro V _ _ G _ hV hdeg
  set θ : ℝ := 1 - min μ 1 / 2 with hθdef
  set R : ℝ := max d₀ (max (1 / μ) 1) with hRdef
  have hnR : R / θ ≤ (Fintype.card V : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hV)
  have hRθn : R ≤ θ * (Fintype.card V : ℝ) := by
    rw [div_le_iff₀ hθ0] at hnR; linarith
  rcases Nat.eq_zero_or_pos (posDeg G).card with hs0 | hspos
  · exact gap_le_of_no_edges G (by positivity) hs0
  obtain ⟨x, hx⟩ : ∃ x, x ∈ posDeg G := Finset.card_pos.mp hspos
  rw [mem_posDeg_iff] at hx
  have hdegx : θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ) := by
    rcases hdeg x with h | h
    · omega
    · exact h
  -- the support is large
  have hxs : (G.degree x : ℝ) ≤ ((posDeg G).card : ℝ) := by
    have h : G.degree x ≤ (posDeg G).card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (neighborFinset_subset_posDeg G x)
    exact_mod_cast h
  have hsupp : θ * (Fintype.card V : ℝ) ≤ ((posDeg G).card : ℝ) := le_trans hdegx hxs
  have hsR : R ≤ ((posDeg G).card : ℝ) := le_trans hRθn hsupp
  have hd0 : d₀ ≤ ((posDeg G).card : ℝ) := le_trans (le_max_left _ _) hsR
  have hinv : 1 / μ ≤ ((posDeg G).card : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsR
  have hspos' : (0 : ℝ) < ((posDeg G).card : ℝ) := by exact_mod_cast hspos
  have hcodeg : (1 : ℝ) ≤ μ * ((posDeg G).card : ℝ) := by
    rw [div_le_iff₀ hμ] at hinv; linarith
  have hsn : ((posDeg G).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast card_posDeg_le G
  -- the integer degree floor
  set D : ℕ := ⌈θ * (Fintype.card V : ℝ)⌉₊ with hDdef
  have hD : ∀ y : V, 0 < G.degree y → D ≤ G.degree y := by
    intro y hy
    refine Nat.ceil_le.mpr ?_
    rcases hdeg y with h | h
    · omega
    · exact h
  have hDR : θ * (Fintype.card V : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
  -- the near-regularity window at scale `d = |support|`
  have hwindow : ∀ E : EdgeV G,
      (1 - μ) * ((posDeg G).card : ℝ) ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ∧
        (Hypergraph.degree (triangleHypergraphSub G) E : ℝ)
          ≤ (1 + μ) * ((posDeg G).card : ℝ) := by
    intro E
    have hlo := triangleSub_degree_ge_support G E hD
    have hhi := triangleSub_degree_le_support G E
    have hθs : θ * ((posDeg G).card : ℝ) ≤ θ * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_left hsn hθ0.le
    constructor
    · nlinarith
    · nlinarith
  have hreg : NearlyRegularMost (triangleHypergraphSub G) ((posDeg G).card : ℝ) μ η :=
    triangleHypergraphSub_nearlyRegularMost_of_bounds G ∅
      (by
        rw [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hη.le (Nat.cast_nonneg _))
      (fun E _ => (hwindow E).1) (fun E _ => (hwindow E).2)
  have hcod : CodegreeBounded (triangleHypergraphSub G) (μ * ((posDeg G).card : ℝ)) :=
    triangleHypergraphSub_codegreeBounded G hcodeg
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) ((posDeg G).card : ℝ) hspos' hd0
      (triangleHypergraphSub_uniform G) hreg hcod (fun E => (hwindow E).2)
  refine gap_le_of_sub_matching G hε hM ?_
  simpa using hMcard

/-- **A new unconditional branch: graphs with a dense core.**  For every `ε > 0` there are `θ < 1`
and `n₀` such that every large graph which becomes (isolated-or-)`θ|V|`-dense after deleting at most
`(ε/4)|V|²` edges has packing gap at most `ε|V|²`.

This strictly extends `Nibble.AX1.nibbleGap_dense` (take `G' = G`, no deletion): the graph itself may
have arbitrarily many vertices of arbitrarily small positive degree, as long as the edges at them are
few. -/
theorem nibbleGap_of_dense_core (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (∀ G' : SimpleGraph V, ∀ _ : DecidableRel G'.Adj, G' ≤ G →
          ((G.cliqueFinset 2 \ G'.cliqueFinset 2).card : ℝ) ≤ (ε / 4) * (Fintype.card V : ℝ) ^ 2 →
          (∀ x : V, G'.degree x = 0 ∨ θ * (Fintype.card V : ℝ) ≤ (G'.degree x : ℝ)) →
          nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2) := by
  obtain ⟨θ, hθ0, hθ1, n₀, hdense⟩ := nibbleGap_denseCore (3 * ε / 4) (by linarith)
  refine ⟨θ, hθ0, hθ1, n₀, ?_⟩
  intro V _ _ G _ hV G' _ hle hdel hdeg
  have hgap' := hdense V G' hV hdeg
  have hstab := gap_le_core_gap G G' hle
  linarith

/-! ### The residual -/

/-- **The core packing-gap statement at parameters `(ε, δ)`.**  The gap `ν₃* − ν₃ ≤ ε|V|²` for large
graphs in which every vertex is isolated or has degree at least `δ|V|`, and whose fractional packing
number exceeds `ε|V|²` (otherwise the conclusion is immediate from `ν₃ ≥ 0`). -/
def CoreGapAt (ε δ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    (∀ x : V, G.degree x = 0 ∨ δ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)) →
    ε * (Fintype.card V : ℝ) ^ 2 < nu3star G →
    nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The residual.**  The core packing gap at every pair of parameters. -/
def CoreGapResidual : Prop := ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → CoreGapAt ε δ

/-- Raising the degree threshold weakens the statement. -/
theorem CoreGapAt.mono_delta {ε δ δ' : ℝ} (h : CoreGapAt ε δ) (hδ : δ ≤ δ') : CoreGapAt ε δ' := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdeg hrich
  refine hmain V G hV (fun x => ?_) hrich
  rcases hdeg x with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) h)

/-- Raising the error term weakens the statement. -/
theorem CoreGapAt.mono_eps {ε ε' δ : ℝ} (h : CoreGapAt ε δ) (hε : ε ≤ ε') : CoreGapAt ε' δ := by
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV hdeg _
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  rcases lt_or_ge (ε * (Fintype.card V : ℝ) ^ 2) (nu3star G) with hlt | hge
  · have := hmain V G hV hdeg hlt
    nlinarith
  · have h2 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- **`CoreGapAt` is unconditionally true for `ε ≥ 1/3`**, since `ν₃* ≤ |E|/3 ≤ |V|²/3`. -/
theorem coreGapAt_of_third {ε δ : ℝ} (hε : 1 / 3 ≤ ε) : CoreGapAt ε δ := by
  refine ⟨0, ?_⟩
  intro V _ _ G _ _ _ _
  have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  have h2 : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := edge_card_le_card_sq G
  have h3 : (0 : ℝ) ≤ (nu3 G : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith

/-- **`CoreGapAt` is unconditionally true near the top of the density range.**  For every `ε > 0`
there is `θ < 1` with `CoreGapAt ε θ` — hence, by `CoreGapAt.mono_delta`, `CoreGapAt ε δ` for every
`δ ≥ θ`.  This is the satisfiability witness for the residual: it is a nonempty, non-circular family
of true statements, proved from the nibble, not from the target. -/
theorem coreGapAt_dense (ε : ℝ) (hε : 0 < ε) : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ CoreGapAt ε θ := by
  obtain ⟨θ, hθ0, hθ1, n₀, hmain⟩ := nibbleGap_denseCore ε hε
  exact ⟨θ, hθ0, hθ1, n₀, fun V _ _ G _ hV hdeg _ => hmain V G hV hdeg⟩

/-! ### The reduction -/

/-- **The reduction.**  `NibbleGapResidual` follows from the core residual: delete the edges at all
vertices of positive degree below `(ε/4)|V|` — this costs at most `(ε/4)|V|²` edges, hence at most
that much of the packing gap — and apply the core residual to the resulting graph. -/
theorem nibbleGapResidual_of_coreGapResidual (h : CoreGapResidual) : NibbleGapResidual := by
  intro ε hε θ _ _
  obtain ⟨n₁, hres⟩ := h (ε / 2) (by linarith) (ε / 4) (by linarith)
  refine ⟨n₁, ?_⟩
  intro V _ _ G _ hV _ _
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  obtain ⟨K, hprop, hdel⟩ := exists_core G (t := (ε / 4) * (Fintype.card V : ℝ)) (by positivity)
  have hle : restrictAway G K ≤ G := restrictAway_le G K
  have hgap' : nu3star (restrictAway G K) - (nu3 (restrictAway G K) : ℝ)
      ≤ (ε / 2) * (Fintype.card V : ℝ) ^ 2 := by
    rcases lt_or_ge ((ε / 2) * (Fintype.card V : ℝ) ^ 2) (nu3star (restrictAway G K))
      with hlt | hge
    · exact hres V (restrictAway G K) hV hprop hlt
    · have h2 : (0 : ℝ) ≤ (nu3 (restrictAway G K) : ℝ) := Nat.cast_nonneg _
      linarith
  have hstab := gap_le_core_gap G (restrictAway G K) hle
  nlinarith only [hdel, hstab, hgap']

/-- **`NibbleGapHyp` from the core residual.** -/
theorem nibbleGapHyp_of_coreGapResidual (h : CoreGapResidual) : NibbleGapHyp :=
  nibbleGapHyp_of_residual (nibbleGapResidual_of_coreGapResidual h)

/-- **AX1 from the core residual**, combining with the proved `strongDualityHyp_holds`. -/
theorem ax1_of_coreGapResidual (h : CoreGapResidual) : AX1Statement :=
  ax1_holds_of_residual (nibbleGapResidual_of_coreGapResidual h)

/-- **The Haxell–Rödl packing gap** for triangle hypergraphs: `ν₃*(G) − ν₃(G) = o(|V|²)` for every
graph.  This is the published theorem the whole AX1 chain is an instance of; it is recorded here
only to certify that the residual below it is genuinely true, never used as an input to anything
proved. -/
def HaxellRodlGap : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- **The residual is a special case of Haxell–Rödl**, hence true and not refutable. -/
theorem coreGapResidual_of_haxellRodl (h : HaxellRodlGap) : CoreGapResidual := by
  intro ε hε _ _
  obtain ⟨n₀, hmain⟩ := h ε hε
  exact ⟨n₀, fun V _ _ G _ hV _ _ => hmain V G hV⟩

/-- **The converse reduction.**  `NibbleGapResidual` implies the core residual as well (the dense
instances being supplied by `nibbleGap_denseCore`), so the reformulation is lossless: nothing has
been strengthened, and the two residuals are equivalent. -/
theorem coreGapResidual_of_nibbleGapResidual (h : NibbleGapResidual) : CoreGapResidual := by
  intro ε hε δ _
  obtain ⟨θ, hθ0, hθ1, n₁, hdense⟩ := nibbleGap_denseCore ε hε
  obtain ⟨n₂, hres⟩ := h ε hε θ hθ0 hθ1
  refine ⟨max n₁ n₂, ?_⟩
  intro V _ _ G _ hV hdeg hrich
  by_cases hmin : ∀ x : V, θ * (Fintype.card V : ℝ) ≤ (G.degree x : ℝ)
  · exact hdense V G (le_trans (le_max_left _ _) hV) (fun x => Or.inr (hmin x))
  push Not at hmin
  refine hres V G (le_trans (le_max_right _ _) hV) hmin ?_
  exact lt_of_lt_of_le hrich (nu3star_le_card_triangles G)

end Nibble.AX1

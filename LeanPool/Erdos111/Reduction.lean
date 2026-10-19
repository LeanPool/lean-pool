/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Bridge
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Reduction of Erdős Problem 111 to countable colorings of linear graphs

* **Countable deletion.** If removing a countable set leaves a countably colorable
  graph, the graph is countably colorable: give the removed vertices fresh colors.
* **Packing.** Uncountably many pairwise disjoint finite witnesses with cost above
  `2 K` per vertex include infinitely many with the same size `v` and cost `b`, since
  these are natural numbers. Then `⌊n / v⌋` of them, padded to `n` vertices, cost at least
  `b ⌊n / v⌋ > K n` for `n ≥ 2 v`.
* **The limit.** If `G` is not countably colorable, fix `K` and take a maximal family of
  pairwise disjoint witnesses. If it were countable, the remainder would be `2 K`-linear
  by maximality, hence countably colorable, and so would `G`. So it is uncountable, and
  packing gives `h G n > K n` for all large `n`.
-/

@[expose] public section

open Filter Cardinal
open scoped NNReal

universe u

namespace Erdos111

variable {V : Type u}

/-- A witness costing more than `2 K` per vertex has a vertex. -/
private theorem card_pos_of_lt_edgeCost {K : ℝ} {s : Finset V} {E : Finset (Sym2 V)}
    (hEs : ∀ e ∈ E, ∀ v ∈ e, v ∈ s) (hcost : 2 * K * s.card < edgeCost E) : 0 < s.card := by
  by_contra hs
  have hs' : s = ∅ := Finset.card_eq_zero.1 (by omega)
  have hE : E = ∅ := Finset.eq_empty_of_forall_notMem fun e he => by
    simpa [hs'] using hEs e he _ e.out_fst_mem
  have h0 : edgeCost E = 0 := Nat.eq_zero_of_le_zero
    ((edgeCost_le_monoCount E fun _ => false).trans (by simp [monoCount, hE]))
  simp [hs', h0] at hcost

/-- Relabeling along an embedding does not lower the edge cost. -/
private theorem edgeCost_le_edgeCost_map {W : Type*} (f : W ↪ V) (E : Finset (Sym2 W)) :
    edgeCost E ≤ edgeCost (E.map f.sym2Map) := by
  classical
  refine le_ciInf fun σ => (edgeCost_le_monoCount E (σ ∘ f)).trans_eq ?_
  rw [monoCount, monoCount, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro e _
  induction e using Sym2.ind with
  | _ a b => exact Iff.rfl

/-- Edge sets with pairwise disjoint vertex sets cost at least the sum of their costs. -/
private theorem sum_edgeCost_le_edgeCost_biUnion [DecidableEq (Sym2 V)] {ι : Type*}
    (T : Finset ι) (s : ι → Finset V) (E : ι → Finset (Sym2 V))
    (hdisj : (T : Set ι).PairwiseDisjoint s) (hEs : ∀ i, ∀ e ∈ E i, ∀ v ∈ e, v ∈ s i) :
    ∑ i ∈ T, edgeCost (E i) ≤ edgeCost (T.biUnion E) := by
  classical
  refine le_ciInf fun σ => ?_
  rw [monoCount, Finset.filter_biUnion, Finset.card_biUnion]
  · exact Finset.sum_le_sum fun i _ => edgeCost_le_monoCount (E i) σ
  · intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro e hei hej
    exact Finset.disjoint_left.1 (hdisj hi hj hij)
      (hEs i e (Finset.mem_filter.1 hei).1 _ e.out_fst_mem)
      (hEs j e (Finset.mem_filter.1 hej).1 _ e.out_fst_mem)

/-- Countable deletion. -/
theorem nonempty_coloring_of_countable_compl {G : SimpleGraph V} {S : Set V}
    (hS : S.Countable) (h : Nonempty ((G.induce Sᶜ).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  obtain ⟨c⟩ := h
  have := hS.to_subtype
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat S
  -- Odd colors for the removed vertices, even colors for the rest.
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if hv : v ∈ S then 2 * f ⟨v, hv⟩ + 1 else 2 * c ⟨v, hv⟩) ?_⟩
  intro a b hab
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp only [ha, hb, ↓reduceDIte]
  · intro heq
    exact hab.ne (congrArg Subtype.val (hf (by omega : f ⟨a, ha⟩ = f ⟨b, hb⟩)))
  · omega
  · omega
  · intro heq
    exact c.valid (show (G.induce Sᶜ).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab) (by omega)

/-- Packing. -/
theorem eventually_lt_h_of_uncountable {G : SimpleGraph V} {ι : Type*} [Uncountable ι]
    (K : ℝ) (s : ι → Finset V) (E : ι → Finset (Sym2 V))
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j)) (hE : ∀ i, ↑(E i) ⊆ G.edgeSet)
    (hEs : ∀ i, ∀ e ∈ E i, ∀ v ∈ e, v ∈ s i)
    (hcost : ∀ i, 2 * K * (s i).card < edgeCost (E i)) :
    ∀ᶠ n : ℕ in atTop, K * n < h G n := by
  classical
  -- Infinitely many witnesses share their size `v` and cost `b`.
  obtain ⟨⟨v, b⟩, hp⟩ : ∃ p : ℕ × ℕ, {i | ((s i).card, edgeCost (E i)) = p}.Infinite := by
    by_contra hfin
    simp only [not_exists, Set.not_infinite] at hfin
    apply not_countable (α := ι)
    rw [← Set.countable_univ_iff]
    have hU : (Set.univ : Set ι) = ⋃ p : ℕ × ℕ, {i | ((s i).card, edgeCost (E i)) = p} := by
      ext i
      simp
    rw [hU]
    exact Set.countable_iUnion fun p => (hfin p).countable
  have hfib : ∀ i ∈ {i | ((s i).card, edgeCost (E i)) = (v, b)}, (s i).card = v ∧
      edgeCost (E i) = b := fun i hi => by simpa using hi
  obtain ⟨i₀, hi₀⟩ := hp.nonempty
  have hv : 0 < v := (hfib i₀ hi₀).1 ▸ card_pos_of_lt_edgeCost (hEs i₀) (hcost i₀)
  have hb : 2 * K * v < b := by
    have := hcost i₀
    rwa [(hfib i₀ hi₀).1, (hfib i₀ hi₀).2] at this
  have hpd : ∀ T₀ : Finset ι, (T₀ : Set ι).PairwiseDisjoint s := fun T₀ i _ j _ hij => hdisj hij
  rw [Filter.eventually_atTop]
  refine ⟨2 * v, fun n hn => ?_⟩
  -- Take `q = n / v` of `n` such witnesses and pad their vertices to `n`.
  set q := n / v with hq
  obtain ⟨T', hT'F, hT'⟩ := hp.exists_subset_card_eq n
  obtain ⟨T, hTT', hT⟩ := Finset.exists_subset_card_eq (s := T') (n := q)
    (by rw [hT']; exact Nat.div_le_self n v)
  have hcardU : ∀ T₀ ⊆ T', (T₀.biUnion s).card = T₀.card * v := by
    intro T₀ hT₀
    rw [Finset.card_biUnion (hpd T₀), Finset.sum_const_nat fun i hi => (hfib i (hT'F (hT₀ hi))).1]
  obtain ⟨s', hUs', -, hs'⟩ := Finset.exists_subsuperset_card_eq (n := n)
    (Finset.biUnion_subset_biUnion_of_subset_left s hTT')
    (by rw [hcardU T hTT', hT]; exact Nat.div_mul_le_self n v)
    (by rw [hcardU T' le_rfl, hT']; exact Nat.le_mul_of_pos_right n hv)
  have hE' : ↑(T.biUnion E) ⊆ G.edgeSet := by
    simp only [Finset.coe_biUnion, Set.iUnion_subset_iff]
    exact fun i _ => hE i
  have hEs' : ∀ e ∈ T.biUnion E, ∀ u ∈ e, u ∈ s' := by
    intro e he u hu
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.1 he
    exact hUs' (Finset.mem_biUnion.2 ⟨i, hi, hEs i e hei u hu⟩)
  have hcostE' : q * b ≤ edgeCost (T.biUnion E) := by
    calc q * b = ∑ i ∈ T, edgeCost (E i) := by
          rw [Finset.sum_const_nat fun i hi => (hfib i (hT'F (hTT' hi))).2, hT]
      _ ≤ _ := sum_edgeCost_le_edgeCost_biUnion T s E (hpd T) hEs
  have hh := edgeCost_le_h hE' hEs'
  rw [hs'] at hh
  -- Then `n < 2 q v`, so `K n < q b`.
  have hq1 : 1 ≤ q := (Nat.le_div_iff_mul_le hv).2 (by omega)
  have hlt : n < v * q + v := by
    have h1 := Nat.div_add_mod n v
    rw [← hq] at h1
    have h2 := Nat.mod_lt n hv
    omega
  have hnR : (n : ℝ) ≤ 2 * q * v := by
    have h1 : (n : ℝ) < v * q + v := by exact_mod_cast hlt
    have h2 : (v : ℝ) ≤ v * q := by exact_mod_cast Nat.le_mul_of_pos_right v hq1
    linarith
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hbig : K * n < q * b := by
    rcases le_or_gt 0 K with hK | hK
    · calc K * n ≤ K * (2 * q * v) := mul_le_mul_of_nonneg_left hnR hK
        _ = q * (2 * K * v) := by ring
        _ < q * b := mul_lt_mul_of_pos_left hb (by linarith)
    · have : (0 : ℝ) ≤ q * b := by positivity
      nlinarith
  calc K * n < q * b := hbig
    _ ≤ h G n := by exact_mod_cast hcostE'.trans hh

/-- If every linear graph is countably colorable, then `h G n / n → ∞` for every graph `G`
that is not countably colorable. -/
theorem tendsto_of_isEmpty_coloring
    (hmain : ∀ (W : Type u) (H : SimpleGraph W) (C : ℝ≥0), Linear H C →
      Nonempty (H.Coloring ℕ))
    (G : SimpleGraph V) (hG : IsEmpty (G.Coloring ℕ)) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop := by
  classical
  suffices hK : ∀ K : ℝ, ∀ᶠ n : ℕ in atTop, K * n < h G n by
    rw [Filter.tendsto_atTop]
    intro K
    filter_upwards [hK K, Filter.eventually_gt_atTop 0] with n hn hn0
    rw [le_div_iff₀ (by exact_mod_cast hn0)]
    exact hn.le
  intro K
  -- The witnesses: edge sets of `G` with ends in `s` costing more than `2 K |s|`.
  let W : Set (Finset V × Finset (Sym2 V)) := {w | ↑w.2 ⊆ G.edgeSet ∧
    (∀ e ∈ w.2, ∀ v ∈ e, v ∈ w.1) ∧ 2 * K * w.1.card < edgeCost w.2}
  let 𝒮 : Set (Set (Finset V × Finset (Sym2 V))) :=
    {𝓕 | 𝓕 ⊆ W ∧ 𝓕.Pairwise fun x y => Disjoint x.1 y.1}
  -- A maximal family of witnesses with pairwise disjoint vertex sets.
  obtain ⟨𝓕, h𝓕⟩ := zorn_subset 𝒮 fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨Set.sUnion_subset fun 𝓖 h𝓖 => (hc h𝓖).1, ?_⟩,
      fun 𝓖 h𝓖 => Set.subset_sUnion_of_mem h𝓖⟩
    rintro x ⟨𝓖, h𝓖, hx⟩ y ⟨𝓗, h𝓗, hy⟩ hxy
    rcases hchain.total h𝓖 h𝓗 with h | h
    · exact (hc h𝓗).2 (h hx) hy hxy
    · exact (hc h𝓖).2 hx (h hy) hxy
  -- If it were countable, the rest of `G` would be `2 K`-linear, so `G` would be
  -- countably colorable.
  have hF : ¬𝓕.Countable := by
    intro hcount
    set S : Set V := ⋃ x ∈ 𝓕, (x.1 : Set V) with hS
    have hScount : S.Countable := hcount.biUnion fun x _ => x.1.countable_toSet
    refine hG.false (nonempty_coloring_of_countable_compl hScount
      (hmain _ (G.induce Sᶜ) (2 * K).toNNReal ?_)).some
    intro s' E' hE' hEs'
    by_contra hlt
    rw [not_le] at hlt
    let f : ↥Sᶜ ↪ V := Function.Embedding.subtype _
    let w : Finset V × Finset (Sym2 V) := (s'.map f, E'.map f.sym2Map)
    have hw : w ∈ W := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 he)
        induction e' using Sym2.ind with
        | _ a b => exact hE' he'
      · intro e he u hu
        obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
        rw [Function.Embedding.sym2Map_apply] at hu
        obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.1 hu
        exact Finset.mem_map_of_mem f (hEs' e' he' a ha)
      · have h1 : ((2 * K).toNNReal * s'.card : ℝ) < edgeCost E' := by exact_mod_cast hlt
        have h2 : (edgeCost E' : ℝ) ≤ edgeCost (E'.map f.sym2Map) := by
          exact_mod_cast edgeCost_le_edgeCost_map f E'
        have h3 : 2 * K ≤ ((2 * K).toNNReal : ℝ) := by
          rw [Real.coe_toNNReal']
          exact le_max_left _ _
        simp only [w, Finset.card_map]
        calc 2 * K * s'.card ≤ (2 * K).toNNReal * s'.card :=
              mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
          _ < edgeCost E' := h1
          _ ≤ edgeCost (E'.map f.sym2Map) := h2
    have hdisjw : ∀ x ∈ 𝓕, Disjoint x.1 w.1 := by
      intro x hx
      rw [Finset.disjoint_left]
      intro u hux huw
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 huw
      exact a.2 (Set.mem_biUnion hx hux)
    have hins : insert w 𝓕 ∈ 𝒮 := by
      refine ⟨Set.insert_subset hw h𝓕.1.1, ?_⟩
      rw [Set.pairwise_insert]
      exact ⟨h𝓕.1.2, fun x hx _ => ⟨(hdisjw x hx).symm, hdisjw x hx⟩⟩
    have hw𝓕 : w ∈ 𝓕 :=
      (h𝓕.2 hins (Set.subset_insert _ _) : insert w 𝓕 ⊆ 𝓕) (Set.mem_insert _ _)
    have hpos := card_pos_of_lt_edgeCost hw.2.1 hw.2.2
    have hempty := hdisjw w hw𝓕
    rw [disjoint_self, Finset.bot_eq_empty] at hempty
    rw [hempty] at hpos
    simp at hpos
  have : Uncountable 𝓕 := ⟨hF⟩
  exact eventually_lt_h_of_uncountable K (fun x : 𝓕 => x.1.1) (fun x => x.1.2)
    (fun x y hxy => h𝓕.1.2 x.2 y.2 (Subtype.coe_ne_coe.2 hxy)) (fun x => (h𝓕.1.1 x.2).1)
    (fun x => (h𝓕.1.1 x.2).2.1) (fun x => (h𝓕.1.1 x.2).2.2)

/-- A graph of chromatic number `ℵ₁` is not countably colorable. -/
theorem isEmpty_coloring_of_chromaticCardinal {G : SimpleGraph V}
    (hG : chromaticCardinal G = ℵ₁) : IsEmpty (G.Coloring ℕ) := by
  refine ⟨fun c => ?_⟩
  let c' : G.Coloring (ULift.{u} ℕ) := SimpleGraph.Coloring.mk (fun v => ULift.up (c v))
    fun hab heq => c.valid hab (congrArg ULift.down heq)
  have hle : chromaticCardinal G ≤ ℵ₀ := csInf_le' ⟨ULift.{u} ℕ, by simp, ⟨c'⟩⟩
  rw [hG] at hle
  exact lt_irrefl _ (aleph0_lt_aleph_one.trans_le hle)

end Erdos111

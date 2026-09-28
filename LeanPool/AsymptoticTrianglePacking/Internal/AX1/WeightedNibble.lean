/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — fractional-packing bounds and a near-regular weighted nibble

This file adds to the AX1 chain (`Nibble.CoreGapAX1`) in two ways.

* **An unconditional improvement of the proved range.**  A maximum triangle packing covers `3ν₃`
  edges that meet every triangle, so every fractional packing has weight at most `3ν₃`
  (`Nibble.nu3star_le_three_nu3`).  With `ν₃* ≤ |E|/3 ≤ |V|²/6` this gives the hypothesis-free bound
  `ν₃* − ν₃ ≤ |V|²/9` (`Nibble.nu3star_sub_nu3_le_ninth`), hence `Nibble.AX1.CoreGapAt ε δ`
  for every
  `ε ≥ 1/9` (`Nibble.AX1.coreGapAt_of_ninth`) — strictly more than the previously proved `ε ≥ 1/3`.

* **A near-regular weighted consequence.** `Nibble.fracMatching_sum_le` bounds the total weight
  of a fractional matching in a uniform hypergraph. Combining it with the proved regular nibble
  yields `Nibble.fracNibble_nearlyRegular`. This result is not an unconditional weighted nibble:
  it retains the near-regularity hypotheses of the regular theorem.

See `RESIDUAL.md` for the exact state of the obligation.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapAX1

/-! # WeightedNibble -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The maximum in the definition of `ν₃` is attained: there is a triangle packing of size
exactly `ν₃ G`. -/
theorem exists_maximum_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ M : Finset (Finset (Finset V)), IsMatching (triangleHypergraphE G) M ∧ M.card = nu3 G := by
  classical
  set S := (triangleHypergraphE G).powerset.filter
    (fun M => IsMatching (triangleHypergraphE G) M) with hS
  have hne : S.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨M, hMS, hsup⟩ := Finset.exists_mem_eq_sup S hne Finset.card
  rw [hS, Finset.mem_filter] at hMS
  exact ⟨M, hMS.2, hsup.symm⟩

/-- Every triangle of `G` shares an edge with a maximum packing: otherwise it could be added. -/
theorem exists_mem_of_maximum_packing (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (Finset V))} (hM : IsMatching (triangleHypergraphE G) M)
    (hcard : M.card = nu3 G) {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE G) :
    ∃ e ∈ M.biUnion id, e ∈ T := by
  classical
  by_contra hcon
  push Not at hcon
  have hdisj : ∀ m ∈ M, Disjoint T m := by
    intro m hm
    rw [Finset.disjoint_left]
    intro e heT hem
    exact hcon e (Finset.mem_biUnion.mpr ⟨m, hm, hem⟩) heT
  have hTcard : T.card = 3 := triangleHypergraphE_uniform G T hT
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hTM : T ∉ M := by
    intro hTM
    obtain ⟨e, he⟩ := hTne
    exact (Finset.disjoint_left.mp (hdisj T hTM) he) he
  have hM' : IsMatching (triangleHypergraphE G) (insert T M) := by
    refine ⟨Finset.insert_subset hT hM.subset, ?_⟩
    intro e he f hf hef
    rw [Finset.mem_insert] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · exact absurd rfl hef
      · exact hdisj f hf
    · rcases hf with rfl | hf
      · exact (hdisj e he).symm
      · exact hM.disjoint e he f hf hef
  have hle : (insert T M).card ≤ nu3 G := nu3_ge G hM'
  rw [Finset.card_insert_of_notMem hTM, hcard] at hle
  omega

/-- **`ν₃* ≤ 3·ν₃`.**  The `3ν₃` edges covered by a maximum triangle packing form a triangle cover,
and the total weight of any fractional packing is at most the number of edges in a cover. -/
theorem nu3star_le_three_nu3 (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star G ≤ 3 * (nu3 G : ℝ) := by
  classical
  obtain ⟨M, hM, hcard⟩ := exists_maximum_packing G
  set F : Finset (Finset V) := M.biUnion id with hF
  have hFcard : (F.card : ℝ) ≤ 3 * (nu3 G : ℝ) := by
    have h1 : F.card ≤ ∑ m ∈ M, (id m).card := Finset.card_biUnion_le
    have h2 : ∑ m ∈ M, (id m).card = 3 * M.card := by
      simp only [id_eq]
      rw [Finset.sum_congr rfl (fun m hm => triangleHypergraphE_uniform G m (hM.subset hm)),
        Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h2, hcard] at h1
    exact_mod_cast h1
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨hnn, -, hcon⟩ := hw
  have key : ∀ T ∈ triangleHypergraphE G,
      w T ≤ ∑ e ∈ F, (if e ∈ T then w T else 0) := by
    intro T hT
    obtain ⟨e₀, he₀F, he₀T⟩ := exists_mem_of_maximum_packing G hM hcard hT
    calc w T = (if e₀ ∈ T then w T else 0) := by simp [he₀T]
      _ ≤ ∑ e ∈ F, (if e ∈ T then w T else 0) := by
          refine Finset.single_le_sum (f := fun e => if e ∈ T then w T else 0) ?_ he₀F
          intro e _
          by_cases h : e ∈ T <;> simp [h, hnn T]
  calc ∑ T ∈ triangleHypergraphE G, w T
      ≤ ∑ T ∈ triangleHypergraphE G, ∑ e ∈ F, (if e ∈ T then w T else 0) :=
        Finset.sum_le_sum key
    _ = ∑ e ∈ F, ∑ T ∈ triangleHypergraphE G, (if e ∈ T then w T else 0) := Finset.sum_comm
    _ = ∑ e ∈ F, ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w T :=
        Finset.sum_congr rfl (fun e _ => by rw [Finset.sum_filter])
    _ ≤ ∑ _e ∈ F, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hcon e)
    _ = (F.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 3 * (nu3 G : ℝ) := hFcard

/-- `|E(G)| ≤ |V|²/2`, sharpening `Nibble.YusterE.edge_card_le_card_sq`. -/
theorem edge_card_le_half_card_sq (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  classical
  have hle : (G.cliqueFinset 2).card ≤ (Fintype.card V).choose 2 := by
    have hsub : (G.cliqueFinset 2).card ≤
        (Finset.univ.powersetCard 2 : Finset (Finset V)).card := by
      apply Finset.card_le_card
      intro e he
      rw [SimpleGraph.mem_cliqueFinset_iff] at he
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ e, he.card_eq⟩
    rwa [Finset.card_powersetCard, Finset.card_univ] at hsub
  have hchoose : 2 * ((Fintype.card V).choose 2) ≤ (Fintype.card V) ^ 2 := by
    rw [Nat.choose_two_right, pow_two]
    calc 2 * (Fintype.card V * (Fintype.card V - 1) / 2)
        ≤ Fintype.card V * (Fintype.card V - 1) := Nat.mul_div_le _ 2
      _ ≤ Fintype.card V * Fintype.card V := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h1 : (2 : ℝ) * ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have : (2 * (G.cliqueFinset 2).card : ℝ) ≤ ((Fintype.card V) ^ 2 : ℝ) := by
      exact_mod_cast le_trans (Nat.mul_le_mul_left 2 hle) hchoose
    linarith
  linarith

/-- **An unconditional `n²/9` bound on the packing gap.**  Since a maximum packing covers a set of
`3ν₃` edges meeting every triangle, `ν₃* ≤ 3ν₃`, so the gap is at most `⅔ν₃*`; and
`ν₃* ≤ |E|/3 ≤ |V|²/6`. -/
theorem nu3star_sub_nu3_le_ninth (G : SimpleGraph V) [DecidableRel G.Adj] :
    nu3star G - (nu3 G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 9 := by
  have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  have h2 := edge_card_le_half_card_sq G
  have h3 := nu3star_le_three_nu3 G
  linarith

/-- **`CoreGapAt ε δ` for every `ε ≥ 1/9`**, unconditionally — a genuine extension of the previously
proved range `ε ≥ 1/3` (`Nibble.AX1.coreGapAt_of_third`). -/
theorem AX1.coreGapAt_of_ninth {ε δ : ℝ} (hε : 1 / 9 ≤ ε) : AX1.CoreGapAt ε δ := by
  refine ⟨0, ?_⟩
  intro V _ _ G _ _ _ _
  have h := nu3star_sub_nu3_le_ninth G
  have hn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith

/-! ### The degree of the edge-based triangle hypergraph -/

/-- **The triangle hypergraph has maximum degree at most `|V|`**: a triangle through a fixed edge
`e` is `insert v e` for one of the `|V|` vertices `v`. -/
theorem triangleHypergraphE_degree_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) :
    (Hypergraph.degree (triangleHypergraphE G) e : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  rw [triangleHypergraphE_degree]
  have hsub : ((G.cliqueFinset 3).filter (fun t => e ∈ t.powersetCard 2))
      ⊆ Finset.univ.image (fun v : V => insert v e) := by
    intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff, Finset.mem_powersetCard] at ht
    obtain ⟨ht3, hesub, hecard⟩ := ht
    have hne : (t \ e).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hesub, ht3.card_eq, hecard]
      norm_num
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_sdiff] at hv
    have hins : insert v e ⊆ t := Finset.insert_subset hv.1 hesub
    have hcard : (insert v e).card = t.card := by
      rw [Finset.card_insert_of_notMem hv.2, hecard, ht3.card_eq]
    have heq : insert v e = t := Finset.eq_of_subset_of_card_le hins (le_of_eq hcard.symm)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, heq⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.image (fun v : V => insert v e)).card ≤ Fintype.card V := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset V)) (f := fun v => insert v e)
  exact_mod_cast le_trans h1 h2

/-- `ν₃* ≥ 0`. -/
theorem nu3star_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ nu3star G :=
  le_csSup (nu3star_bddAbove G) ⟨fun _ => 0, isFracPacking_zero G, by simp⟩

/-! ### A proved instance of the weighted nibble: the near-regular case -/

/-- **Every fractional matching of an `r`-uniform hypergraph has total weight at most `|W|/r`.** -/
theorem fracMatching_sum_le {W : Type} [Fintype W] [DecidableEq W] {H : Finset (Finset W)}
    {r : ℕ} (hr : IsUniform H r) {w : Finset W → ℝ}
    (hcon : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) :
    (r : ℝ) * (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) := by
  classical
  have expand : ∀ T ∈ H, ∑ v : W, (if v ∈ T then w T else 0) = (r : ℝ) * w T := by
    intro T hT
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hr T hT, nsmul_eq_mul]
  calc (r : ℝ) * (∑ T ∈ H, w T)
      = ∑ T ∈ H, ∑ v : W, (if v ∈ T then w T else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T hT => (expand T hT).symm)
    _ = ∑ v : W, ∑ T ∈ H, (if v ∈ T then w T else 0) := Finset.sum_comm
    _ = ∑ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T :=
        Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_filter])
    _ ≤ ∑ _v : W, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hcon v)
    _ = (Fintype.card W : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]

/-- **The weighted nibble holds for nearly regular hypergraphs**, as an immediate consequence of the
proved regular nibble `Nibble.nibbleTheoremMostCeil_holds`: the matching it produces already covers
all but a `β`-fraction of the ground set, and *every* fractional matching has total weight at most
`|W|/r`. This conclusion relies on the stated near-regularity hypotheses. -/
theorem fracNibble_nearlyRegular (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ) (d : ℝ),
        0 < d → d₀ ≤ d → IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
        (∀ x : W, (Hypergraph.degree H x : ℝ) ≤ (1 + μ) * d) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, ?_⟩
  intro W _ _ H w d hd hd0 hunif hreg hcod hceil hnn hcon
  obtain ⟨M, hM, hMcard⟩ := hmain H d hd hd0 hunif hreg hcod hceil
  refine ⟨M, hM, ?_⟩
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  have hsum : (∑ T ∈ H, w T) ≤ (Fintype.card W : ℝ) / r := by
    rw [le_div_iff₀ hrpos, mul_comm]
    exact fracMatching_sum_le hunif hcon
  rcases le_or_gt β 1 with h1 | h1
  · exact le_trans (mul_le_mul_of_nonneg_left hsum (by linarith)) hMcard
  · have hnn' : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hnn T)
    have : (1 - β) * (∑ T ∈ H, w T) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn'
    exact le_trans this (Nat.cast_nonneg _)

end Nibble

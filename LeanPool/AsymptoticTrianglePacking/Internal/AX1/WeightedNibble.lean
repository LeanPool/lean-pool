/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the weighted (fractional) nibble, and what it gives for AX1

This file adds to the AX1 chain (`Nibble.CoreGapAX1`) in two independent ways.

* **An unconditional improvement of the proved range.**  A maximum triangle packing covers `3ν₃`
  edges that meet every triangle, so every fractional packing has weight at most `3ν₃`
  (`Nibble.nu3star_le_three_nu3`).  With `ν₃* ≤ |E|/3 ≤ |V|²/6` this gives the hypothesis-free bound
  `ν₃* − ν₃ ≤ |V|²/9` (`Nibble.nu3star_sub_nu3_le_ninth`), hence `Nibble.AX1.CoreGapAt ε δ`
  for every
  `ε ≥ 1/9` (`Nibble.AX1.coreGapAt_of_ninth`) — strictly more than the previously proved `ε ≥ 1/3`.

* **The residual, isolated as a reusable hypergraph statement.**
  `Nibble.FracNibbleTheorem` is the weighted / fractional nibble (Kahn's linear-programming form of
  the Frankl–Rödl–Pippenger theorem): an `r`-uniform hypergraph of maximum degree `≤ D` and codegree
  `≤ γD` carrying a fractional matching `w` has an integer matching of size `≥ (1−β)∑w`.  No
  near-regularity is assumed — the weighting plays the role of the regular measure — so this is not
  the refuted near-regularity obligation.  From it the whole AX1 packing gap follows for *every*
  graph (`Nibble.AX1.haxellRodlGap_of_fracNibble`), hence `Nibble.AX1.CoreGapResidual`
  (`Nibble.AX1.coreGapResidual_of_fracNibble`), the triangle hypergraph being `3`-uniform of
  maximum degree `≤ |V|` (`Nibble.triangleHypergraphE_degree_le_card`) and codegree `≤ 1`.
  `Nibble.fracNibble_nearlyRegular` proves the statement for nearly regular hypergraphs from the
  already proved regular nibble, which certifies that the residual is a genuine (non-vacuous,
  non-circular) strengthening.

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

/-! ### The weighted (fractional) nibble -/

/-- **The weighted / fractional nibble** (Kahn's linear-programming form of the
Frankl–Rödl–Pippenger theorem).  For every uniformity `r ≥ 2` and every tolerance `β > 0` there are
a codegree tolerance `γ > 0` and a degree scale `D₀` such that: every `r`-uniform hypergraph `H` of
maximum degree at most `D ≥ D₀` and maximum codegree at most `γD`, equipped with a fractional
matching `w` (nonnegative weights supported on `H`, total weight through every vertex at most `1`),
contains an (integer) matching of size at least `(1-β)∑ w`.

Unlike the regular nibble `Nibble.NibbleTheoremMostCeil` this makes no near-regularity assumption:
the weighting `w` plays the role of the regular measure, so degree-irregular hypergraphs are
covered.  It is exactly the input needed to turn a fractional decomposition into an approximate
integer one, and, as `Nibble.AX1.haxellRodlGap_of_fracNibble` below shows, it closes the AX1 packing
gap outright. -/
def FracNibbleTheorem : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ) (D : ℝ),
      D₀ ≤ D → IsUniform H r →
      (∀ T, 0 ≤ w T) → (∀ T ∉ H, w T = 0) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ v : W, (Hypergraph.degree H v : ℝ) ≤ D) →
      (∀ x y : W, x ≠ y → (Hypergraph.codegree H x y : ℝ) ≤ γ * D) →
      ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- **The weighted nibble closes the packing gap.**  Applied to the edge-based triangle hypergraph
of a graph on `n` vertices — which is `3`-uniform, has maximum degree at most `n` and codegree at
most `1` — with a near-optimal fractional triangle packing as its weighting, it yields
`ν₃ ≥ (1-β)(ν₃* - 1)`, hence `ν₃* - ν₃ ≤ εn²` for large `n`.  No regularity or degree hypothesis on
the graph is used. -/
theorem AX1.haxellRodlGap_of_fracNibble (h : FracNibbleTheorem) : AX1.HaxellRodlGap := by
  intro ε hε
  obtain ⟨γ, hγ, D₀, hD₀, hmain⟩ := h 3 (by norm_num) (min 1 (3 * ε))
    (lt_min one_pos (by linarith))
  set β : ℝ := min 1 (3 * ε) with hβdef
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβ3 : β ≤ 3 * ε := min_le_right _ _
  refine ⟨max ⌈D₀⌉₊ (max ⌈1 / γ⌉₊ ⌈2 / ε⌉₊), ?_⟩
  intro V _ _ G _ hV
  have hn0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hD : D₀ ≤ (Fintype.card V : ℝ) := by
    have hc : (⌈D₀⌉₊ : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hV
    exact le_trans (Nat.le_ceil _) hc
  have hginv : 1 / γ ≤ (Fintype.card V : ℝ) := by
    have hc : (⌈1 / γ⌉₊ : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hV
    exact le_trans (Nat.le_ceil _) hc
  have heps : 2 / ε ≤ (Fintype.card V : ℝ) := by
    have hc : (⌈2 / ε⌉₊ : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hV
    exact le_trans (Nat.le_ceil _) hc
  have hgD : (1 : ℝ) ≤ γ * (Fintype.card V : ℝ) := by
    rw [div_le_iff₀ hγ] at hginv
    linarith
  obtain ⟨x, hxmem, hxlt⟩ := exists_lt_of_lt_csSup
    (⟨0, ⟨fun _ => 0, isFracPacking_zero G, by simp⟩⟩ :
      Set.Nonempty {x : ℝ | ∃ w, IsFracPacking G w ∧ x = ∑ T ∈ triangleHypergraphE G, w T})
    (show nu3star G - 1 < nu3star G by linarith)
  obtain ⟨w, ⟨hnn, hzero, hcon⟩, rfl⟩ := hxmem
  obtain ⟨M, hM, hMcard⟩ := hmain (triangleHypergraphE G) w ((Fintype.card V : ℝ))
    hD (triangleHypergraphE_uniform G) hnn hzero hcon
    (fun e => triangleHypergraphE_degree_le_card G e)
    (fun e e' hee => by
      have h1 : (Hypergraph.codegree (triangleHypergraphE G) e e' : ℝ) ≤ 1 := by
        exact_mod_cast triangleHypergraphE_codegree_le_one G hee
      linarith)
  have hnu3 : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast nu3_ge G hM
  have hstar : nu3star G ≤ (Fintype.card V : ℝ) ^ 2 / 6 := by
    have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
    have h2 := edge_card_le_half_card_sq G
    linarith
  have hstar0 : 0 ≤ nu3star G := nu3star_nonneg G
  have h1eps : 1 ≤ ε * (Fintype.card V : ℝ) ^ 2 / 2 := by
    have hnpos : 0 < (Fintype.card V : ℝ) := lt_of_lt_of_le (by positivity) heps
    have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
      have : 1 ≤ Fintype.card V := by exact_mod_cast hnpos
      exact_mod_cast this
    have h2 : 2 ≤ ε * (Fintype.card V : ℝ) := by
      rw [div_le_iff₀ hε] at heps
      linarith
    nlinarith
  have hsum : (1 - β) * (nu3star G - 1) ≤ (M.card : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (le_of_lt hxlt) (by linarith)) hMcard
  nlinarith [hnu3, hsum, hstar, hstar0, h1eps]

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
`|W|/r`.  This is a non-circular satisfiability witness for `Nibble.FracNibbleTheorem`: the residual
is a genuine strengthening of a proved theorem, not an unfalsifiable statement. -/
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

/-- **`CoreGapResidual` from the weighted nibble.**  Composing
`Nibble.AX1.haxellRodlGap_of_fracNibble` with the (already proved) reduction
`Nibble.AX1.coreGapResidual_of_haxellRodl`. -/
theorem AX1.coreGapResidual_of_fracNibble (h : FracNibbleTheorem) : AX1.CoreGapResidual :=
  AX1.coreGapResidual_of_haxellRodl (AX1.haxellRodlGap_of_fracNibble h)

end Nibble

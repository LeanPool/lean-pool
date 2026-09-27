/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the near-complete branch, and a universal packing-gap constant below `1/9`

The best previously proved *hypothesis-free* bound on the triangle packing gap is
`Nibble.nu3star_sub_nu3_le_ninth`: `ν₃* − ν₃ ≤ |V|²/9`, from `ν₃* ≤ |E|/3 ≤ |V|²/6` and
`ν₃* ≤ 3ν₃`.  Its extremal case is the *complete* graph, where `|E| = |V|²/2` — and complete-ish
graphs are exactly the ones the dense nibble branch handles.  This file exploits that tension.

* `Nibble.AX1.gap_le_of_near_complete` — **the near-complete branch**: for every `ε > 0` there is
  `η > 0` such that every large graph with at least `(1/2 − η)|V|²` edges has packing gap at most
  `ε|V|²`.  Deleting the edges at the (few) vertices of degree below `(1+θ)|V|/2` costs at most
  `(ε/4)|V|²` edges and produces an isolated-or-`θ|V|`-dense graph, which is
  `Nibble.AX1.nibbleGap_of_dense_core`.

* `Nibble.AX1.exists_gap_const_lt_ninth` — the consequence: there is a constant `c < 1/9` with
  `ν₃* − ν₃ ≤ c|V|²` for all large graphs; sparse graphs are handled by `ν₃* ≤ |E|/3` and
  `ν₃* ≤ 3ν₃`, near-complete ones by the branch above.

* `Nibble.AX1.coreGapAt_of_lt_ninth` — hence `Nibble.AX1.CoreGapAt ε δ` for every `δ` and every
  `ε ≥ c`, strictly improving `Nibble.AX1.coreGapAt_of_ninth` (`ε ≥ 1/9`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRemoval
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.WeightedNibble

/-! # CoreGapNearComplete -/

@[expose] public section

open Finset SimpleGraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Edge counting -/

/-- The number of `2`-cliques is at most the number of edges. -/
theorem card_clique2_le_card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueFinset 2).card : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  classical
  have hsurj : Set.SurjOn (fun e : Sym2 V => e.toFinset) (G.edgeFinset : Set (Sym2 V))
      ((G.cliqueFinset 2 : Finset (Finset V)) : Set (Finset V)) := by
    intro f hf
    simp only [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at hf
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hf.card_eq
    have hadj : G.Adj a b := hf.1 (by simp) (by simp) hab
    refine ⟨s(a, b), ?_, ?_⟩
    · simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset]
      exact hadj
    · ext x; simp [Sym2.mem_toFinset]
  exact_mod_cast Finset.card_le_card_of_surjOn _ hsurj

/-- **Few vertices of low degree in an edge-rich graph.**  With `L` the set of vertices of degree
below `t`, one has `|L|·(|V| − t) ≤ |V|² − 2|E|`. -/
theorem card_lowDeg_mul_le (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) :
    (((univ : Finset V).filter (fun v => (G.degree v : ℝ) < t)).card : ℝ)
        * ((Fintype.card V : ℝ) - t)
      ≤ (Fintype.card V : ℝ) ^ 2 - 2 * (G.edgeFinset.card : ℝ) := by
  classical
  set L : Finset V := (univ : Finset V).filter (fun v => (G.degree v : ℝ) < t) with hL
  have hsum : ∑ v : V, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    have := SimpleGraph.sum_degrees_eq_twice_card_edges G
    have h2 : ((∑ v : V, G.degree v : ℕ) : ℝ) = ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at h2
    simpa using h2
  have hsplit : ∑ v ∈ L, (G.degree v : ℝ) + ∑ v ∈ Lᶜ, (G.degree v : ℝ)
      = ∑ v : V, (G.degree v : ℝ) := by
    rw [← Finset.sum_add_sum_compl L (fun v => (G.degree v : ℝ))]
  have hL1 : ∑ v ∈ L, (G.degree v : ℝ) ≤ (L.card : ℝ) * t := by
    calc ∑ v ∈ L, (G.degree v : ℝ) ≤ ∑ _v ∈ L, t := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          exact le_of_lt (Finset.mem_filter.mp hv).2
      _ = (L.card : ℝ) * t := by rw [Finset.sum_const, nsmul_eq_mul]
  have hdegle : ∀ v : V, (G.degree v : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro v
    have := SimpleGraph.degree_lt_card_verts (G := G) v
    exact le_of_lt (by exact_mod_cast this)
  have hL2 : ∑ v ∈ Lᶜ, (G.degree v : ℝ) ≤ ((Lᶜ).card : ℝ) * (Fintype.card V : ℝ) := by
    calc ∑ v ∈ Lᶜ, (G.degree v : ℝ) ≤ ∑ _v ∈ Lᶜ, (Fintype.card V : ℝ) :=
          Finset.sum_le_sum (fun v _ => hdegle v)
      _ = ((Lᶜ).card : ℝ) * (Fintype.card V : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcompl : ((Lᶜ).card : ℝ) = (Fintype.card V : ℝ) - (L.card : ℝ) := by
    have : (Lᶜ).card = Fintype.card V - L.card := by
      rw [Finset.card_compl]
    have hle : L.card ≤ Fintype.card V := Finset.card_le_univ L
    rw [this, Nat.cast_sub hle]
  rw [hcompl] at hL2
  linarith only [hsum, hsplit, hL1, hL2]

/-! ### The deletion at a set of vertices -/

/-- Deleting all edges at the vertices of `L` destroys at most `|L|·|V|` edges. -/
theorem card_deleted_restrictAway_le (G : SimpleGraph V) [DecidableRel G.Adj] (L : Finset V) :
    ((G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2).card : ℝ)
      ≤ (L.card : ℝ) * (Fintype.card V : ℝ) := by
  classical
  have hsub : G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2
      ⊆ L.biUnion (fun v => (G.neighborFinset v).image (fun u => ({v, u} : Finset V))) := by
    intro e he
    rw [Finset.mem_sdiff, SimpleGraph.mem_cliqueFinset_iff] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he1.card_eq
    have hadj : G.Adj a b := he1.1 (by simp) (by simp) hab
    have hnadj : ¬ (restrictAway G L).Adj a b := by
      intro h
      refine he2 (SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, Finset.card_pair hab⟩)
      simpa using SimpleGraph.isClique_pair.mpr (fun _ => h)
    have hmem : a ∈ L ∨ b ∈ L := by
      by_contra hcon
      push Not at hcon
      exact hnadj ⟨hadj, hcon.1, hcon.2⟩
    rw [Finset.mem_biUnion]
    rcases hmem with h | h
    · exact ⟨a, h, Finset.mem_image.mpr ⟨b, by simpa using hadj, rfl⟩⟩
    · refine ⟨b, h, Finset.mem_image.mpr ⟨a, by simpa using hadj.symm, ?_⟩⟩
      exact Finset.pair_comm b a
  have hcard := Finset.card_le_card hsub
  have hbu : (L.biUnion (fun v => (G.neighborFinset v).image (fun u => ({v, u} : Finset V)))).card
      ≤ ∑ v ∈ L, G.degree v := by
    refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum (fun v _ => ?_))
    exact le_trans (Finset.card_image_le) (le_of_eq (SimpleGraph.card_neighborFinset_eq_degree G v))
  have hdeg : ∑ v ∈ L, G.degree v ≤ L.card * Fintype.card V := by
    calc ∑ v ∈ L, G.degree v ≤ ∑ _v ∈ L, Fintype.card V := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          exact le_of_lt (SimpleGraph.degree_lt_card_verts (G := G) v)
      _ = L.card * Fintype.card V := by rw [Finset.sum_const, smul_eq_mul]
  have : (G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2).card
      ≤ L.card * Fintype.card V := le_trans hcard (le_trans hbu hdeg)
  exact_mod_cast this

/-- Deleting the edges at `L` lowers each degree outside `L` by at most `|L|`. -/
theorem degree_restrictAway_ge (G : SimpleGraph V) [DecidableRel G.Adj] {L : Finset V} {x : V}
    (hx : x ∉ L) :
    (G.degree x : ℝ) - (L.card : ℝ) ≤ ((restrictAway G L).degree x : ℝ) := by
  classical
  have hsub : G.neighborFinset x \ L ⊆ (restrictAway G L).neighborFinset x := by
    intro y hy
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
    exact SimpleGraph.mem_neighborFinset _ _ _ |>.mpr ⟨hy.1, hx, hy.2⟩
  have h1 : (G.neighborFinset x \ L).card ≤ (restrictAway G L).degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card hsub
  have h2 : G.degree x ≤ (G.neighborFinset x \ L).card + L.card := by
    have := Finset.card_le_card_sdiff_add_card (s := G.neighborFinset x) (t := L)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at this
    exact this
  have h3 : (G.degree x : ℝ) ≤ ((G.neighborFinset x \ L).card : ℝ) + (L.card : ℝ) := by
    exact_mod_cast h2
  have h4 : (((G.neighborFinset x \ L).card : ℕ) : ℝ) ≤ ((restrictAway G L).degree x : ℝ) := by
    exact_mod_cast h1
  linarith only [h3, h4]

/-! ### The near-complete branch -/

/-- **The near-complete branch.**  For every `ε > 0` there is `η > 0` such that every large graph
with at least `(1/2 − η)|V|²` edges has packing gap at most `ε|V|²`. -/
theorem gap_le_of_near_complete (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (1 / 2 - η) * (Fintype.card V : ℝ) ^ 2 ≤ ((G.cliqueFinset 2).card : ℝ) →
        nu3star G - (nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨θ, hθ0, hθ1, n₀, hdense⟩ := nibbleGap_of_dense_core ε hε
  set θ₂ : ℝ := (1 + θ) / 2 with hθ₂def
  have hθ₂lo : θ < θ₂ := by rw [hθ₂def]; linarith only [hθ1]
  have hθ₂hi : θ₂ < 1 := by rw [hθ₂def]; linarith only [hθ₂def, hθ₂lo]
  have hgap2 : 0 < 1 - θ₂ := by linarith only [hθ₂hi]
  have hp1 : (0 : ℝ) < (1 - θ₂) * ε / 8 := by
    apply div_pos (mul_pos hgap2 hε); norm_num
  have hp2 : (0 : ℝ) < (1 - θ₂) * (1 - θ) / 4 := by
    apply div_pos (mul_pos hgap2 (by linarith)); norm_num
  refine ⟨min ((1 - θ₂) * ε / 8) ((1 - θ₂) * (1 - θ) / 4), lt_min hp1 hp2, max n₀ 1, ?_⟩
  set η : ℝ := min ((1 - θ₂) * ε / 8) ((1 - θ₂) * (1 - θ) / 4) with hηdef
  have hη1 : η ≤ (1 - θ₂) * ε / 8 := min_le_left _ _
  have hη2 : η ≤ (1 - θ₂) * (1 - θ) / 4 := min_le_right _ _
  have hηpos : 0 < η := lt_min hp1 hp2
  intro V _ _ G _ hV hedge
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    have : 1 ≤ Fintype.card V := le_trans (le_max_right n₀ 1) hV
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith only [hn1]
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  -- the low-degree set
  set L : Finset V := (univ : Finset V).filter (fun v => (G.degree v : ℝ) < θ₂ * n) with hLdef
  have hcount := card_lowDeg_mul_le G (θ₂ * n)
  have hE : ((G.cliqueFinset 2).card : ℝ) ≤ (G.edgeFinset.card : ℝ) :=
    card_clique2_le_card_edgeFinset G
  have hL : (L.card : ℝ) * ((1 - θ₂) * n) ≤ 2 * η * n ^ 2 := by
    have h1 : n - θ₂ * n = (1 - θ₂) * n := by ring
    rw [h1] at hcount
    linarith only [hcount, hE, hedge]
  have hLcard : (L.card : ℝ) ≤ 2 * η * n / (1 - θ₂) := by
    rw [le_div_iff₀ hgap2]
    nlinarith only [hL, hnpos]
  -- the deletion is small
  have hdel : ((G.cliqueFinset 2 \ (restrictAway G L).cliqueFinset 2).card : ℝ)
      ≤ (ε / 4) * n ^ 2 := by
    have h1 := card_deleted_restrictAway_le G L
    have h2 : (L.card : ℝ) * n ≤ (2 * η * n / (1 - θ₂)) * n := by
      apply mul_le_mul_of_nonneg_right hLcard (le_of_lt hnpos)
    have h3 : (2 * η * n / (1 - θ₂)) * n ≤ (ε / 4) * n ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hgap2]
      nlinarith only [hη1, hnpos]
    linarith only [h1, h2, h3]
  -- the core is dense
  have hdeg : ∀ x : V, (restrictAway G L).degree x = 0 ∨
      θ * n ≤ ((restrictAway G L).degree x : ℝ) := by
    intro x
    by_cases hx : x ∈ L
    · exact Or.inl (restrictAway_degree_eq_zero G hx)
    · refine Or.inr ?_
      have hdx : θ₂ * n ≤ (G.degree x : ℝ) := by
        by_contra hcon
        push Not at hcon
        exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcon⟩)
      have hlow := degree_restrictAway_ge G (L := L) hx
      have hLsmall : (L.card : ℝ) ≤ (1 - θ) * n / 2 := by
        have : 2 * η * n / (1 - θ₂) ≤ (1 - θ) * n / 2 := by
          rw [div_le_div_iff₀ hgap2 (by norm_num : (0:ℝ) < 2)]
          nlinarith only [hη2, hnpos]
        linarith [hLcard]
      have hθ₂eq : θ₂ * n = θ * n + (1 - θ) * n / 2 := by rw [hθ₂def]; ring
      linarith only [hdx, hlow, hLsmall, hθ₂eq]
  exact hdense V G (le_trans (le_max_left n₀ 1) hV) (restrictAway G L) _ (restrictAway_le G L)
    hdel hdeg

/-! ### A universal constant below `1/9` -/

/-- **A universal packing-gap constant below `1/9`.**  There is `c < 1/9` with
`ν₃* − ν₃ ≤ c|V|²` for every large graph: near-complete graphs are handled by
`Nibble.AX1.gap_le_of_near_complete`, all others by `ν₃* ≤ |E|/3` together with `ν₃* ≤ 3ν₃`. -/
theorem exists_gap_const_lt_ninth :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 9 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → nu3star G - (nu3 G : ℝ) ≤ c * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨η, hη, n₀, hnear⟩ := gap_le_of_near_complete (1 / 10) (by norm_num)
  refine ⟨max (1 / 10) (1 / 9 - 2 * η / 9), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_,
    n₀, ?_⟩
  · exact max_lt (by norm_num) (by linarith)
  intro V _ _ G _ hV
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  rcases le_or_gt ((1 / 2 - η) * (Fintype.card V : ℝ) ^ 2) (((G.cliqueFinset 2).card : ℝ))
    with hcase | hcase
  · have := hnear V G hV hcase
    have hle : (1 / 10 : ℝ) ≤ max (1 / 10) (1 / 9 - 2 * η / 9) := le_max_left _ _
    nlinarith only [this, hle]
  · have h1 : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
    have h2 : nu3star G ≤ 3 * (nu3 G : ℝ) := Nibble.nu3star_le_three_nu3 G
    have hle : (1 / 9 - 2 * η / 9 : ℝ) ≤ max (1 / 10) (1 / 9 - 2 * η / 9) := le_max_right _ _
    nlinarith only [hcase, h1, h2, hle]

/-- **`CoreGapAt ε δ` for every `δ` and every `ε` above a constant `c < 1/9`**, strictly improving
`Nibble.AX1.coreGapAt_of_ninth`. -/
theorem coreGapAt_of_lt_ninth :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 9 ∧ ∀ ε δ : ℝ, c ≤ ε → CoreGapAt ε δ := by
  obtain ⟨c, hc0, hc9, n₀, hmain⟩ := exists_gap_const_lt_ninth
  refine ⟨c, hc0, hc9, fun ε δ hε => ⟨n₀, ?_⟩⟩
  intro V _ _ G _ hV _ _
  have h := hmain V G hV
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hε) hnn]

end Nibble.AX1

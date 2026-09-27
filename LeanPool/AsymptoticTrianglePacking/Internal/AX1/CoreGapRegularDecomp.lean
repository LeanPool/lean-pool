/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — reducing the AX1 residual to a purely structural statement

`Nibble.AX1.gap_le_of_regular_triangle_degrees` (`Nibble.CoreGapRegularDegrees`) discharges the
nibble side of the packing gap: a graph whose triangle degrees are near-regular at *any* scale has
gap `≤ ε|V|²`.  This file turns that into a reduction of the whole residual
`Nibble.AX1.CoreGapResidual` to a statement in which no packing, no matching and no probability
appears — only the existence of a *near-regular decomposition* of the edge set.

* `Nibble.AX1.edgeSelect`, `Nibble.AX1.colorPart` — the spanning subgraph of the edges satisfying a
  predicate, and the colour classes of an edge colouring `col : Finset V → ℕ`.
* `Nibble.AX1.nu3_sum_colorParts_le` — **superadditivity**: `∑ᵢ ν₃(Gᵢ) ≤ ν₃(G)` for the colour
  classes `Gᵢ` of any edge colouring, since matchings in edge-disjoint subgraphs unite to a matching.
* `Nibble.AX1.nu3_ge_of_regular_triangle_degrees` — the nibble, in the form
  `ν₃(G) ≥ (1−β)|E(G)|/3` for near-regular triangle degrees.
* `Nibble.AX1.RegularDecompAt`, `Nibble.AX1.RegularDecompResidual` — the structural residual: every
  large graph has an edge colouring whose colour classes each have near-regular triangle degrees (at
  their own scale, with few exceptional edges) and whose total edge count recovers `3ν₃*(G)` up to
  `ε|V|²`.
* `Nibble.AX1.coreGapResidual_of_regularDecomp`, `Nibble.AX1.ax1_of_regularDecomp` — the reductions
  to `Nibble.AX1.CoreGapResidual` and to `AX1Statement`.

This is exactly what the Szemerédi-regularity construction in the Haxell–Rödl proof produces (clean
the irregular and sparse pairs, split each pair among the cluster triples in proportion to the
fractional optimum, sparsify each triple to a common density); the analytic step it used to be
paired with — the nibble — is now proved, so the remaining mathematics is entirely structural.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularDegrees

/-! # CoreGapRegularDecomp -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Colour classes of an edge colouring -/

/-- The spanning subgraph of `G` consisting of the edges `e` with `P e`. -/
def edgeSelect (G : SimpleGraph V) (P : Finset V → Prop) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ P {x, y}
  symm := ⟨by
    rintro x y ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rwa [Finset.pair_comm]⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable instance instDecidableRelEdgeSelect (G : SimpleGraph V) (P : Finset V → Prop) :
    DecidableRel (edgeSelect G P).Adj := fun _ _ => Classical.dec _

theorem edgeSelect_adj (G : SimpleGraph V) (P : Finset V → Prop) (x y : V) :
    (edgeSelect G P).Adj x y ↔ G.Adj x y ∧ P {x, y} := Iff.rfl

theorem edgeSelect_le (G : SimpleGraph V) (P : Finset V → Prop) : edgeSelect G P ≤ G :=
  fun _ _ h => h.1

/-- The `i`-th colour class of the edge colouring `col`. -/
noncomputable def colorPart (G : SimpleGraph V) (col : Finset V → ℕ) (i : ℕ) : SimpleGraph V :=
  edgeSelect G (fun e => col e = i)

noncomputable instance instDecidableRelColorPart (G : SimpleGraph V)
    (col : Finset V → ℕ) (i : ℕ) : DecidableRel (colorPart G col i).Adj :=
  instDecidableRelEdgeSelect G _

theorem colorPart_le (G : SimpleGraph V) (col : Finset V → ℕ) (i : ℕ) : colorPart G col i ≤ G :=
  edgeSelect_le G _

/-- Every edge of a triangle of the `i`-th colour class has colour `i`. -/
theorem colorPart_hyperedge_color (G : SimpleGraph V) (col : Finset V → ℕ) (i : ℕ)
    {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE (colorPart G col i)) :
    ∀ e ∈ T, col e = i := by
  classical
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  intro e he
  rw [Finset.mem_powersetCard] at he
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.2
  have hadj : (colorPart G col i).Adj a b :=
    ht.1 (he.1 (by simp)) (he.1 (by simp)) hab
  exact hadj.2

/-- Hyperedges of a triangle hypergraph are nonempty. -/
theorem triangleHypergraphE_nonempty_of_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Finset (Finset V)} (hT : T ∈ triangleHypergraphE G) : T.Nonempty := by
  classical
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  rw [← Finset.card_pos, Finset.card_powersetCard, ht.card_eq]
  decide +kernel

/-- **Superadditivity of `ν₃` over the colour classes of an edge colouring.**  The colour classes are
edge-disjoint, so maximum packings of the classes unite to a packing of `G`. -/
theorem nu3_sum_colorParts_le (G : SimpleGraph V) [DecidableRel G.Adj] (col : Finset V → ℕ)
    (k : ℕ) : ∑ i ∈ Finset.range k, nu3 (colorPart G col i) ≤ nu3 G := by
  classical
  have hex : ∀ i : ℕ, ∃ M : Finset (Finset (Finset V)),
      IsMatching (triangleHypergraphE (colorPart G col i)) M ∧
        M.card = nu3 (colorPart G col i) := fun i => Nibble.exists_maximum_packing _
  choose Mf hMf hMcard using hex
  have hmemcol : ∀ (i : ℕ), ∀ T ∈ Mf i, ∀ e ∈ T, col e = i := by
    intro i T hT
    exact colorPart_hyperedge_color G col i ((hMf i).subset hT)
  have hmemne : ∀ (i : ℕ), ∀ T ∈ Mf i, T.Nonempty := by
    intro i T hT
    exact triangleHypergraphE_nonempty_of_mem _ ((hMf i).subset hT)
  have hdisj : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, i ≠ j → Disjoint (Mf i) (Mf j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro T hTi hTj
    obtain ⟨e, he⟩ := hmemne i T hTi
    have h1 := hmemcol i T hTi e he
    have h2 := hmemcol j T hTj e he
    exact hij (h1 ▸ h2 ▸ rfl)
  set M : Finset (Finset (Finset V)) := (Finset.range k).biUnion Mf with hMdef
  have hcard : M.card = ∑ i ∈ Finset.range k, (Mf i).card := Finset.card_biUnion hdisj
  have hMatch : IsMatching (triangleHypergraphE G) M := by
    constructor
    · intro T hT
      rw [hMdef, Finset.mem_biUnion] at hT
      obtain ⟨i, -, hTi⟩ := hT
      exact triangleHypergraphE_mono G (colorPart G col i) (colorPart_le G col i)
        ((hMf i).subset hTi)
    · intro T hT T' hT' hne
      rw [hMdef, Finset.mem_biUnion] at hT hT'
      obtain ⟨i, -, hTi⟩ := hT
      obtain ⟨j, -, hTj⟩ := hT'
      by_cases hij : i = j
      · subst hij
        exact (hMf i).disjoint T hTi T' hTj hne
      · rw [Finset.disjoint_left]
        intro e he he'
        exact hij ((hmemcol i T hTi e he) ▸ (hmemcol j T' hTj e he') ▸ rfl)
  calc ∑ i ∈ Finset.range k, nu3 (colorPart G col i)
      = ∑ i ∈ Finset.range k, (Mf i).card := by
        exact Finset.sum_congr rfl (fun i _ => (hMcard i).symm)
    _ = M.card := hcard.symm
    _ ≤ nu3 G := nu3_ge G hMatch

/-! ### The nibble, as a lower bound on `ν₃` -/

/-- **The nibble as an integral packing bound.**  For every `β > 0` there are `μ, η > 0` and `d₀`
such that a graph with near-regular triangle degrees at a scale `d ≥ d₀` has
`ν₃ ≥ (1−β)|E|/3`. -/
theorem nu3_ge_of_regular_triangle_degrees (β : ℝ) (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (d : ℝ) (Exc : Finset (Finset V)), d₀ ≤ d →
        (Exc.card : ℝ) ≤ η * ((G.cliqueFinset 2).card : ℝ) →
        (∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d) →
        (∀ e ∈ G.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ)) →
        (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (nu3 G : ℝ) := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds 3 (by norm_num) β hβ
  refine ⟨μ, hμ, η, hη, max d₀ (max (1 / μ) 1), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  intro V _ _ G _ d Exc hd hExc hhi hlo
  have hdd₀ : d₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hinv : 1 / μ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hcodeg : (1 : ℝ) ≤ μ * d := by
    rw [div_le_iff₀ hμ] at hinv; linarith
  set Exc' : Finset (EdgeV G) := (univ : Finset (EdgeV G)).filter (fun E => E.val ∈ Exc)
    with hExc'def
  have hExc'card : Exc'.card ≤ Exc.card := by
    refine Finset.card_le_card_of_injOn (fun E => E.val) (fun E hE => ?_) ?_
    · exact (Finset.mem_filter.mp hE).2
    · intro E _ E' _ h
      exact Subtype.ext h
  have hcardEdge : (Fintype.card (EdgeV G) : ℝ) = ((G.cliqueFinset 2).card : ℝ) := by
    exact_mod_cast card_EdgeV G
  have hExc' : (Exc'.card : ℝ) ≤ η * (Fintype.card (EdgeV G) : ℝ) := by
    rw [hcardEdge]
    have : (Exc'.card : ℝ) ≤ (Exc.card : ℝ) := by exact_mod_cast hExc'card
    linarith
  have hhi' : ∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d := by
    intro E
    rw [edgeTriangleDegree_eq G E]
    exact hhi E.val E.property
  have hlo' : ∀ E ∉ Exc', (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
    intro E hE
    rw [edgeTriangleDegree_eq G E]
    refine hlo E.val E.property (fun hc => hE ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ E, hc⟩
  have hreg : NearlyRegularMost (triangleHypergraphSub G) d μ η :=
    triangleHypergraphSub_nearlyRegularMost_of_bounds G Exc' hExc' hlo' (fun E _ => hhi' E)
  have hcod : CodegreeBounded (triangleHypergraphSub G) (μ * d) :=
    triangleHypergraphSub_codegreeBounded G hcodeg
  obtain ⟨M, hM, hMcard⟩ :=
    hmain (triangleHypergraphSub G) d hdpos hdd₀ (triangleHypergraphSub_uniform G) hreg hcod hhi'
  have hle : (M.card : ℝ) ≤ (nu3 G : ℝ) := by exact_mod_cast sub_matching_card_le_nu3 G hM
  have hMcard' : (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (M.card : ℝ) := by
    have := hMcard
    rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num] at this
    rwa [hcardEdge] at this
  linarith

/-! ### The structural residual -/

/-- **A near-regular decomposition at parameters `(ε, μ, η, d₀)`.**  Every large graph carries an
edge colouring whose colour classes have near-regular triangle degrees — each at its own scale
`d i ≥ d₀`, with the lower bound allowed to fail on at most an `η`-fraction of that class's edges —
and whose total edge count is at least `3ν₃*(G) − 3ε|V|²`. -/
def RegularDecompAt (ε μ η d₀ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V →
    ∃ (k : ℕ) (col : Finset V → ℕ) (d : ℕ → ℝ),
      (∀ i < k, d₀ ≤ d i) ∧
      (∀ i < k, ∀ e ∈ (colorPart G col i).cliqueFinset 2,
        (edgeTriangleDegree (colorPart G col i) e : ℝ) ≤ (1 + μ) * d i) ∧
      (∀ i < k, ∃ Exc : Finset (Finset V),
        (Exc.card : ℝ) ≤ η * (((colorPart G col i).cliqueFinset 2).card : ℝ) ∧
        ∀ e ∈ (colorPart G col i).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d i ≤ (edgeTriangleDegree (colorPart G col i) e : ℝ)) ∧
      nu3star G ≤ (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3) + ε * (Fintype.card V : ℝ) ^ 2

/-- **The structural residual**: a near-regular decomposition at every window of parameters. -/
def RegularDecompResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    RegularDecompAt ε μ η d₀

/-- **The reduction.**  A near-regular decomposition of every large graph implies the AX1 core
residual: the nibble packs each colour class up to a `(1−β)`-fraction of its edges
(`Nibble.AX1.nu3_ge_of_regular_triangle_degrees`), the classes are edge-disjoint so the packings
unite (`Nibble.AX1.nu3_sum_colorParts_le`), and the decomposition's edge count recovers `ν₃*`. -/
theorem coreGapResidual_of_regularDecomp (h : RegularDecompResidual) : CoreGapResidual := by
  intro ε hε δ _
  rcases le_or_gt (1 / 3 : ℝ) ε with hbig | hsmall
  · exact coreGapAt_of_third hbig
  -- `β = 3ε < 1`
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hnib⟩ := nu3_ge_of_regular_triangle_degrees (3 * ε) (by linarith)
  obtain ⟨n₀, hdec⟩ := h (ε / 2) (by linarith) μ hμ η hη d₀ hd₀
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV _ _
  obtain ⟨k, col, d, hd, hhi, hlo, hval⟩ := hdec V G hV
  -- each colour class is packed by the nibble
  have hpart : ∀ i ∈ Finset.range k,
      (1 - 3 * ε) * ((((colorPart G col i).cliqueFinset 2).card : ℝ) / 3)
        ≤ (nu3 (colorPart G col i) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨Exc, hExc, hlo'⟩ := hlo i hi
    exact hnib V (colorPart G col i) (d i) Exc (hd i hi) hExc (hhi i hi) hlo'
  have hsum : (1 - 3 * ε) * (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3)
      ≤ ∑ i ∈ Finset.range k, (nu3 (colorPart G col i) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpart
  have hsuper : ∑ i ∈ Finset.range k, (nu3 (colorPart G col i) : ℝ) ≤ (nu3 G : ℝ) := by
    have := nu3_sum_colorParts_le G col k
    exact_mod_cast this
  -- assemble
  set S : ℝ := ∑ i ∈ Finset.range k, (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3 with hS
  have hSnn : 0 ≤ S := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    positivity
  have hstar : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
  have hEn : ((G.cliqueFinset 2).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 :=
    Nibble.edge_card_le_half_card_sq G
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  have hstar6 : nu3star G ≤ (Fintype.card V : ℝ) ^ 2 / 6 := by linarith
  have hcoef : (0 : ℝ) < 1 - 3 * ε := by linarith
  have hS' : nu3star G - (ε / 2) * (Fintype.card V : ℝ) ^ 2 ≤ S := by linarith
  have h1 : (1 - 3 * ε) * (nu3star G - (ε / 2) * (Fintype.card V : ℝ) ^ 2)
      ≤ (1 - 3 * ε) * S := mul_le_mul_of_nonneg_left hS' hcoef.le
  have hA : (1 - 3 * ε) * (nu3star G - (ε / 2) * (Fintype.card V : ℝ) ^ 2) ≤ (nu3 G : ℝ) :=
    le_trans h1 (le_trans hsum hsuper)
  have hB : 3 * ε * nu3star G ≤ 3 * ε * ((Fintype.card V : ℝ) ^ 2 / 6) :=
    mul_le_mul_of_nonneg_left hstar6 (by positivity)
  have hC : (0 : ℝ) ≤ ε ^ 2 * (Fintype.card V : ℝ) ^ 2 := by positivity
  linarith only [hA, hB, hC]

/-- **AX1 from the structural residual.** -/
theorem ax1_of_regularDecomp (h : RegularDecompResidual) : AX1Statement :=
  ax1_of_coreGapResidual (coreGapResidual_of_regularDecomp h)

/-! ### The residual is satisfiable: the one-colour witness -/

/-- Colouring every edge `0` leaves the graph unchanged. -/
theorem colorPart_const (G : SimpleGraph V) : colorPart G (fun _ => 0) 0 = G := by
  ext x y
  simp [colorPart, edgeSelect_adj]

/-- **The one-colour witness.**  A graph whose own triangle degrees are near-regular at a scale
`d ≥ d₀` satisfies the requirement of `Nibble.AX1.RegularDecompAt` with the trivial one-colour
decomposition.  So the structural residual is exactly the assertion that *every* large graph can be
edge-coloured into near-regular classes without losing more than `ε|V|²` of the fractional optimum:
it is a genuine statement about colourings, non-vacuous and satisfied by the regular graphs. -/
theorem regularDecomp_witness_of_regular (ε μ η d₀ : ℝ) (hε : 0 ≤ ε)
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (Exc : Finset (Finset V)) (hd : d₀ ≤ d)
    (hExc : (Exc.card : ℝ) ≤ η * ((G.cliqueFinset 2).card : ℝ))
    (hhi : ∀ e ∈ G.cliqueFinset 2, (edgeTriangleDegree G e : ℝ) ≤ (1 + μ) * d)
    (hlo : ∀ e ∈ G.cliqueFinset 2, e ∉ Exc → (1 - μ) * d ≤ (edgeTriangleDegree G e : ℝ)) :
    ∃ (k : ℕ) (col : Finset V → ℕ) (dd : ℕ → ℝ),
      (∀ i < k, d₀ ≤ dd i) ∧
      (∀ i < k, ∀ e ∈ (colorPart G col i).cliqueFinset 2,
        (edgeTriangleDegree (colorPart G col i) e : ℝ) ≤ (1 + μ) * dd i) ∧
      (∀ i < k, ∃ Exc' : Finset (Finset V),
        (Exc'.card : ℝ) ≤ η * (((colorPart G col i).cliqueFinset 2).card : ℝ) ∧
        ∀ e ∈ (colorPart G col i).cliqueFinset 2, e ∉ Exc' →
          (1 - μ) * dd i ≤ (edgeTriangleDegree (colorPart G col i) e : ℝ)) ∧
      nu3star G ≤ (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3) + ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hge : G ≤ colorPart G (fun _ => 0) 0 := by rw [colorPart_const]
  have hdeg : ∀ e, edgeTriangleDegree (colorPart G (fun _ => 0) 0) e = edgeTriangleDegree G e :=
    fun e => le_antisymm (edgeTriangleDegree_mono G _ (colorPart_le G _ 0) e)
      (edgeTriangleDegree_mono _ G hge e)
  have hsub : (colorPart G (fun _ => 0) 0).cliqueFinset 2 ⊆ G.cliqueFinset 2 :=
    SimpleGraph.cliqueFinset_mono _ (colorPart_le G (fun _ => 0) 0)
  have hsup : G.cliqueFinset 2 ⊆ (colorPart G (fun _ => 0) 0).cliqueFinset 2 :=
    SimpleGraph.cliqueFinset_mono _ hge
  have hcard : (((colorPart G (fun _ => 0) 0).cliqueFinset 2).card : ℝ)
      = ((G.cliqueFinset 2).card : ℝ) := by
    congr 2
    exact Finset.Subset.antisymm hsub hsup
  refine ⟨1, fun _ => 0, fun _ => d, fun i _ => hd, ?_, ?_, ?_⟩
  · intro i hi e he
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    rw [hdeg]
    exact hhi e (hsub he)
  · intro i hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    refine ⟨Exc, by rw [hcard]; exact hExc, ?_⟩
    intro e he hne
    rw [hdeg]
    exact hlo e (hsub he) hne
  · have hstar : nu3star G ≤ ((G.cliqueFinset 2).card : ℝ) / 3 := nu3star_le G
    have hnn : (0 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by positivity
    simp only [Finset.sum_range_one]
    rw [hcard]
    linarith

end Nibble.AX1

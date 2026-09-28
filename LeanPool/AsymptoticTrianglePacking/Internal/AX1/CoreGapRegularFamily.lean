/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the near-regular *family* form of the AX1 structural residual

`Nibble.AX1.RegularDecompAt` (`Nibble.CoreGapRegularDecomp`) asks for an edge *colouring* whose
colour classes have near-regular triangle degrees and together carry `3ν₃*(G) − o(|V|²)` edges.
Colourings are an awkward object to construct; what a regularity argument actually produces is a
*family of edge-disjoint subgraphs*.  This file

* defines `Nibble.AX1.HasNearRegularFamily G ε μ η d₀` — the same requirement, phrased for a family
  `H : ℕ → SimpleGraph V` of pairwise edge-disjoint subgraphs of `G`;
* turns such a family into a colouring (`Nibble.AX1.familyColoring`,
  `Nibble.AX1.colorPart_familyColoring`), so that
  `Nibble.AX1.regularDecompAt_of_family` reduces `RegularDecompAt` to the family form, and
  `Nibble.AX1.hasNearRegularFamily_of_regularDecomp` gives the converse: nothing is lost;
* records the two structural moves the regularity route needs:
  - `Nibble.AX1.HasNearRegularFamily.mono_of_le` — a family for a spanning subgraph `G' ≤ G` is a
    family for `G`, at a cost equal to the loss of `ν₃*`;
  - `Nibble.AX1.hasNearRegularFamily_of_few_triangles` — the empty family already works for
    triangle-poor graphs (Mathlib's triangle removal lemma, via
    `Nibble.AX1.nu3star_le_of_few_triangles`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularDecomp
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRemoval

/-! # CoreGapRegularFamily -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Edge-disjoint families and the colouring they induce -/

/-- The first `k` members of the family `H` are pairwise edge-disjoint. -/
def EdgeDisjointFamily (H : ℕ → SimpleGraph V) (k : ℕ) : Prop :=
  ∀ i < k, ∀ j < k, i ≠ j → ∀ x y, (H i).Adj x y → ¬ (H j).Adj x y

/-- A pair `{x, y}` of distinct vertices is a `2`-clique of `H` iff `x` and `y` are adjacent. -/
theorem pair_mem_cliqueFinset_two (H : SimpleGraph V) [DecidableRel H.Adj] {x y : V} (hxy : x ≠ y) :
    ({x, y} : Finset V) ∈ H.cliqueFinset 2 ↔ H.Adj x y := by
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, Finset.card_pair hxy]
  simp [hxy]

/-- The `2`-cliques of two equal graphs agree, whatever the decidability instances. -/
theorem cliqueFinset_congr_graph {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj]
    [DecidableRel G₂.Adj] (h : G₁ = G₂) (n : ℕ) : G₁.cliqueFinset n = G₂.cliqueFinset n := by
  subst h; congr!

/-- Triangle degrees of two equal graphs agree, whatever the decidability instances. -/
theorem edgeTriangleDegree_congr_graph {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj]
    [DecidableRel G₂.Adj] (h : G₁ = G₂) (e : Finset V) :
    edgeTriangleDegree G₁ e = edgeTriangleDegree G₂ e := by
  subst h; congr!

open Classical in
/-- The edge colouring induced by an edge-disjoint family: an edge gets the index of the member of
the family containing it, and the junk colour `k` if there is none. -/
noncomputable def familyColoring (H : ℕ → SimpleGraph V) (k : ℕ) (e : Finset V) : ℕ :=
  if h : ∃ i, i < k ∧ e ∈ (H i).cliqueFinset 2 then Nat.find h else k

/-- The colour classes of `Nibble.AX1.familyColoring` are exactly the members of the family. -/
theorem colorPart_familyColoring (G : SimpleGraph V) (H : ℕ → SimpleGraph V)
    (k : ℕ) (hle : ∀ i < k, H i ≤ G) (hdisj : EdgeDisjointFamily H k) {i : ℕ} (hi : i < k) :
    colorPart G (familyColoring H k) i = H i := by
  classical
  ext x y
  rw [colorPart, edgeSelect_adj]
  constructor
  · rintro ⟨hG, hcol⟩
    have hxy : x ≠ y := hG.ne
    rw [familyColoring] at hcol
    by_cases hex : ∃ j, j < k ∧ ({x, y} : Finset V) ∈ (H j).cliqueFinset 2
    · rw [dite_eq_left hex] at hcol
      have hspec := Nat.find_spec hex
      rw [hcol] at hspec
      exact (pair_mem_cliqueFinset_two (H i) hxy).mp hspec.2
    · rw [dite_eq_right hex] at hcol
      exact absurd hcol.symm (Nat.ne_of_lt hi)
  · intro hHi
    have hxy : x ≠ y := hHi.ne
    refine ⟨hle i hi hHi, ?_⟩
    have hex : ∃ j, j < k ∧ ({x, y} : Finset V) ∈ (H j).cliqueFinset 2 :=
      ⟨i, hi, (pair_mem_cliqueFinset_two (H i) hxy).mpr hHi⟩
    rw [familyColoring, dite_eq_left hex]
    obtain ⟨hjk, hjmem⟩ := Nat.find_spec hex
    have hjadj : (H (Nat.find hex)).Adj x y :=
      (pair_mem_cliqueFinset_two (H (Nat.find hex)) hxy).mp hjmem
    by_contra hne
    exact hdisj (Nat.find hex) hjk i hi hne x y hjadj hHi

/-! ### The family form of the structural residual -/

open Classical in
/-- **A near-regular family for `G` at parameters `(ε, μ, η, d₀)`**: pairwise edge-disjoint
subgraphs `H 0, …, H (k−1)` of `G`, each with near-regular triangle degrees at its own scale
`d i ≥ d₀` (the lower bound being allowed to fail on at most an `η`-fraction of that member's
edges), whose total edge count is at least `3ν₃*(G) − 3ε|V|²`. -/
def HasNearRegularFamily (G : SimpleGraph V) [DecidableRel G.Adj] (ε μ η d₀ : ℝ) : Prop :=
  ∃ (k : ℕ) (H : ℕ → SimpleGraph V) (d : ℕ → ℝ),
    (∀ i < k, H i ≤ G) ∧
    EdgeDisjointFamily H k ∧
    (∀ i < k, d₀ ≤ d i) ∧
    (∀ i < k, ∀ e ∈ (H i).cliqueFinset 2,
      (edgeTriangleDegree (H i) e : ℝ) ≤ (1 + μ) * d i) ∧
    (∀ i < k, ∃ Exc : Finset (Finset V),
      (Exc.card : ℝ) ≤ η * (((H i).cliqueFinset 2).card : ℝ) ∧
      ∀ e ∈ (H i).cliqueFinset 2, e ∉ Exc →
        (1 - μ) * d i ≤ (edgeTriangleDegree (H i) e : ℝ)) ∧
    nu3star G ≤ (∑ i ∈ Finset.range k, (((H i).cliqueFinset 2).card : ℝ) / 3)
      + ε * (Fintype.card V : ℝ) ^ 2

/-- Weakening the accuracy of a near-regular family. -/
theorem HasNearRegularFamily.mono_eps {G : SimpleGraph V} [DecidableRel G.Adj] {ε ε' μ η d₀ : ℝ}
    (h : HasNearRegularFamily G ε μ η d₀) (hεε' : ε ≤ ε') :
    HasNearRegularFamily G ε' μ η d₀ := by
  obtain ⟨k, H, d, hle, hdisj, hd, hhi, hlo, hval⟩ := h
  refine ⟨k, H, d, hle, hdisj, hd, hhi, hlo, ?_⟩
  have hnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
  nlinarith only [hεε', hval]

/-- **A family for a spanning subgraph is a family for the graph.**  If `G' ≤ G` and the fractional
optimum drops by at most `c|V|²` when passing to `G'`, a near-regular family for `G'` is one for
`G` at accuracy `ε + c`. -/
theorem HasNearRegularFamily.mono_of_le {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] {ε c μ η d₀ : ℝ} (hle : G' ≤ G)
    (hgap : nu3star G ≤ nu3star G' + c * (Fintype.card V : ℝ) ^ 2)
    (h : HasNearRegularFamily G' ε μ η d₀) :
    HasNearRegularFamily G (ε + c) μ η d₀ := by
  obtain ⟨k, H, d, hleH, hdisj, hd, hhi, hlo, hval⟩ := h
  refine ⟨k, H, d, fun i hi => le_trans (hleH i hi) hle, hdisj, hd, hhi, hlo, ?_⟩
  have : nu3star G ≤ nu3star G' + c * (Fintype.card V : ℝ) ^ 2 := hgap
  nlinarith [hval]

/-- **The triangle-poor branch.**  A graph with fewer than `triangleRemovalBound(ε)·|V|³` triangles
has `ν₃* ≤ ε|V|²`, so the *empty* family is already a near-regular family. -/
theorem hasNearRegularFamily_of_few_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ : ℝ} (hfew : ((G.cliqueFinset 3).card : ℝ)
      < SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3) :
    HasNearRegularFamily G ε μ η d₀ := by
  refine ⟨0, fun _ => ⊥, fun _ => d₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · simpa using nu3star_le_of_few_triangles G hfew

/-! ### From families to colourings -/

/-- A near-regular family gives the data required by `Nibble.AX1.RegularDecompAt`. -/
theorem regularDecomp_data_of_family (G : SimpleGraph V) [DecidableRel G.Adj] {ε μ η d₀ : ℝ}
    (h : HasNearRegularFamily G ε μ η d₀) :
    ∃ (k : ℕ) (col : Finset V → ℕ) (d : ℕ → ℝ),
      (∀ i < k, d₀ ≤ d i) ∧
      (∀ i < k, ∀ e ∈ (colorPart G col i).cliqueFinset 2,
        (edgeTriangleDegree (colorPart G col i) e : ℝ) ≤ (1 + μ) * d i) ∧
      (∀ i < k, ∃ Exc : Finset (Finset V),
        (Exc.card : ℝ) ≤ η * (((colorPart G col i).cliqueFinset 2).card : ℝ) ∧
        ∀ e ∈ (colorPart G col i).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d i ≤ (edgeTriangleDegree (colorPart G col i) e : ℝ)) ∧
      nu3star G ≤ (∑ i ∈ Finset.range k,
        (((colorPart G col i).cliqueFinset 2).card : ℝ) / 3) + ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨k, H, d, hle, hdisj, hd, hhi, hlo, hval⟩ := h
  have hcp : ∀ i < k, colorPart G (familyColoring H k) i = H i := fun i hi =>
    colorPart_familyColoring G H k hle hdisj hi
  have hclique : ∀ i < k,
      (colorPart G (familyColoring H k) i).cliqueFinset 2 = (H i).cliqueFinset 2 := fun i hi =>
    cliqueFinset_congr_graph (hcp i hi) 2
  have hdeg : ∀ i < k, ∀ e : Finset V,
      edgeTriangleDegree (colorPart G (familyColoring H k) i) e = edgeTriangleDegree (H i) e :=
    fun i hi e => edgeTriangleDegree_congr_graph (hcp i hi) e
  refine ⟨k, familyColoring H k, d, hd, ?_, ?_, ?_⟩
  · intro i hi e he
    rw [hdeg i hi]
    exact hhi i hi e ((hclique i hi) ▸ he)
  · intro i hi
    obtain ⟨Exc, hExc, hlo'⟩ := hlo i hi
    refine ⟨Exc, by rw [hclique i hi]; exact hExc, ?_⟩
    intro e he hne
    rw [hdeg i hi]
    exact hlo' e ((hclique i hi) ▸ he) hne
  · have hsum : ∑ i ∈ Finset.range k,
        (((colorPart G (familyColoring H k) i).cliqueFinset 2).card : ℝ) / 3
        = ∑ i ∈ Finset.range k, (((H i).cliqueFinset 2).card : ℝ) / 3 :=
      Finset.sum_congr rfl (fun i hi => by rw [hclique i (Finset.mem_range.mp hi)])
    rw [hsum]
    exact hval

/-- **The reduction to the family form.**  If every large graph has a near-regular family, then the
structural residual `Nibble.AX1.RegularDecompAt` holds. -/
theorem regularDecompAt_of_family {ε μ η d₀ : ℝ}
    (h : ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], n₀ ≤ Fintype.card V → HasNearRegularFamily G ε μ η d₀) :
    RegularDecompAt ε μ η d₀ := by
  obtain ⟨n₀, hmain⟩ := h
  exact ⟨n₀, fun V _ _ G _ hV => regularDecomp_data_of_family G (hmain V G hV)⟩

/-- **The converse.**  A colour decomposition *is* an edge-disjoint family, so the family form is
equivalent to `Nibble.AX1.RegularDecompAt`: nothing has been smuggled in. -/
theorem hasNearRegularFamily_of_regularDecomp {ε μ η d₀ : ℝ} (h : RegularDecompAt ε μ η d₀) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → HasNearRegularFamily G ε μ η d₀ := by
  classical
  obtain ⟨n₀, hmain⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hV
  obtain ⟨k, col, d, hd, hhi, hlo, hval⟩ := hmain V G hV
  refine ⟨k, fun i => colorPart G col i, d, fun i _ => colorPart_le G col i, ?_, hd, ?_, ?_, ?_⟩
  · intro i _ j _ hij x y hxi hxj
    exact hij (hxi.2 ▸ hxj.2 ▸ rfl)
  · intro i hi e he
    exact hhi i hi e he
  · intro i hi
    obtain ⟨Exc, hExc, hlo'⟩ := hlo i hi
    exact ⟨Exc, hExc, hlo'⟩
  · exact hval

/-! ### Cleaning: passing to the regularity-reduced graph -/

/-- **The cleaning step.**  Mathlib's `SimpleGraph.regularityReduced` keeps only the edges lying in
an `ε₁/8`-uniform pair of parts of density at least `ε₁/4`; for a uniform equipartition with enough
parts it discards fewer than `ε₁|V|²` edges
(`SimpleGraph.regularityReduced_edges_card_aux`), and deleting `m` edges costs the fractional
optimum at most `m` (`Nibble.AX1.nu3star_le_add_deleted`).  So a near-regular family for the reduced
graph is one for `G`, at accuracy `ε + ε₁`. -/
theorem hasNearRegularFamily_of_reduced [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε₁ μ η d₀ : ℝ} (hε₁ : 0 < ε₁) (P : Finpartition (univ : Finset V))
    (hP : P.IsEquipartition) (hPl : 4 / ε₁ ≤ (P.parts.card : ℝ))
    (hPu : P.IsUniform G (ε₁ / 8))
    (h : HasNearRegularFamily (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀) :
    HasNearRegularFamily G (ε + ε₁) μ η d₀ := by
  classical
  set G' : SimpleGraph V := G.regularityReduced P (ε₁ / 8) (ε₁ / 4) with hG'
  have hle : G' ≤ G := SimpleGraph.regularityReduced_le
  have hedges := SimpleGraph.regularityReduced_edges_card_aux (G := G) (P := P) (ε := ε₁)
    hε₁ hP hPu hPl
  have hedges' : (G.edgeFinset.card : ℝ) - (G'.edgeFinset.card : ℝ)
      < ε₁ * (Fintype.card V : ℝ) ^ 2 := by
    have hcast : ((Fintype.card V ^ 2 : ℕ) : ℝ) = (Fintype.card V : ℝ) ^ 2 := by push_cast; ring
    rw [hcast] at hedges
    linarith only [hedges]
  have hcnt := card_clique2_sdiff_le G G' hle
  have hgap : nu3star G ≤ nu3star G' + ε₁ * (Fintype.card V : ℝ) ^ 2 := by
    have := nu3star_le_add_deleted G G' hle
    linarith only [hedges', hcnt, this]
  exact HasNearRegularFamily.mono_of_le hle hgap h

/-! ### The reduced residual -/

/-- **The reduced residual at parameters `(ε, μ, η, d₀)` and regularity scale `ε₁`**: every
*regularity-reduced* graph — the subgraph of a large graph `G` consisting of the edges inside the
`ε₁/8`-uniform pairs of density at least `ε₁/4` of an `ε₁/8`-uniform equipartition `P` with a
bounded number of parts — which is triangle-rich carries a near-regular family recovering `3ν₃*`
up to `3ε|V|²`.

This is what remains of `Nibble.AX1.RegularDecompResidual` after Szemerédi regularity and the
triangle removal lemma have been applied: all pairs of parts carrying edges are uniform and dense,
so the missing mathematics is the Haxell–Rödl splitting of each uniform pair among the cluster
triples together with the sparsification making the triangle degrees of each triple concentrate at
a common scale. -/
def ReducedFamilyAt (ε μ η d₀ ε₁ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)),
    n₀ ≤ Fintype.card V →
    P.IsEquipartition →
    4 / ε₁ ≤ (P.parts.card : ℝ) →
    (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
    P.IsUniform G (ε₁ / 8) →
    SimpleGraph.triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3
      ≤ ((((G.regularityReduced P (ε₁ / 8) (ε₁ / 4))).cliqueFinset 3).card : ℝ) →
    HasNearRegularFamily (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) ε μ η d₀

/-- **The reduced residual**: at every window of parameters, *for some* regularity scale `ε₁` as
small as one likes.  The scale is existentially quantified — the cleaning loss it causes is paid for
out of the accuracy `ε` — so a proof is free to run the regularity lemma as finely as it needs. -/
def ReducedFamilyResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ μ : ℝ, 0 < μ → ∀ η : ℝ, 0 < η → ∀ d₀ : ℝ, 0 < d₀ →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε ∧ ε₁ ≤ 1 ∧ ReducedFamilyAt ε μ η d₀ ε₁

/-- **The reduction of the structural residual to the reduced one.**  Given `ε`, apply Szemerédi's
regularity lemma at the scale `ε₁ ≤ ε/2` supplied by the residual; the reduced graph is either
triangle-poor — and then the empty family already works, by the triangle removal lemma — or
triangle-rich, and then the reduced residual applies.  Cleaning costs at most `ε₁|V|² ≤ (ε/2)|V|²`
of the fractional optimum. -/
theorem regularDecompResidual_of_reducedFamily (h : ReducedFamilyResidual) :
    RegularDecompResidual := by
  classical
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨ε₁, hε₁, hε₁le, hε₁one, n₀, hmain⟩ := h (ε / 2) (by linarith) μ hμ η hη d₀ hd₀
  refine regularDecompAt_of_family ⟨max n₀ (max ⌈4 / ε₁⌉₊ 1), ?_⟩
  intro V _ _ G _ hV
  have hV₀ : n₀ ≤ Fintype.card V := le_trans (le_max_left _ _) hV
  have hVl : ⌈4 / ε₁⌉₊ ≤ Fintype.card V :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hV
  have hV1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hV
  have hne : Nonempty V := Fintype.card_pos_iff.mp hV1
  obtain ⟨P, hP, hPl, hPb, hPu⟩ :=
    szemeredi_regularity G (ε := ε₁ / 8) (l := ⌈4 / ε₁⌉₊) (by positivity) hVl
  have hPl' : 4 / ε₁ ≤ (P.parts.card : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast hPl
  have hPb' : (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast hPb
  set G' : SimpleGraph V := G.regularityReduced P (ε₁ / 8) (ε₁ / 4) with hG'
  have hfam : HasNearRegularFamily G' (ε / 2) μ η d₀ := by
    rcases lt_or_ge (((G'.cliqueFinset 3).card : ℝ))
      (SimpleGraph.triangleRemovalBound (ε / 2) * (Fintype.card V : ℝ) ^ 3) with hpoor | hrich
    · exact hasNearRegularFamily_of_few_triangles G' hpoor
    · exact hmain V G P hV₀ hP hPl' hPb' hPu hrich
  have := hasNearRegularFamily_of_reduced G hε₁ P hP hPl' hPu hfam
  exact this.mono_eps (by linarith)

/-- **The converse.**  The reduced residual is a *weakening* of `Nibble.AX1.RegularDecompResidual`
(reduced graphs are graphs), so by `Nibble.AX1.regularDecompResidual_of_reducedFamily` the two are
equivalent: the passage to regularity-reduced graphs smuggles in no strength. -/
theorem reducedFamilyResidual_of_regularDecompResidual (h : RegularDecompResidual) :
    ReducedFamilyResidual := by
  intro ε hε μ hμ η hη d₀ hd₀
  obtain ⟨n₀, hmain⟩ := hasNearRegularFamily_of_regularDecomp (h ε hε μ hμ η hη d₀ hd₀)
  refine ⟨min ε 1, lt_min hε one_pos, min_le_left _ _, min_le_right _ _, n₀, ?_⟩
  exact fun V _ _ G _ P hV _ _ _ _ _ =>
    hmain V (G.regularityReduced P (min ε 1 / 8) (min ε 1 / 4)) hV

/-- **AX1 from the reduced residual.** -/
theorem ax1_of_reducedFamily (h : ReducedFamilyResidual) : AX1Statement :=
  ax1_of_regularDecomp (regularDecompResidual_of_reducedFamily h)

end Nibble.AX1

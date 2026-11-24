/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM10.TangleLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A Tangle in a Grid (Graph Minors X, Section 7)

This file formalizes Section 7 of N. Robertson and P. D. Seymour,
*Graph Minors. X. Obstructions to tree-decomposition*, J. Combin. Theory Ser. B 52 (1991) 153–190
(pages 171–173):

- Structural lemmas on the `θ`-grid hypergraph `gridHypergraph θ`, its row paths `gridRowPath θ i`,
  its column paths `gridColPath θ j`, and the edge boundary `edgeBoundary (gridHypergraph θ) X`.
- `theorem_7_1` (**Graph Minors X, (7.1)**, page 171): for `X ⊆ E(G)` with `|∂(X)| < θ`, `X`
  includes `E(Pᵢ)` for some `i` if and only if `X` includes `E(Qⱼ)` for some `j`.
- `theorem_7_2` (**Graph Minors X, (7.2)**, page 172, Kleitman–Saks lemma): if
  `X₁ ∪ X₂ ∪ X₃ = E(G)`, then not all of `X₁, X₂, X₃` are small in `G`.
- `theorem_7_3` (**Graph Minors X, (7.3)**, page 173): `gridTangle θ` is a tangle in
  `gridHypergraph θ` of order `θ` for `θ ≥ 2`.
-/

public section

namespace GraphMinor.GM10

open Graph SimpleGraph Hypergraph

/-! ## Basic properties of `gridHypergraph`, `gridRowPath`, and `gridColPath` -/

/-- The underlying simple graph `pathGraph θ □ pathGraph θ` of the `θ`-grid. -/
private abbrev gridSimpleGraph (θ : ℕ) : SimpleGraph (Fin θ × Fin θ) :=
  pathGraph θ □ pathGraph θ

@[simp]
theorem gridHypergraph_vertexSet (θ : ℕ) :
    (gridHypergraph θ).vertexSet = Set.univ := rfl

@[simp]
theorem gridHypergraph_edgeSet (θ : ℕ) :
    (gridHypergraph θ).edgeSet = (pathGraph θ □ pathGraph θ).edgeSet := rfl

theorem gridHypergraph_inc_iff {θ : ℕ} {e : Sym2 (Fin θ × Fin θ)} {v : Fin θ × Fin θ} :
    (gridHypergraph θ).Inc e v ↔
      e ∈ (pathGraph θ □ pathGraph θ).edgeSet ∧ v ∈ e := by
  change (Graph.ofSimpleGraph (gridSimpleGraph θ)).Inc e v ↔
    e ∈ (gridSimpleGraph θ).edgeSet ∧ v ∈ e
  constructor
  · rintro ⟨w, rfl, he⟩
    exact ⟨he, Sym2.mem_mk_left v w⟩
  · rintro ⟨he, hv⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
    exact ⟨w, rfl, he⟩

theorem gridHypergraph_inc_sym2 {θ : ℕ} {u w v : Fin θ × Fin θ} :
    (gridHypergraph θ).Inc s(u, w) v ↔
      (pathGraph θ □ pathGraph θ).Adj u w ∧ (v = u ∨ v = w) := by
  rw [gridHypergraph_inc_iff, SimpleGraph.mem_edgeSet, Sym2.mem_iff]

@[simp]
theorem gridRowPath_vertexSet (θ : ℕ) (i : Fin θ) :
    (gridRowPath θ i).vertexSet = {v : Fin θ × Fin θ | v.1 = i} := rfl

@[simp]
theorem gridColPath_vertexSet (θ : ℕ) (j : Fin θ) :
    (gridColPath θ j).vertexSet = {v : Fin θ × Fin θ | v.2 = j} := rfl

/-- Construct a horizontal edge in row `i` between columns `a` and `a + 1`. -/
private def rowEdge {θ : ℕ} (i : Fin θ) (a : ℕ) (ha : a + 1 < θ) : Sym2 (Fin θ × Fin θ) :=
  s((i, ⟨a, Nat.lt_of_succ_lt ha⟩), (i, ⟨a + 1, ha⟩))

/-- Construct a vertical edge in column `j` between rows `a` and `a + 1`. -/
private def colEdge {θ : ℕ} (j : Fin θ) (a : ℕ) (ha : a + 1 < θ) : Sym2 (Fin θ × Fin θ) :=
  s((⟨a, Nat.lt_of_succ_lt ha⟩, j), (⟨a + 1, ha⟩, j))

private theorem rowEdge_adj {θ : ℕ} (i : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    (gridSimpleGraph θ).Adj (i, ⟨a, Nat.lt_of_succ_lt ha⟩) (i, ⟨a + 1, ha⟩) := by
  rw [boxProd_adj]
  right
  exact ⟨pathGraph_adj.2 (Or.inl rfl), rfl⟩

private theorem colEdge_adj {θ : ℕ} (j : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    (gridSimpleGraph θ).Adj (⟨a, Nat.lt_of_succ_lt ha⟩, j) (⟨a + 1, ha⟩, j) := by
  rw [boxProd_adj]
  left
  exact ⟨pathGraph_adj.2 (Or.inl rfl), rfl⟩

private theorem rowEdge_mem_gridRowPath {θ : ℕ} (i : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    rowEdge i a ha ∈ (gridRowPath θ i).edgeSet := by
  refine ⟨rowEdge_adj i a ha, ?_⟩
  intro v hv
  rw [rowEdge, gridHypergraph_inc_sym2] at hv
  rcases hv.2 with rfl | rfl <;> rfl

private theorem colEdge_mem_gridColPath {θ : ℕ} (j : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    colEdge j a ha ∈ (gridColPath θ j).edgeSet := by
  refine ⟨colEdge_adj j a ha, ?_⟩
  intro v hv
  rw [colEdge, gridHypergraph_inc_sym2] at hv
  rcases hv.2 with rfl | rfl <;> rfl

private theorem rowEdge_mem_gridHypergraph {θ : ℕ} (i : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    rowEdge i a ha ∈ (gridHypergraph θ).edgeSet :=
  (rowEdge_mem_gridRowPath i a ha).1

private theorem colEdge_mem_gridHypergraph {θ : ℕ} (j : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    colEdge j a ha ∈ (gridHypergraph θ).edgeSet :=
  (colEdge_mem_gridColPath j a ha).1

private theorem rowEdge_inc_left {θ : ℕ} (i : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    (gridHypergraph θ).Inc (rowEdge i a ha) (i, ⟨a, Nat.lt_of_succ_lt ha⟩) :=
  gridHypergraph_inc_sym2.2 ⟨rowEdge_adj i a ha, Or.inl rfl⟩

private theorem rowEdge_inc_right {θ : ℕ} (i : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    (gridHypergraph θ).Inc (rowEdge i a ha) (i, ⟨a + 1, ha⟩) :=
  gridHypergraph_inc_sym2.2 ⟨rowEdge_adj i a ha, Or.inr rfl⟩

private theorem colEdge_inc_left {θ : ℕ} (j : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    (gridHypergraph θ).Inc (colEdge j a ha) (⟨a, Nat.lt_of_succ_lt ha⟩, j) :=
  gridHypergraph_inc_sym2.2 ⟨colEdge_adj j a ha, Or.inl rfl⟩

private theorem colEdge_inc_right {θ : ℕ} (j : Fin θ) (a : ℕ) (ha : a + 1 < θ) :
    (gridHypergraph θ).Inc (colEdge j a ha) (⟨a + 1, ha⟩, j) :=
  gridHypergraph_inc_sym2.2 ⟨colEdge_adj j a ha, Or.inr rfl⟩

/-- Every edge of `gridRowPath θ i` is `rowEdge i a ha` for some `a` with `a + 1 < θ`. -/
private theorem mem_gridRowPath_edgeSet_iff {θ : ℕ} {i : Fin θ} {e : Sym2 (Fin θ × Fin θ)} :
    e ∈ (gridRowPath θ i).edgeSet ↔
      ∃ (a : ℕ) (ha : a + 1 < θ), e = rowEdge i a ha := by
  constructor
  · rintro ⟨he, hrow⟩
    induction e using Sym2.ind with | _ u w =>
    have hadj : (gridSimpleGraph θ).Adj u w := he
    have hu : u.1 = i := hrow u (gridHypergraph_inc_sym2.2 ⟨hadj, Or.inl rfl⟩)
    have hw : w.1 = i := hrow w (gridHypergraph_inc_sym2.2 ⟨hadj, Or.inr rfl⟩)
    rcases boxProd_adj.1 hadj with ⟨h1, _⟩ | ⟨h2, _⟩
    · exfalso
      have huw : u.1 = w.1 := hu.trans hw.symm
      exact (pathGraph θ).loopless.irrefl u.1 (huw ▸ h1)
    · rcases pathGraph_adj.1 h2 with hlt | hlt
      · have ha : u.2.val + 1 < θ := by omega
        refine ⟨u.2.val, ha, ?_⟩
        have hu_eq : u = (i, ⟨u.2.val, Nat.lt_of_succ_lt ha⟩) :=
          Prod.ext hu rfl
        have hw_eq : w = (i, ⟨u.2.val + 1, ha⟩) :=
          Prod.ext hw (Fin.ext hlt.symm)
        rw [rowEdge, ← hu_eq, ← hw_eq]
      · have ha : w.2.val + 1 < θ := by omega
        refine ⟨w.2.val, ha, ?_⟩
        have hw_eq : w = (i, ⟨w.2.val, Nat.lt_of_succ_lt ha⟩) :=
          Prod.ext hw rfl
        have hu_eq : u = (i, ⟨w.2.val + 1, ha⟩) :=
          Prod.ext hu (Fin.ext hlt.symm)
        rw [rowEdge, ← hw_eq, ← hu_eq, Sym2.eq_swap]
  · rintro ⟨a, ha, rfl⟩
    exact rowEdge_mem_gridRowPath i a ha

/-- Every edge of `gridColPath θ j` is `colEdge j a ha` for some `a` with `a + 1 < θ`. -/
private theorem mem_gridColPath_edgeSet_iff {θ : ℕ} {j : Fin θ} {e : Sym2 (Fin θ × Fin θ)} :
    e ∈ (gridColPath θ j).edgeSet ↔
      ∃ (a : ℕ) (ha : a + 1 < θ), e = colEdge j a ha := by
  constructor
  · rintro ⟨he, hcol⟩
    induction e using Sym2.ind with | _ u w =>
    have hadj : (gridSimpleGraph θ).Adj u w := he
    have hu : u.2 = j := hcol u (gridHypergraph_inc_sym2.2 ⟨hadj, Or.inl rfl⟩)
    have hw : w.2 = j := hcol w (gridHypergraph_inc_sym2.2 ⟨hadj, Or.inr rfl⟩)
    rcases boxProd_adj.1 hadj with ⟨h1, _⟩ | ⟨h2, _⟩
    · rcases pathGraph_adj.1 h1 with hlt | hlt
      · have ha : u.1.val + 1 < θ := by omega
        refine ⟨u.1.val, ha, ?_⟩
        have hu_eq : u = (⟨u.1.val, Nat.lt_of_succ_lt ha⟩, j) :=
          Prod.ext rfl hu
        have hw_eq : w = (⟨u.1.val + 1, ha⟩, j) :=
          Prod.ext (Fin.ext hlt.symm) hw
        rw [colEdge, ← hu_eq, ← hw_eq]
      · have ha : w.1.val + 1 < θ := by omega
        refine ⟨w.1.val, ha, ?_⟩
        have hw_eq : w = (⟨w.1.val, Nat.lt_of_succ_lt ha⟩, j) :=
          Prod.ext rfl hw
        have hu_eq : u = (⟨w.1.val + 1, ha⟩, j) :=
          Prod.ext (Fin.ext hlt.symm) hu
        rw [colEdge, ← hw_eq, ← hu_eq, Sym2.eq_swap]
    · exfalso
      have huw : u.2 = w.2 := hu.trans hw.symm
      exact (pathGraph θ).loopless.irrefl u.2 (huw ▸ h2)
  · rintro ⟨a, ha, rfl⟩
    exact colEdge_mem_gridColPath j a ha

/-- Every vertex `(i, j)` in a `θ`-grid with `θ ≥ 2` is incident with an edge of `gridRowPath θ i`.
-/
private theorem exists_mem_gridRowPath_inc {θ : ℕ} (hθ : 2 ≤ θ) (i j : Fin θ) :
    ∃ e ∈ (gridRowPath θ i).edgeSet, (gridHypergraph θ).Inc e (i, j) := by
  by_cases hj : j.val + 1 < θ
  · exact ⟨rowEdge i j.val hj, rowEdge_mem_gridRowPath i j.val hj, rowEdge_inc_left i j.val hj⟩
  · have hj_pos : 0 < j.val := by omega
    have ha : (j.val - 1) + 1 < θ := by
      rw [Nat.sub_add_cancel hj_pos]
      exact j.isLt
    refine ⟨rowEdge i (j.val - 1) ha, rowEdge_mem_gridRowPath i (j.val - 1) ha, ?_⟩
    have hjeq : (⟨(j.val - 1) + 1, ha⟩ : Fin θ) = j := Fin.ext (Nat.sub_add_cancel hj_pos)
    simpa [hjeq] using rowEdge_inc_right i (j.val - 1) ha

/-- Every vertex `(i, j)` in a `θ`-grid with `θ ≥ 2` is incident with an edge of `gridColPath θ j`.
-/
private theorem exists_mem_gridColPath_inc {θ : ℕ} (hθ : 2 ≤ θ) (i j : Fin θ) :
    ∃ e ∈ (gridColPath θ j).edgeSet, (gridHypergraph θ).Inc e (i, j) := by
  by_cases hi : i.val + 1 < θ
  · exact ⟨colEdge j i.val hi, colEdge_mem_gridColPath j i.val hi, colEdge_inc_left j i.val hi⟩
  · have hi_pos : 0 < i.val := by omega
    have ha : (i.val - 1) + 1 < θ := by
      rw [Nat.sub_add_cancel hi_pos]
      exact i.isLt
    refine ⟨colEdge j (i.val - 1) ha, colEdge_mem_gridColPath j (i.val - 1) ha, ?_⟩
    have hieq : (⟨(i.val - 1) + 1, ha⟩ : Fin θ) = i := Fin.ext (Nat.sub_add_cancel hi_pos)
    simpa [hieq] using colEdge_inc_right j (i.val - 1) ha

/-! ## Boundary vertices along a column or row -/

private theorem mem_edgeBoundary_gridHypergraph_iff {θ : ℕ}
    {X : Set (Sym2 (Fin θ × Fin θ))} {v : Fin θ × Fin θ} :
    v ∈ edgeBoundary (gridHypergraph θ) X ↔
      (∃ e ∈ X, (gridHypergraph θ).Inc e v) ∧
      (∃ e ∈ (gridHypergraph θ).edgeSet \ X, (gridHypergraph θ).Inc e v) := by
  simp [edgeBoundary]

/-- If `(i₀, j)` is incident with an edge in `X`, and `colEdge j a ha ∉ X` with `i₀.val ≤ a`, then
there is a vertex `(i₁, j) ∈ edgeBoundary (gridHypergraph θ) X` with `i₀.val ≤ i₁.val ≤ a`. -/
private theorem exists_le_mem_edgeBoundary_col {θ : ℕ} {X : Set (Sym2 (Fin θ × Fin θ))}
    (j : Fin θ) {i₀ : Fin θ} (hX₀ : ∃ e ∈ X, (gridHypergraph θ).Inc e (i₀, j))
    {a : ℕ} (ha : a + 1 < θ) (hia : i₀.val ≤ a) (hna : colEdge j a ha ∉ X) :
    ∃ i₁ : Fin θ, i₀.val ≤ i₁.val ∧ i₁.val ≤ a ∧
      (i₁, j) ∈ edgeBoundary (gridHypergraph θ) X := by
  classical
  have hex : ∃ b : ℕ, i₀.val ≤ b ∧ b ≤ a ∧ ∃ hb : b + 1 < θ, colEdge j b hb ∉ X :=
    ⟨a, hia, le_rfl, ha, hna⟩
  let b := Nat.find hex
  obtain ⟨hib, hba, hb, hnb⟩ := Nat.find_spec hex
  let i₁ : Fin θ := ⟨b, Nat.lt_of_succ_lt hb⟩
  refine ⟨i₁, hib, hba, mem_edgeBoundary_gridHypergraph_iff.2 ⟨?_, ?_⟩⟩
  · rcases eq_or_lt_of_le hib with heq | hlt
    · have hi₁ : i₁ = i₀ := Fin.ext heq.symm
      rwa [hi₁]
    · have hlt_find : b - 1 < b := Nat.sub_lt (Nat.zero_lt_of_lt hlt) Nat.one_pos
      have hmin := Nat.find_min hex hlt_find
      have hb1_lt : (b - 1) + 1 < θ := by
        rw [Nat.sub_add_cancel (Nat.one_le_of_lt hlt)]
        exact Nat.lt_of_succ_lt hb
      have hmemX : colEdge j (b - 1) hb1_lt ∈ X := by
        by_contra hnotX
        exact hmin ⟨Nat.le_sub_one_of_lt hlt, (Nat.sub_le b 1).trans hba, hb1_lt, hnotX⟩
      refine ⟨colEdge j (b - 1) hb1_lt, hmemX, ?_⟩
      have heq_b : (⟨(b - 1) + 1, hb1_lt⟩ : Fin θ) = i₁ :=
        Fin.ext (Nat.sub_add_cancel (Nat.one_le_of_lt hlt))
      simpa [heq_b] using colEdge_inc_right j (b - 1) hb1_lt
  · exact ⟨colEdge j b hb, ⟨colEdge_mem_gridHypergraph j b hb, hnb⟩, colEdge_inc_left j b hb⟩

/-- If `(i₀, j)` is incident with an edge in `X`, and `colEdge j a ha ∉ X` with `a < i₀.val`, then
there is a vertex `(i₂, j) ∈ edgeBoundary (gridHypergraph θ) X` with `a < i₂.val ≤ i₀.val`. -/
private theorem exists_gt_mem_edgeBoundary_col {θ : ℕ} {X : Set (Sym2 (Fin θ × Fin θ))}
    (j : Fin θ) {i₀ : Fin θ} (hX₀ : ∃ e ∈ X, (gridHypergraph θ).Inc e (i₀, j))
    {a : ℕ} (ha : a + 1 < θ) (hai : a < i₀.val) (hna : colEdge j a ha ∉ X) :
    ∃ i₂ : Fin θ, a < i₂.val ∧ i₂.val ≤ i₀.val ∧
      (i₂, j) ∈ edgeBoundary (gridHypergraph θ) X := by
  classical
  have hex : ∃ d : ℕ, d ≤ i₀.val - 1 - a ∧
      ∃ hd : (i₀.val - 1 - d) + 1 < θ, colEdge j (i₀.val - 1 - d) hd ∉ X := by
    refine ⟨i₀.val - 1 - a, le_rfl, ?_⟩
    have heq : i₀.val - 1 - (i₀.val - 1 - a) = a := by omega
    rw [heq]
    exact ⟨ha, hna⟩
  let d := Nat.find hex
  obtain ⟨hda, hd, hnd⟩ := Nat.find_spec hex
  let b := i₀.val - 1 - d
  let i₂ : Fin θ := ⟨b + 1, hd⟩
  have hab : a < b + 1 := by omega
  have hbi : b + 1 ≤ i₀.val := by omega
  refine ⟨i₂, hab, hbi, mem_edgeBoundary_gridHypergraph_iff.2 ⟨?_, ?_⟩⟩
  · rcases eq_or_lt_of_le (Nat.zero_le d) with hd0 | hd_pos
    · have hi₂ : i₂ = i₀ := by
        ext
        dsimp [i₂, b]
        omega
      rwa [hi₂]
    · have hlt_find : d - 1 < d := Nat.sub_lt hd_pos Nat.one_pos
      have hmin := Nat.find_min hex hlt_find
      have hb1_eq : i₀.val - 1 - (d - 1) = b + 1 := by omega
      have hb1_lt : (b + 1) + 1 < θ := by
        have : b + 2 ≤ i₀.val := by omega
        exact Nat.lt_of_le_of_lt this i₀.isLt
      have hmemX : colEdge j (b + 1) hb1_lt ∈ X := by
        by_contra hnotX
        apply hmin
        refine ⟨by omega, ?_⟩
        rw [hb1_eq]
        exact ⟨hb1_lt, hnotX⟩
      exact ⟨colEdge j (b + 1) hb1_lt, hmemX, colEdge_inc_left j (b + 1) hb1_lt⟩
  · exact ⟨colEdge j b hd, ⟨colEdge_mem_gridHypergraph j b hd, hnd⟩, colEdge_inc_right j b hd⟩

/-- If `V(Qⱼ)` contains a vertex incident with an edge in `X` and `¬ E(Qⱼ) ⊆ X`, then `V(Qⱼ)`
meets `∂(X)`. -/
private theorem gridColPath_meets_edgeBoundary {θ : ℕ} {X : Set (Sym2 (Fin θ × Fin θ))}
    (j : Fin θ) {i₀ : Fin θ} (hX₀ : ∃ e ∈ X, (gridHypergraph θ).Inc e (i₀, j))
    (hnot : ¬ (gridColPath θ j).edgeSet ⊆ X) :
    ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X).Nonempty := by
  obtain ⟨e, heQ, heX⟩ := Set.not_subset.1 hnot
  obtain ⟨a, ha, rfl⟩ := mem_gridColPath_edgeSet_iff.1 heQ
  rcases le_or_gt i₀.val a with hle | hgt
  · obtain ⟨i₁, _, _, hmem⟩ := exists_le_mem_edgeBoundary_col j hX₀ ha hle heX
    exact ⟨(i₁, j), rfl, hmem⟩
  · obtain ⟨i₂, _, _, hmem⟩ := exists_gt_mem_edgeBoundary_col j hX₀ ha hgt heX
    exact ⟨(i₂, j), rfl, hmem⟩

/-- If both ends `(0, j)` and `(θ - 1, j)` of `Qⱼ` are incident with edges in `X` and
`¬ E(Qⱼ) ⊆ X`, then `|V(Qⱼ) ∩ ∂(X)| ≥ 2` (Graph Minors X, Section 7, proof of (7.2), page 172). -/
private theorem two_le_ncard_gridColPath_inter_edgeBoundary {θ : ℕ} (hθ : 2 ≤ θ)
    {X : Set (Sym2 (Fin θ × Fin θ))} (j : Fin θ)
    (hX_top : ∃ e ∈ X, (gridHypergraph θ).Inc e (⟨0, by omega⟩, j))
    (hX_bot : ∃ e ∈ X, (gridHypergraph θ).Inc e (⟨θ - 1, by omega⟩, j))
    (hnot : ¬ (gridColPath θ j).edgeSet ⊆ X) :
    2 ≤ ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X).ncard := by
  obtain ⟨e, heQ, heX⟩ := Set.not_subset.1 hnot
  obtain ⟨a, ha, rfl⟩ := mem_gridColPath_edgeSet_iff.1 heQ
  obtain ⟨i₁, _, hi₁a, hmem₁⟩ :=
    exists_le_mem_edgeBoundary_col j hX_top ha (Nat.zero_le a) heX
  obtain ⟨i₂, hai₂, _, hmem₂⟩ :=
    exists_gt_mem_edgeBoundary_col j hX_bot ha (by dsimp; omega) heX
  have hne : (i₁, j) ≠ (i₂, j) := by
    intro h
    have : i₁.val = i₂.val := congrArg (fun p : Fin θ × Fin θ ↦ p.1.val) h
    omega
  have hsub : ({(i₁, j), (i₂, j)} : Set (Fin θ × Fin θ)) ⊆
      (gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X := by
    rintro v (rfl | rfl)
    · exact ⟨rfl, hmem₁⟩
    · exact ⟨rfl, hmem₂⟩
  have hcard : ({(i₁, j), (i₂, j)} : Set (Fin θ × Fin θ)).ncard = 2 :=
    Set.ncard_pair hne
  rw [← hcard]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-! ## Row-column transpose symmetry -/

/-- Swapping the two coordinates of `Fin θ × Fin θ` induces an involution on edges of the
`θ`-grid. -/
private def swapEdge (θ : ℕ) (e : Sym2 (Fin θ × Fin θ)) : Sym2 (Fin θ × Fin θ) :=
  Sym2.map Prod.swap e

@[simp]
private theorem swapEdge_swapEdge {θ : ℕ} (e : Sym2 (Fin θ × Fin θ)) :
    swapEdge θ (swapEdge θ e) = e := by
  induction e using Sym2.ind with | _ x y =>
  simp [swapEdge]

private theorem gridSimpleGraph_adj_swap {θ : ℕ} {u v : Fin θ × Fin θ} :
    (gridSimpleGraph θ).Adj u.swap v.swap ↔ (gridSimpleGraph θ).Adj u v := by
  simp [gridSimpleGraph, boxProd_adj, or_comm]

private theorem swapEdge_mem_gridHypergraph {θ : ℕ} {e : Sym2 (Fin θ × Fin θ)} :
    swapEdge θ e ∈ (gridHypergraph θ).edgeSet ↔ e ∈ (gridHypergraph θ).edgeSet := by
  induction e using Sym2.ind with | _ u v =>
  exact gridSimpleGraph_adj_swap

private theorem gridHypergraph_inc_swapEdge {θ : ℕ} {e : Sym2 (Fin θ × Fin θ)}
    {v : Fin θ × Fin θ} :
    (gridHypergraph θ).Inc (swapEdge θ e) v.swap ↔ (gridHypergraph θ).Inc e v := by
  have h1 : (gridHypergraph θ).Inc (swapEdge θ e) v.swap ↔
      swapEdge θ e ∈ (gridSimpleGraph θ).edgeSet ∧ v.swap ∈ swapEdge θ e := gridHypergraph_inc_iff
  have h2 : (gridHypergraph θ).Inc e v ↔
      e ∈ (gridSimpleGraph θ).edgeSet ∧ v ∈ e := gridHypergraph_inc_iff
  rw [h1, h2]
  refine and_congr swapEdge_mem_gridHypergraph ?_
  induction e using Sym2.ind with | _ x y =>
  simp [swapEdge, Prod.swap_inj]

private theorem swapEdge_mem_gridRowPath_iff {θ : ℕ} {i : Fin θ} {e : Sym2 (Fin θ × Fin θ)} :
    swapEdge θ e ∈ (gridRowPath θ i).edgeSet ↔ e ∈ (gridColPath θ i).edgeSet := by
  simp only [gridRowPath, gridColPath, Set.mem_sep_iff, swapEdge_mem_gridHypergraph]
  refine and_congr_right fun _ ↦ ⟨fun h v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · simpa using h v.swap (gridHypergraph_inc_swapEdge.2 hv)
  · have hv' : (gridHypergraph θ).Inc e v.swap :=
      (gridHypergraph_inc_swapEdge (v := v.swap)).1 (by simpa using hv)
    exact h v.swap hv'

private theorem swapEdge_mem_gridColPath_iff {θ : ℕ} {j : Fin θ} {e : Sym2 (Fin θ × Fin θ)} :
    swapEdge θ e ∈ (gridColPath θ j).edgeSet ↔ e ∈ (gridRowPath θ j).edgeSet := by
  simp only [gridRowPath, gridColPath, Set.mem_sep_iff, swapEdge_mem_gridHypergraph]
  refine and_congr_right fun _ ↦ ⟨fun h v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · simpa using h v.swap (gridHypergraph_inc_swapEdge.2 hv)
  · have hv' : (gridHypergraph θ).Inc e v.swap :=
      (gridHypergraph_inc_swapEdge (v := v.swap)).1 (by simpa using hv)
    exact h v.swap hv'

private theorem mem_edgeBoundary_preimage_swapEdge {θ : ℕ} {X : Set (Sym2 (Fin θ × Fin θ))}
    {v : Fin θ × Fin θ} :
    v ∈ edgeBoundary (gridHypergraph θ) (swapEdge θ ⁻¹' X) ↔
      v.swap ∈ edgeBoundary (gridHypergraph θ) X := by
  rw [mem_edgeBoundary_gridHypergraph_iff, mem_edgeBoundary_gridHypergraph_iff]
  constructor
  · rintro ⟨⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂X⟩, hinc₂⟩⟩
    exact ⟨⟨swapEdge θ e₁, he₁, gridHypergraph_inc_swapEdge.2 hinc₁⟩,
      ⟨swapEdge θ e₂, ⟨swapEdge_mem_gridHypergraph.2 he₂G, he₂X⟩,
        gridHypergraph_inc_swapEdge.2 hinc₂⟩⟩
  · rintro ⟨⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂X⟩, hinc₂⟩⟩
    refine ⟨⟨swapEdge θ e₁, by simpa using he₁, ?_⟩,
      ⟨swapEdge θ e₂, ⟨swapEdge_mem_gridHypergraph.2 he₂G, by simpa using he₂X⟩, ?_⟩⟩
    · have := gridHypergraph_inc_swapEdge.2 hinc₁
      simpa using this
    · have := gridHypergraph_inc_swapEdge.2 hinc₂
      simpa using this

private theorem ncard_edgeBoundary_preimage_swapEdge {θ : ℕ} (X : Set (Sym2 (Fin θ × Fin θ))) :
    (edgeBoundary (gridHypergraph θ) (swapEdge θ ⁻¹' X)).ncard =
      (edgeBoundary (gridHypergraph θ) X).ncard := by
  refine Set.ncard_congr (fun v _ ↦ v.swap)
    (fun v hv ↦ mem_edgeBoundary_preimage_swapEdge.1 hv)
    (fun _ _ _ _ h ↦ Prod.swap_inj.1 h)
    (fun w hw ↦ ⟨w.swap, ?_, Prod.swap_swap w⟩)
  rw [mem_edgeBoundary_preimage_swapEdge, Prod.swap_swap]
  exact hw

/-- If `V(Pᵢ)` contains a vertex incident with an edge in `X` and `¬ E(Pᵢ) ⊆ X`, then `V(Pᵢ)`
meets `∂(X)`. -/
private theorem gridRowPath_meets_edgeBoundary {θ : ℕ} {X : Set (Sym2 (Fin θ × Fin θ))}
    (i : Fin θ) {j₀ : Fin θ} (hX₀ : ∃ e ∈ X, (gridHypergraph θ).Inc e (i, j₀))
    (hnot : ¬ (gridRowPath θ i).edgeSet ⊆ X) :
    ((gridRowPath θ i).vertexSet ∩ edgeBoundary (gridHypergraph θ) X).Nonempty := by
  have hX₀' : ∃ e ∈ swapEdge θ ⁻¹' X, (gridHypergraph θ).Inc e (j₀, i) := by
    obtain ⟨e, heX, hinc⟩ := hX₀
    refine ⟨swapEdge θ e, by simpa using heX, ?_⟩
    have := gridHypergraph_inc_swapEdge.2 hinc
    simpa using this
  have hnot' : ¬ (gridColPath θ i).edgeSet ⊆ swapEdge θ ⁻¹' X := by
    intro hsub
    apply hnot
    intro e he
    have hm : swapEdge θ e ∈ swapEdge θ ⁻¹' X := hsub (swapEdge_mem_gridColPath_iff.2 he)
    simpa using hm
  obtain ⟨v, hvQ, hvB⟩ := gridColPath_meets_edgeBoundary i hX₀' hnot'
  exact ⟨v.swap, hvQ, mem_edgeBoundary_preimage_swapEdge.1 hvB⟩

/-! ## Proof of (7.1) -/

/-- Forward direction of **Graph Minors X, (7.1)** (page 171): if `|∂(X)| < θ` and `E(Pᵢ) ⊆ X` for
some `i`, then `E(Qⱼ) ⊆ X` for some `j`. -/
private theorem theorem_7_1_mp {θ : ℕ} (hθ : 2 ≤ θ) {X : Set (Sym2 (Fin θ × Fin θ))}
    (hB : (edgeBoundary (gridHypergraph θ) X).ncard < θ)
    (hP : ∃ i : Fin θ, (gridRowPath θ i).edgeSet ⊆ X) :
    ∃ j : Fin θ, (gridColPath θ j).edgeSet ⊆ X := by
  obtain ⟨i, hi⟩ := hP
  by_contra! hno
  have hmeet : ∀ j : Fin θ,
      ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X).Nonempty := by
    intro j
    obtain ⟨e, heP, hinc⟩ := exists_mem_gridRowPath_inc hθ i j
    exact gridColPath_meets_edgeBoundary j ⟨e, hi heP, hinc⟩ (hno j)
  choose f hf using hmeet
  have hinj : Function.Injective f := by
    intro j₁ j₂ heq
    have h₁ : (f j₁).2 = j₁ := (hf j₁).1
    have h₂ : (f j₂).2 = j₂ := (hf j₂).1
    rw [← h₁, ← h₂, heq]
  have hsub : Set.range f ⊆ edgeBoundary (gridHypergraph θ) X := by
    rintro _ ⟨j, rfl⟩
    exact (hf j).2
  have hcard_range : (Set.range f).ncard = θ := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : (Set.range f).ncard ≤ (edgeBoundary (gridHypergraph θ) X).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

private theorem theorem_7_1_iff {θ : ℕ} (hθ : 2 ≤ θ) {X : Set (Sym2 (Fin θ × Fin θ))}
    (hB : (edgeBoundary (gridHypergraph θ) X).ncard < θ) :
    (∃ i : Fin θ, (gridRowPath θ i).edgeSet ⊆ X) ↔
      (∃ j : Fin θ, (gridColPath θ j).edgeSet ⊆ X) := by
  constructor
  · exact theorem_7_1_mp hθ hB
  · intro ⟨j, hj⟩
    have hB' : (edgeBoundary (gridHypergraph θ) (swapEdge θ ⁻¹' X)).ncard < θ := by
      rwa [ncard_edgeBoundary_preimage_swapEdge]
    have hP' : ∃ i : Fin θ, (gridRowPath θ i).edgeSet ⊆ swapEdge θ ⁻¹' X := by
      refine ⟨j, fun e he ↦ ?_⟩
      change swapEdge θ e ∈ X
      exact hj (swapEdge_mem_gridColPath_iff.2 he)
    obtain ⟨i, hi⟩ := theorem_7_1_mp hθ hB' hP'
    refine ⟨i, fun e he ↦ ?_⟩
    have hm : swapEdge θ e ∈ swapEdge θ ⁻¹' X := hi (swapEdge_mem_gridColPath_iff.2 he)
    simpa using hm

/-- **Graph Minors X, (7.1)** (page 171):
"If $X \subseteq E(G)$ and $|\partial(X)| < \theta$ then $X$ includes $E(P_i)$ for some $i$
$(1 \le i \le \theta)$ if and only if $X$ includes $E(Q_j)$ for some $j$ $(1 \le j \le
\theta)$." -/
theorem theorem_7_1_proof {θ : ℕ} (hθ : 2 ≤ θ) {X : Set (Sym2 (Fin θ × Fin θ))}
    (_hX : X ⊆ (gridHypergraph θ).edgeSet)
    (hB : (edgeBoundary (gridHypergraph θ) X).ncard < θ) :
    (∃ i : Fin θ, (gridRowPath θ i).edgeSet ⊆ X) ↔
      (∃ j : Fin θ, (gridColPath θ j).edgeSet ⊆ X) :=
  theorem_7_1_iff hθ hB

/-! ## Row-reversal symmetry and column partitioning for (7.2) -/

/-- If `X` is small in the `θ`-grid (`θ ≥ 2`), then `X` includes `E(Qⱼ)` for no `j`. -/
private theorem IsSmallEdgeSet.not_gridColPath_subset {θ : ℕ} (hθ : 2 ≤ θ)
    {X : Set (Sym2 (Fin θ × Fin θ))} (hX : IsSmallEdgeSet θ X) (j : Fin θ) :
    ¬ (gridColPath θ j).edgeSet ⊆ X := by
  intro hj
  obtain ⟨i, hi⟩ := (theorem_7_1_iff hθ hX.1).2 ⟨j, hj⟩
  exact hX.2 i hi

/-- Partitioning a vertex subset `S` of the `θ`-grid by columns: `|S| = ∑ⱼ |V(Qⱼ) ∩ S|`. -/
private theorem ncard_eq_sum_gridColPath_inter {θ : ℕ} (S : Set (Fin θ × Fin θ)) :
    S.ncard = ∑ j : Fin θ, ((gridColPath θ j).vertexSet ∩ S).ncard := by
  have hsum : ∀ s : Finset (Fin θ),
      (⋃ j ∈ s, ((gridColPath θ j).vertexSet ∩ S)).ncard =
        ∑ j ∈ s, ((gridColPath θ j).vertexSet ∩ S).ncard := by
    intro s
    induction s using Finset.cons_induction_on with
    | empty => simp
    | cons a s ha ih =>
      have hbi : (⋃ j ∈ Finset.cons a s ha, (gridColPath θ j).vertexSet ∩ S) =
          ((gridColPath θ a).vertexSet ∩ S) ∪ (⋃ j ∈ s, (gridColPath θ j).vertexSet ∩ S) := by
        ext
        simp
      rw [hbi, Finset.sum_cons, ← ih]
      refine Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _)
      rw [Set.disjoint_left]
      intro v hv₁ hv₂
      simp only [Set.mem_iUnion, Set.mem_inter_iff, gridColPath_vertexSet,
        Set.mem_ofPred_eq] at hv₁ hv₂
      obtain ⟨b, hb, hvb, _⟩ := hv₂
      have hab : a = b := hv₁.1.symm.trans hvb
      exact ha (hab.symm ▸ hb)
  have huniv : (⋃ j ∈ (Finset.univ : Finset (Fin θ)), ((gridColPath θ j).vertexSet ∩ S)) = S := by
    ext v
    simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_inter_iff,
      gridColPath_vertexSet, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, _, _, hv⟩ ↦ hv, fun hv ↦ ⟨v.2, trivial, rfl, hv⟩⟩
  rw [← hsum Finset.univ, huniv]

/-- If `X₁ ∪ X₂ ∪ X₃ = E(G)` and `X₁, X₂` are small in `G`, then `X₃` cannot be disjoint from
both `E(P₀)` and `E(P_{θ-1})` (Graph Minors X, Section 7, proof of (7.2), page 172). -/
private theorem theorem_7_2_claim_top_or_bot_meets {θ : ℕ} (hθ : 2 ≤ θ)
    {X₁ X₂ X₃ : Set (Sym2 (Fin θ × Fin θ))}
    (hU : X₁ ∪ X₂ ∪ X₃ = (gridHypergraph θ).edgeSet)
    (hS₁ : IsSmallEdgeSet θ X₁) (hS₂ : IsSmallEdgeSet θ X₂) :
    ((gridRowPath θ ⟨0, by omega⟩).edgeSet ∩ X₃).Nonempty ∨
      ((gridRowPath θ ⟨θ - 1, by omega⟩).edgeSet ∩ X₃).Nonempty := by
  by_contra! hempty
  rcases hempty with ⟨h0, hlast⟩
  have hj_bound : ∀ j : Fin θ,
      2 ≤ ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₁).ncard +
        ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₂).ncard := by
    intro j
    let i_top : Fin θ := ⟨0, by omega⟩
    let i_bot : Fin θ := ⟨θ - 1, by omega⟩
    obtain ⟨e_top, he_topP, hinc_top⟩ := exists_mem_gridRowPath_inc hθ i_top j
    obtain ⟨e_bot, he_botP, hinc_bot⟩ := exists_mem_gridRowPath_inc hθ i_bot j
    have he_topG : e_top ∈ X₁ ∪ X₂ ∪ X₃ := hU.symm ▸ he_topP.1
    have he_botG : e_bot ∈ X₁ ∪ X₂ ∪ X₃ := hU.symm ▸ he_botP.1
    have he_top12 : e_top ∈ X₁ ∨ e_top ∈ X₂ := by
      rcases he_topG with (h1 | h2) | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exact (Set.notMem_empty e_top (h0 ▸ Set.mem_inter he_topP h3)).elim
    have he_bot12 : e_bot ∈ X₁ ∨ e_bot ∈ X₂ := by
      rcases he_botG with (h1 | h2) | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exact (Set.notMem_empty e_bot (hlast ▸ Set.mem_inter he_botP h3)).elim
    have hnotQ₁ := hS₁.not_gridColPath_subset hθ j
    have hnotQ₂ := hS₂.not_gridColPath_subset hθ j
    rcases he_top12 with htop1 | htop2 <;> rcases he_bot12 with hbot1 | hbot2
    · have h2 := two_le_ncard_gridColPath_inter_edgeBoundary hθ j
        ⟨e_top, htop1, hinc_top⟩ ⟨e_bot, hbot1, hinc_bot⟩ hnotQ₁
      omega
    · have hne1 := gridColPath_meets_edgeBoundary j ⟨e_top, htop1, hinc_top⟩ hnotQ₁
      have hne2 := gridColPath_meets_edgeBoundary j ⟨e_bot, hbot2, hinc_bot⟩ hnotQ₂
      have hc1 : 1 ≤ ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₁).ncard :=
        Nat.one_le_iff_ne_zero.2 ((Set.ncard_ne_zero_of_mem hne1.some_mem))
      have hc2 : 1 ≤ ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₂).ncard :=
        Nat.one_le_iff_ne_zero.2 ((Set.ncard_ne_zero_of_mem hne2.some_mem))
      omega
    · have hne2 := gridColPath_meets_edgeBoundary j ⟨e_top, htop2, hinc_top⟩ hnotQ₂
      have hne1 := gridColPath_meets_edgeBoundary j ⟨e_bot, hbot1, hinc_bot⟩ hnotQ₁
      have hc1 : 1 ≤ ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₁).ncard :=
        Nat.one_le_iff_ne_zero.2 ((Set.ncard_ne_zero_of_mem hne1.some_mem))
      have hc2 : 1 ≤ ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₂).ncard :=
        Nat.one_le_iff_ne_zero.2 ((Set.ncard_ne_zero_of_mem hne2.some_mem))
      omega
    · have h2 := two_le_ncard_gridColPath_inter_edgeBoundary hθ j
        ⟨e_top, htop2, hinc_top⟩ ⟨e_bot, hbot2, hinc_bot⟩ hnotQ₂
      omega
  have hsum_ge : ∑ _j : Fin θ, 2 ≤
      ∑ j : Fin θ, (((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₁).ncard +
        ((gridColPath θ j).vertexSet ∩ edgeBoundary (gridHypergraph θ) X₂).ncard) :=
    Finset.sum_le_sum fun j _ ↦ hj_bound j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Finset.sum_add_distrib, ← ncard_eq_sum_gridColPath_inter,
    ← ncard_eq_sum_gridColPath_inter] at hsum_ge
  have h1 := hS₁.1
  have h2 := hS₂.1
  omega

/-- Reversing the row order `(i, j) ↦ (i.rev, j)`. -/
private def revRowVert {θ : ℕ} (v : Fin θ × Fin θ) : Fin θ × Fin θ :=
  (v.1.rev, v.2)

@[simp]
private theorem revRowVert_revRowVert {θ : ℕ} (v : Fin θ × Fin θ) :
    revRowVert (revRowVert v) = v := by
  ext <;> simp [revRowVert]

private theorem revRowVert_injective {θ : ℕ} : Function.Injective (@revRowVert θ) :=
  Function.LeftInverse.injective revRowVert_revRowVert

private def revRowEdge (θ : ℕ) (e : Sym2 (Fin θ × Fin θ)) : Sym2 (Fin θ × Fin θ) :=
  Sym2.map revRowVert e

@[simp]
private theorem revRowEdge_revRowEdge {θ : ℕ} (e : Sym2 (Fin θ × Fin θ)) :
    revRowEdge θ (revRowEdge θ e) = e := by
  induction e using Sym2.ind with | _ x y =>
  simp [revRowEdge]

private theorem pathGraph_adj_rev {θ : ℕ} {i₁ i₂ : Fin θ} :
    (pathGraph θ).Adj i₁.rev i₂.rev ↔ (pathGraph θ).Adj i₁ i₂ := by
  rw [pathGraph_adj, pathGraph_adj, Fin.val_rev, Fin.val_rev]
  have h1 := i₁.isLt
  have h2 := i₂.isLt
  omega

private theorem gridSimpleGraph_adj_revRowVert {θ : ℕ} {u v : Fin θ × Fin θ} :
    (gridSimpleGraph θ).Adj (revRowVert u) (revRowVert v) ↔ (gridSimpleGraph θ).Adj u v := by
  simp [gridSimpleGraph, boxProd_adj, revRowVert, pathGraph_adj_rev]

private theorem revRowEdge_mem_gridHypergraph {θ : ℕ} {e : Sym2 (Fin θ × Fin θ)} :
    revRowEdge θ e ∈ (gridHypergraph θ).edgeSet ↔ e ∈ (gridHypergraph θ).edgeSet := by
  induction e using Sym2.ind with | _ u v =>
  exact gridSimpleGraph_adj_revRowVert

private theorem gridHypergraph_inc_revRowEdge {θ : ℕ} {e : Sym2 (Fin θ × Fin θ)}
    {v : Fin θ × Fin θ} :
    (gridHypergraph θ).Inc (revRowEdge θ e) (revRowVert v) ↔ (gridHypergraph θ).Inc e v := by
  have h1 : (gridHypergraph θ).Inc (revRowEdge θ e) (revRowVert v) ↔
      revRowEdge θ e ∈ (gridSimpleGraph θ).edgeSet ∧ revRowVert v ∈ revRowEdge θ e :=
    gridHypergraph_inc_iff
  have h2 : (gridHypergraph θ).Inc e v ↔
      e ∈ (gridSimpleGraph θ).edgeSet ∧ v ∈ e := gridHypergraph_inc_iff
  rw [h1, h2]
  refine and_congr revRowEdge_mem_gridHypergraph ?_
  induction e using Sym2.ind with | _ x y =>
  simp [revRowEdge, revRowVert_injective.eq_iff]

private theorem revRowEdge_mem_gridRowPath_iff {θ : ℕ} {i : Fin θ} {e : Sym2 (Fin θ × Fin θ)} :
    revRowEdge θ e ∈ (gridRowPath θ i).edgeSet ↔ e ∈ (gridRowPath θ i.rev).edgeSet := by
  simp only [gridRowPath, Set.mem_sep_iff, revRowEdge_mem_gridHypergraph]
  refine and_congr_right fun _ ↦ ⟨fun h v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · have := h (revRowVert v) (gridHypergraph_inc_revRowEdge.2 hv)
    simpa [revRowVert, Fin.rev_eq_iff] using this
  · have hv' : (gridHypergraph θ).Inc e (revRowVert v) :=
      (gridHypergraph_inc_revRowEdge (v := revRowVert v)).1 (by simpa using hv)
    have := h (revRowVert v) hv'
    simpa [revRowVert, Fin.rev_eq_iff] using this

private theorem revRowEdge_mem_gridColPath_iff {θ : ℕ} {j : Fin θ} {e : Sym2 (Fin θ × Fin θ)} :
    revRowEdge θ e ∈ (gridColPath θ j).edgeSet ↔ e ∈ (gridColPath θ j).edgeSet := by
  simp only [gridColPath, Set.mem_sep_iff, revRowEdge_mem_gridHypergraph]
  refine and_congr_right fun _ ↦ ⟨fun h v hv ↦ ?_, fun h v hv ↦ ?_⟩
  · simpa [revRowVert] using h (revRowVert v) (gridHypergraph_inc_revRowEdge.2 hv)
  · have hv' : (gridHypergraph θ).Inc e (revRowVert v) :=
      (gridHypergraph_inc_revRowEdge (v := revRowVert v)).1 (by simpa using hv)
    simpa [revRowVert] using h (revRowVert v) hv'

private theorem mem_edgeBoundary_preimage_revRowEdge {θ : ℕ} {X : Set (Sym2 (Fin θ × Fin θ))}
    {v : Fin θ × Fin θ} :
    v ∈ edgeBoundary (gridHypergraph θ) (revRowEdge θ ⁻¹' X) ↔
      revRowVert v ∈ edgeBoundary (gridHypergraph θ) X := by
  rw [mem_edgeBoundary_gridHypergraph_iff, mem_edgeBoundary_gridHypergraph_iff]
  constructor
  · rintro ⟨⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂X⟩, hinc₂⟩⟩
    exact ⟨⟨revRowEdge θ e₁, he₁, gridHypergraph_inc_revRowEdge.2 hinc₁⟩,
      ⟨revRowEdge θ e₂, ⟨revRowEdge_mem_gridHypergraph.2 he₂G, he₂X⟩,
        gridHypergraph_inc_revRowEdge.2 hinc₂⟩⟩
  · rintro ⟨⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂X⟩, hinc₂⟩⟩
    refine ⟨⟨revRowEdge θ e₁, by simpa using he₁, ?_⟩,
      ⟨revRowEdge θ e₂, ⟨revRowEdge_mem_gridHypergraph.2 he₂G, by simpa using he₂X⟩, ?_⟩⟩
    · have := gridHypergraph_inc_revRowEdge.2 hinc₁
      simpa using this
    · have := gridHypergraph_inc_revRowEdge.2 hinc₂
      simpa using this

private theorem ncard_edgeBoundary_preimage_revRowEdge {θ : ℕ} (X : Set (Sym2 (Fin θ × Fin θ))) :
    (edgeBoundary (gridHypergraph θ) (revRowEdge θ ⁻¹' X)).ncard =
      (edgeBoundary (gridHypergraph θ) X).ncard := by
  refine Set.ncard_congr (fun v _ ↦ revRowVert v)
    (fun v hv ↦ mem_edgeBoundary_preimage_revRowEdge.1 hv)
    (fun _ _ _ _ h ↦ revRowVert_injective h)
    (fun w hw ↦ ⟨revRowVert w, ?_, revRowVert_revRowVert w⟩)
  rw [mem_edgeBoundary_preimage_revRowEdge, revRowVert_revRowVert]
  exact hw

private theorem isSmallEdgeSet_preimage_revRowEdge {θ : ℕ} {X : Set (Sym2 (Fin θ × Fin θ))}
    (hX : IsSmallEdgeSet θ X) :
    IsSmallEdgeSet θ (revRowEdge θ ⁻¹' X) := by
  refine ⟨by rw [ncard_edgeBoundary_preimage_revRowEdge]; exact hX.1, fun i hsub ↦ ?_⟩
  apply hX.2 i.rev
  intro e he
  have hm : revRowEdge θ e ∈ revRowEdge θ ⁻¹' X := hsub (revRowEdge_mem_gridRowPath_iff.2 he)
  simpa using hm

/-! ## Restriction from `(m + 1)`-grid to `m`-grid in (7.2) -/

/-- Embedding vertices of the `m`-grid into the top-left `m × m` subgrid of the `(m + 1)`-grid. -/
private def embVert {m : ℕ} (v : Fin m × Fin m) : Fin (m + 1) × Fin (m + 1) :=
  (v.1.castSucc, v.2.castSucc)

private theorem embVert_injective {m : ℕ} : Function.Injective (@embVert m) := by
  intro u v h
  exact Prod.ext (Fin.castSucc_inj.1 (congrArg Prod.fst h))
    (Fin.castSucc_inj.1 (congrArg Prod.snd h))

private def embEdge (m : ℕ) (e : Sym2 (Fin m × Fin m)) : Sym2 (Fin (m + 1) × Fin (m + 1)) :=
  Sym2.map embVert e

private theorem gridSimpleGraph_adj_embVert {m : ℕ} {u v : Fin m × Fin m} :
    (gridSimpleGraph (m + 1)).Adj (embVert u) (embVert v) ↔ (gridSimpleGraph m).Adj u v := by
  simp [gridSimpleGraph, boxProd_adj, embVert, pathGraph_adj, Fin.castSucc_inj]

private theorem embEdge_mem_gridHypergraph {m : ℕ} {e : Sym2 (Fin m × Fin m)} :
    embEdge m e ∈ (gridHypergraph (m + 1)).edgeSet ↔ e ∈ (gridHypergraph m).edgeSet := by
  induction e using Sym2.ind with | _ u v =>
  exact gridSimpleGraph_adj_embVert

private theorem gridHypergraph_inc_embEdge {m : ℕ} {e : Sym2 (Fin m × Fin m)}
    {v : Fin m × Fin m} :
    (gridHypergraph (m + 1)).Inc (embEdge m e) (embVert v) ↔ (gridHypergraph m).Inc e v := by
  have h1 : (gridHypergraph (m + 1)).Inc (embEdge m e) (embVert v) ↔
      embEdge m e ∈ (gridSimpleGraph (m + 1)).edgeSet ∧ embVert v ∈ embEdge m e :=
    gridHypergraph_inc_iff
  have h2 : (gridHypergraph m).Inc e v ↔
      e ∈ (gridSimpleGraph m).edgeSet ∧ v ∈ e := gridHypergraph_inc_iff
  rw [h1, h2]
  refine and_congr embEdge_mem_gridHypergraph ?_
  induction e using Sym2.ind with | _ x y =>
  simp [embEdge, embVert_injective.eq_iff]

private theorem embEdge_rowEdge {m : ℕ} (i : Fin m) (a : ℕ) (ha : a + 1 < m) :
    embEdge m (rowEdge i a ha) = rowEdge i.castSucc a (Nat.lt_succ_of_lt ha) := rfl

private theorem embEdge_colEdge {m : ℕ} (j : Fin m) (a : ℕ) (ha : a + 1 < m) :
    embEdge m (colEdge j a ha) = colEdge j.castSucc a (Nat.lt_succ_of_lt ha) := rfl

/-- The pullback `X' = X ∩ E(G')` of an edge set `X` of the `(m + 1)`-grid to the `m`-grid. -/
private def restrictEdgeSet (m : ℕ) (X : Set (Sym2 (Fin (m + 1) × Fin (m + 1)))) :
    Set (Sym2 (Fin m × Fin m)) :=
  {e ∈ (gridHypergraph m).edgeSet | embEdge m e ∈ X}

private theorem embVert_mem_edgeBoundary_of_mem_restrictEdgeSet {m : ℕ}
    {X : Set (Sym2 (Fin (m + 1) × Fin (m + 1)))} {v : Fin m × Fin m}
    (hv : v ∈ edgeBoundary (gridHypergraph m) (restrictEdgeSet m X)) :
    embVert v ∈ edgeBoundary (gridHypergraph (m + 1)) X := by
  rw [mem_edgeBoundary_gridHypergraph_iff] at hv ⊢
  rcases hv with ⟨⟨e₁, he₁, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂X⟩, hinc₂⟩⟩
  refine ⟨⟨embEdge m e₁, he₁.2, gridHypergraph_inc_embEdge.2 hinc₁⟩,
    ⟨embEdge m e₂, ⟨embEdge_mem_gridHypergraph.2 he₂G, fun h ↦ he₂X ⟨he₂G, h⟩⟩,
      gridHypergraph_inc_embEdge.2 hinc₂⟩⟩

/-- If `V(P_m ∪ Q_m)` meets `∂(X)`, then `|∂'(X')| < |∂(X)|`
(Graph Minors X, Section 7, proof of (7.2), page 172). -/
private theorem ncard_edgeBoundary_restrictEdgeSet_lt {m : ℕ}
    {X : Set (Sym2 (Fin (m + 1) × Fin (m + 1)))}
    (hmeet : (((gridRowPath (m + 1) (Fin.last m)).vertexSet ∪
        (gridColPath (m + 1) (Fin.last m)).vertexSet) ∩
        edgeBoundary (gridHypergraph (m + 1)) X).Nonempty) :
    (edgeBoundary (gridHypergraph m) (restrictEdgeSet m X)).ncard <
      (edgeBoundary (gridHypergraph (m + 1)) X).ncard := by
  obtain ⟨w, hwPQ, hwB⟩ := hmeet
  have himg_sub : embVert '' edgeBoundary (gridHypergraph m) (restrictEdgeSet m X) ⊆
      edgeBoundary (gridHypergraph (m + 1)) X \ {w} := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨embVert_mem_edgeBoundary_of_mem_restrictEdgeSet hv, ?_⟩
    rw [Set.mem_singleton_iff]
    rintro rfl
    rcases hwPQ with hrow | hcol
    · exact Fin.castSucc_ne_last v.1 hrow
    · exact Fin.castSucc_ne_last v.2 hcol
  have hcard_img : (embVert '' edgeBoundary (gridHypergraph m) (restrictEdgeSet m X)).ncard =
      (edgeBoundary (gridHypergraph m) (restrictEdgeSet m X)).ncard :=
    Set.ncard_image_of_injective _ embVert_injective
  have hle : (edgeBoundary (gridHypergraph m) (restrictEdgeSet m X)).ncard ≤
      (edgeBoundary (gridHypergraph (m + 1)) X \ {w}).ncard := by
    rw [← hcard_img]
    exact Set.ncard_le_ncard himg_sub (Set.toFinite _)
  have hlt : (edgeBoundary (gridHypergraph (m + 1)) X \ {w}).ncard <
      (edgeBoundary (gridHypergraph (m + 1)) X).ncard :=
    Set.ncard_lt_ncard (Set.sdiff_singleton_ssubset.2 hwB) (Set.toFinite _)
  exact hle.trans_lt hlt

/-- Core step of the induction in (7.2) once `E(Q_m)` meets `X₁` and `X₂` and `E(P_m)` meets `X₃`.
-/
private theorem theorem_7_2_step_core {m : ℕ} (hm : 2 ≤ m)
    (ih : ∀ ⦃Y₁ Y₂ Y₃ : Set (Sym2 (Fin m × Fin m))⦄,
      Y₁ ∪ Y₂ ∪ Y₃ = (gridHypergraph m).edgeSet →
      ¬ (IsSmallEdgeSet m Y₁ ∧ IsSmallEdgeSet m Y₂ ∧ IsSmallEdgeSet m Y₃))
    {X₁ X₂ X₃ : Set (Sym2 (Fin (m + 1) × Fin (m + 1)))}
    (hU : X₁ ∪ X₂ ∪ X₃ = (gridHypergraph (m + 1)).edgeSet)
    (hS₁ : IsSmallEdgeSet (m + 1) X₁)
    (hS₂ : IsSmallEdgeSet (m + 1) X₂)
    (hS₃ : IsSmallEdgeSet (m + 1) X₃)
    (hQ₁ : ((gridColPath (m + 1) (Fin.last m)).edgeSet ∩ X₁).Nonempty)
    (hQ₂ : ((gridColPath (m + 1) (Fin.last m)).edgeSet ∩ X₂).Nonempty)
    (hP₃ : ((gridRowPath (m + 1) (Fin.last m)).edgeSet ∩ X₃).Nonempty) :
    False := by
  have hm1 : 2 ≤ m + 1 := by omega
  have hmeet₁ : (((gridRowPath (m + 1) (Fin.last m)).vertexSet ∪
      (gridColPath (m + 1) (Fin.last m)).vertexSet) ∩
      edgeBoundary (gridHypergraph (m + 1)) X₁).Nonempty := by
    obtain ⟨e, heQ, heX₁⟩ := hQ₁
    obtain ⟨a, ha, rfl⟩ := mem_gridColPath_edgeSet_iff.1 heQ
    obtain ⟨v, hvQ, hvB⟩ := gridColPath_meets_edgeBoundary (Fin.last m)
      ⟨colEdge (Fin.last m) a ha, heX₁, colEdge_inc_left (Fin.last m) a ha⟩
      (hS₁.not_gridColPath_subset hm1 (Fin.last m))
    exact ⟨v, Or.inr hvQ, hvB⟩
  have hmeet₂ : (((gridRowPath (m + 1) (Fin.last m)).vertexSet ∪
      (gridColPath (m + 1) (Fin.last m)).vertexSet) ∩
      edgeBoundary (gridHypergraph (m + 1)) X₂).Nonempty := by
    obtain ⟨e, heQ, heX₂⟩ := hQ₂
    obtain ⟨a, ha, rfl⟩ := mem_gridColPath_edgeSet_iff.1 heQ
    obtain ⟨v, hvQ, hvB⟩ := gridColPath_meets_edgeBoundary (Fin.last m)
      ⟨colEdge (Fin.last m) a ha, heX₂, colEdge_inc_left (Fin.last m) a ha⟩
      (hS₂.not_gridColPath_subset hm1 (Fin.last m))
    exact ⟨v, Or.inr hvQ, hvB⟩
  have hmeet₃ : (((gridRowPath (m + 1) (Fin.last m)).vertexSet ∪
      (gridColPath (m + 1) (Fin.last m)).vertexSet) ∩
      edgeBoundary (gridHypergraph (m + 1)) X₃).Nonempty := by
    obtain ⟨e, heP, heX₃⟩ := hP₃
    obtain ⟨a, ha, rfl⟩ := mem_gridRowPath_edgeSet_iff.1 heP
    obtain ⟨v, hvP, hvB⟩ := gridRowPath_meets_edgeBoundary (Fin.last m)
      ⟨rowEdge (Fin.last m) a ha, heX₃, rowEdge_inc_left (Fin.last m) a ha⟩
      (hS₃.2 (Fin.last m))
    exact ⟨v, Or.inl hvP, hvB⟩
  let X'₁ := restrictEdgeSet m X₁
  let X'₂ := restrictEdgeSet m X₂
  let X'₃ := restrictEdgeSet m X₃
  have hU' : X'₁ ∪ X'₂ ∪ X'₃ = (gridHypergraph m).edgeSet := by
    ext e
    simp only [X'₁, X'₂, X'₃, restrictEdgeSet, Set.mem_union, Set.mem_sep_iff]
    constructor
    · rintro ((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he
    · intro he
      have he' : embEdge m e ∈ X₁ ∪ X₂ ∪ X₃ :=
        hU.symm ▸ embEdge_mem_gridHypergraph.2 he
      rcases he' with (h1 | h2) | h3
      · exact Or.inl (Or.inl ⟨he, h1⟩)
      · exact Or.inl (Or.inr ⟨he, h2⟩)
      · exact Or.inr ⟨he, h3⟩
  have hB'₁ : (edgeBoundary (gridHypergraph m) X'₁).ncard < m := by
    have hlt := ncard_edgeBoundary_restrictEdgeSet_lt hmeet₁
    have h1 := hS₁.1
    dsimp [X'₁]
    omega
  have hB'₂ : (edgeBoundary (gridHypergraph m) X'₂).ncard < m := by
    have hlt := ncard_edgeBoundary_restrictEdgeSet_lt hmeet₂
    have h2 := hS₂.1
    dsimp [X'₂]
    omega
  have hB'₃ : (edgeBoundary (gridHypergraph m) X'₃).ncard < m := by
    have hlt := ncard_edgeBoundary_restrictEdgeSet_lt hmeet₃
    have h3 := hS₃.1
    dsimp [X'₃]
    omega
  have hnot_all := ih hU'
  have hrow_or : (∃ i' : Fin m, (gridRowPath m i').edgeSet ⊆ X'₁) ∨
      (∃ i' : Fin m, (gridRowPath m i').edgeSet ⊆ X'₂) ∨
      (∃ i' : Fin m, (gridRowPath m i').edgeSet ⊆ X'₃) := by
    by_contra! hno
    exact hnot_all ⟨⟨hB'₁, hno.1⟩, ⟨hB'₂, hno.2.1⟩, ⟨hB'₃, hno.2.2⟩⟩
  have col_contra : ∀ {X : Set (Sym2 (Fin (m + 1) × Fin (m + 1)))},
      IsSmallEdgeSet (m + 1) X →
      ((gridColPath (m + 1) (Fin.last m)).edgeSet ∩ X).Nonempty →
      (∃ i' : Fin m, (gridRowPath m i').edgeSet ⊆ restrictEdgeSet m X) → False := by
    intro X hSX hQX ⟨i', hi'⟩
    have hmeet_all : ∀ j : Fin (m + 1),
        ((gridColPath (m + 1) j).vertexSet ∩ edgeBoundary (gridHypergraph (m + 1)) X).Nonempty := by
      intro j
      induction j using Fin.lastCases with
      | last =>
        obtain ⟨e, heQ, heX⟩ := hQX
        obtain ⟨a, ha, rfl⟩ := mem_gridColPath_edgeSet_iff.1 heQ
        exact gridColPath_meets_edgeBoundary (Fin.last m)
          ⟨colEdge (Fin.last m) a ha, heX, colEdge_inc_left (Fin.last m) a ha⟩
          (hSX.not_gridColPath_subset hm1 (Fin.last m))
      | cast j₀ =>
        obtain ⟨e₀, he₀P, hinc₀⟩ := exists_mem_gridRowPath_inc hm i' j₀
        have he₀X : embEdge m e₀ ∈ X := (hi' he₀P).2
        have hinc : (gridHypergraph (m + 1)).Inc (embEdge m e₀) (i'.castSucc, j₀.castSucc) :=
          gridHypergraph_inc_embEdge.2 hinc₀
        exact gridColPath_meets_edgeBoundary j₀.castSucc ⟨embEdge m e₀, he₀X, hinc⟩
          (hSX.not_gridColPath_subset hm1 j₀.castSucc)
    have hsum : ∑ _j : Fin (m + 1), 1 ≤
        ∑ j : Fin (m + 1),
          ((gridColPath (m + 1) j).vertexSet ∩ edgeBoundary (gridHypergraph (m + 1)) X).ncard := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      exact Nat.one_le_iff_ne_zero.2 (Set.ncard_ne_zero_of_mem (hmeet_all j).some_mem)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one,
      ← ncard_eq_sum_gridColPath_inter] at hsum
    have := hSX.1
    omega
  rcases hrow_or with h1 | h2 | h3
  · exact col_contra hS₁ hQ₁ h1
  · exact col_contra hS₂ hQ₂ h2
  · obtain ⟨j', hj'⟩ := (theorem_7_1_proof hm (X := X'₃) (fun _ h ↦ h.1) hB'₃).1 h3
    have hmeet_rows : ∀ i : Fin (m + 1),
        ((gridRowPath (m + 1) i).vertexSet ∩ edgeBoundary (gridHypergraph (m + 1)) X₃).Nonempty
          := by
      intro i
      induction i using Fin.lastCases with
      | last =>
        obtain ⟨e, heP, heX₃⟩ := hP₃
        obtain ⟨a, ha, rfl⟩ := mem_gridRowPath_edgeSet_iff.1 heP
        exact gridRowPath_meets_edgeBoundary (Fin.last m)
          ⟨rowEdge (Fin.last m) a ha, heX₃, rowEdge_inc_left (Fin.last m) a ha⟩
          (hS₃.2 (Fin.last m))
      | cast i₀ =>
        obtain ⟨e₀, he₀Q, hinc₀⟩ := exists_mem_gridColPath_inc hm i₀ j'
        have he₀X₃ : embEdge m e₀ ∈ X₃ := (hj' he₀Q).2
        have hinc : (gridHypergraph (m + 1)).Inc (embEdge m e₀) (i₀.castSucc, j'.castSucc) :=
          gridHypergraph_inc_embEdge.2 hinc₀
        exact gridRowPath_meets_edgeBoundary i₀.castSucc ⟨embEdge m e₀, he₀X₃, hinc⟩
          (hS₃.2 i₀.castSucc)
    choose f hf using hmeet_rows
    have hinj : Function.Injective f := by
      intro i₁ i₂ heq
      have h₁ : (f i₁).1 = i₁ := (hf i₁).1
      have h₂ : (f i₂).1 = i₂ := (hf i₂).1
      rw [← h₁, ← h₂, heq]
    have hsub : Set.range f ⊆ edgeBoundary (gridHypergraph (m + 1)) X₃ := by
      rintro _ ⟨i, rfl⟩
      exact (hf i).2
    have hcard_range : (Set.range f).ncard = m + 1 := by
      rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hle : (Set.range f).ncard ≤ (edgeBoundary (gridHypergraph (m + 1)) X₃).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have := hS₃.1
    omega

/-- Step of (7.2) once `E(Q_m)` meets `X₁` and `X₂` (handling the two cases for whether `E(P_0)` or
`E(P_m)` meets `X₃` via row reversal). -/
private theorem theorem_7_2_step_wlog {m : ℕ} (hm : 2 ≤ m)
    (ih : ∀ ⦃Y₁ Y₂ Y₃ : Set (Sym2 (Fin m × Fin m))⦄,
      Y₁ ∪ Y₂ ∪ Y₃ = (gridHypergraph m).edgeSet →
      ¬ (IsSmallEdgeSet m Y₁ ∧ IsSmallEdgeSet m Y₂ ∧ IsSmallEdgeSet m Y₃))
    {X₁ X₂ X₃ : Set (Sym2 (Fin (m + 1) × Fin (m + 1)))}
    (hU : X₁ ∪ X₂ ∪ X₃ = (gridHypergraph (m + 1)).edgeSet)
    (hS₁ : IsSmallEdgeSet (m + 1) X₁)
    (hS₂ : IsSmallEdgeSet (m + 1) X₂)
    (hS₃ : IsSmallEdgeSet (m + 1) X₃)
    (hQ₁ : ((gridColPath (m + 1) (Fin.last m)).edgeSet ∩ X₁).Nonempty)
    (hQ₂ : ((gridColPath (m + 1) (Fin.last m)).edgeSet ∩ X₂).Nonempty) :
    False := by
  have hm1 : 2 ≤ m + 1 := by omega
  rcases theorem_7_2_claim_top_or_bot_meets hm1 hU hS₁ hS₂ with hP₀ | hP_last
  · let R₁ := revRowEdge (m + 1) ⁻¹' X₁
    let R₂ := revRowEdge (m + 1) ⁻¹' X₂
    let R₃ := revRowEdge (m + 1) ⁻¹' X₃
    have hUR : R₁ ∪ R₂ ∪ R₃ = (gridHypergraph (m + 1)).edgeSet := by
      ext e
      simp only [R₁, R₂, R₃, Set.mem_union, Set.mem_preimage]
      have : revRowEdge (m + 1) e ∈ X₁ ∪ X₂ ∪ X₃ ↔
          revRowEdge (m + 1) e ∈ (gridHypergraph (m + 1)).edgeSet := by rw [hU]
      exact this.trans revRowEdge_mem_gridHypergraph
    have hRQ₁ : ((gridColPath (m + 1) (Fin.last m)).edgeSet ∩ R₁).Nonempty := by
      obtain ⟨e, heQ, heX₁⟩ := hQ₁
      exact ⟨revRowEdge (m + 1) e, revRowEdge_mem_gridColPath_iff.2 heQ, by simpa [R₁] using heX₁⟩
    have hRQ₂ : ((gridColPath (m + 1) (Fin.last m)).edgeSet ∩ R₂).Nonempty := by
      obtain ⟨e, heQ, heX₂⟩ := hQ₂
      exact ⟨revRowEdge (m + 1) e, revRowEdge_mem_gridColPath_iff.2 heQ, by simpa [R₂] using heX₂⟩
    have hRP₃ : ((gridRowPath (m + 1) (Fin.last m)).edgeSet ∩ R₃).Nonempty := by
      obtain ⟨e, heP, heX₃⟩ := hP₀
      refine ⟨revRowEdge (m + 1) e, ?_, by simpa [R₃] using heX₃⟩
      rw [revRowEdge_mem_gridRowPath_iff]
      have hrev_last : (Fin.last m).rev = ⟨0, by omega⟩ := Fin.rev_last m
      rwa [hrev_last]
    exact theorem_7_2_step_core hm ih hUR
      (isSmallEdgeSet_preimage_revRowEdge hS₁)
      (isSmallEdgeSet_preimage_revRowEdge hS₂)
      (isSmallEdgeSet_preimage_revRowEdge hS₃)
      hRQ₁ hRQ₂ hRP₃
  · exact theorem_7_2_step_core hm ih hU hS₁ hS₂ hS₃ hQ₁ hQ₂ hP_last

/-- **Graph Minors X, (7.2)** (Kleitman–Saks lemma, page 172):
"If $G$ is a $\theta$-grid and $X_1, X_2, X_3 \subseteq E(G)$ with $X_1 \cup X_2 \cup X_3 =
E(G)$, then not all of $X_1, X_2, X_3$ are small in $G$." -/
theorem theorem_7_2_proof {θ : ℕ} (hθ : 2 ≤ θ)
    {X₁ X₂ X₃ : Set (Sym2 (Fin θ × Fin θ))}
    (hU : X₁ ∪ X₂ ∪ X₃ = (gridHypergraph θ).edgeSet) :
    ¬ (IsSmallEdgeSet θ X₁ ∧ IsSmallEdgeSet θ X₂ ∧ IsSmallEdgeSet θ X₃) := by
  induction θ, hθ using Nat.le_induction with
  | base =>
    rintro ⟨hS₁, hS₂, hS₃⟩
    let i₀ : Fin 2 := ⟨0, by decide⟩
    have ha₀ : 0 + 1 < 2 := by decide
    let e₀ := rowEdge i₀ 0 ha₀
    have he₀G : e₀ ∈ X₁ ∪ X₂ ∪ X₃ := hU.symm ▸ rowEdge_mem_gridHypergraph i₀ 0 ha₀
    have hrow_sub : ∀ {X : Set (Sym2 (Fin 2 × Fin 2))}, e₀ ∈ X →
        (gridRowPath 2 i₀).edgeSet ⊆ X := by
      intro X heX e he
      obtain ⟨a, ha, rfl⟩ := mem_gridRowPath_edgeSet_iff.1 he
      have ha_zero : a = 0 := by omega
      subst ha_zero
      exact heX
    rcases he₀G with (h1 | h2) | h3
    · exact hS₁.2 i₀ (hrow_sub h1)
    · exact hS₂.2 i₀ (hrow_sub h2)
    · exact hS₃.2 i₀ (hrow_sub h3)
  | succ m hm ih =>
    rintro ⟨hS₁, hS₂, hS₃⟩
    have hm1 : 2 ≤ m + 1 := by omega
    let j_last : Fin (m + 1) := Fin.last m
    have ha₀ : 0 + 1 < m + 1 := by omega
    let e₀ := colEdge j_last 0 ha₀
    have he₀Q : e₀ ∈ (gridColPath (m + 1) j_last).edgeSet :=
      colEdge_mem_gridColPath j_last 0 ha₀
    have he₀U : e₀ ∈ X₁ ∪ X₂ ∪ X₃ := hU.symm ▸ he₀Q.1
    have hnotQ₁ := hS₁.not_gridColPath_subset hm1 j_last
    have hnotQ₂ := hS₂.not_gridColPath_subset hm1 j_last
    have hnotQ₃ := hS₃.not_gridColPath_subset hm1 j_last
    have hU132 : X₁ ∪ X₃ ∪ X₂ = (gridHypergraph (m + 1)).edgeSet := by
      rw [← hU]; ext; simp [or_right_comm]
    have hU231 : X₂ ∪ X₃ ∪ X₁ = (gridHypergraph (m + 1)).edgeSet := by
      rw [← hU]; ext; simp; tauto
    rcases he₀U with (he1 | he2) | he3
    · obtain ⟨f, hfQ, hf_not1⟩ := Set.not_subset.1 hnotQ₁
      have hfU : f ∈ X₁ ∪ X₂ ∪ X₃ := hU.symm ▸ hfQ.1
      rcases hfU with (hf1 | hf2) | hf3
      · exact hf_not1 hf1
      · exact theorem_7_2_step_wlog hm (@ih) hU hS₁ hS₂ hS₃
          ⟨e₀, he₀Q, he1⟩ ⟨f, hfQ, hf2⟩
      · exact theorem_7_2_step_wlog hm (@ih) hU132 hS₁ hS₃ hS₂
          ⟨e₀, he₀Q, he1⟩ ⟨f, hfQ, hf3⟩
    · obtain ⟨f, hfQ, hf_not2⟩ := Set.not_subset.1 hnotQ₂
      have hfU : f ∈ X₁ ∪ X₂ ∪ X₃ := hU.symm ▸ hfQ.1
      rcases hfU with (hf1 | hf2) | hf3
      · exact theorem_7_2_step_wlog hm (@ih) hU hS₁ hS₂ hS₃
          ⟨f, hfQ, hf1⟩ ⟨e₀, he₀Q, he2⟩
      · exact hf_not2 hf2
      · exact theorem_7_2_step_wlog hm (@ih) hU231 hS₂ hS₃ hS₁
          ⟨e₀, he₀Q, he2⟩ ⟨f, hfQ, hf3⟩
    · obtain ⟨f, hfQ, hf_not3⟩ := Set.not_subset.1 hnotQ₃
      have hfU : f ∈ X₁ ∪ X₂ ∪ X₃ := hU.symm ▸ hfQ.1
      rcases hfU with (hf1 | hf2) | hf3
      · exact theorem_7_2_step_wlog hm (@ih) hU132 hS₁ hS₃ hS₂
          ⟨f, hfQ, hf1⟩ ⟨e₀, he₀Q, he3⟩
      · exact theorem_7_2_step_wlog hm (@ih) hU231 hS₂ hS₃ hS₁
          ⟨f, hfQ, hf2⟩ ⟨e₀, he₀Q, he3⟩
      · exact hf_not3 hf3

/-! ## Proof of (7.3) -/

/-- For any separation `(A, B)` of `G`, `∂(E(A)) ⊆ V(A ∩ B)`. -/
private theorem edgeBoundary_edgeSet_subset_inter {α β : Type*} {G A B : Hypergraph α β}
    (hsep : G.IsSeparation A B) :
    edgeBoundary G A.edgeSet ⊆ (A ∩ B).vertexSet := by
  rintro v ⟨_, ⟨e₁, he₁A, hinc₁⟩, ⟨e₂, ⟨he₂G, he₂notA⟩, hinc₂⟩⟩
  have hvA : v ∈ A.vertexSet :=
    A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le he₁A).2 hinc₁)
  have he₂B : e₂ ∈ B.edgeSet :=
    (hsep.edgeSet_union.symm ▸ he₂G).resolve_left he₂notA
  have hvB : v ∈ B.vertexSet :=
    B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le he₂B).2 hinc₂)
  exact ⟨hvA, hvB⟩

/-- If `(A, B)` is a separation of the `θ`-grid and `V(Qⱼ)` meets both `V(A)` and `V(B)`, then
`V(Qⱼ)` meets `V(A ∩ B)` (Graph Minors X, Section 7, proof of (7.3), page 173). -/
private theorem gridColPath_inter_separation_nonempty {θ : ℕ}
    {A B : Hypergraph (Fin θ × Fin θ) (Sym2 (Fin θ × Fin θ))}
    (hsep : (gridHypergraph θ).IsSeparation A B) (j : Fin θ)
    {h i : Fin θ} (hh : (h, j) ∈ A.vertexSet) (hi : (i, j) ∈ B.vertexSet) :
    ((gridColPath θ j).vertexSet ∩ (A ∩ B).vertexSet).Nonempty := by
  by_contra! hemp
  have hwalk : ∀ {u v : Fin θ}, (pathGraph θ).Reachable u v →
      (u, j) ∈ A.vertexSet → (v, j) ∈ A.vertexSet := by
    intro u v hreach huA
    obtain ⟨w⟩ := hreach
    induction w with
    | nil => exact huA
    | @cons x y z hadj w' ih =>
      apply ih
      have hadjG : (gridSimpleGraph θ).Adj (x, j) (y, j) := by
        rw [boxProd_adj]
        exact Or.inl ⟨hadj, rfl⟩
      have heG : s((x, j), (y, j)) ∈ A.edgeSet ∪ B.edgeSet :=
        hsep.edgeSet_union.symm ▸ hadjG
      have hinc_x : (gridHypergraph θ).Inc s((x, j), (y, j)) (x, j) :=
        gridHypergraph_inc_sym2.2 ⟨hadjG, Or.inl rfl⟩
      have hinc_y : (gridHypergraph θ).Inc s((x, j), (y, j)) (y, j) :=
        gridHypergraph_inc_sym2.2 ⟨hadjG, Or.inr rfl⟩
      rcases heG with heA | heB
      · exact A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).2 hinc_y)
      · have hxB : (x, j) ∈ B.vertexSet :=
          B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).2 hinc_x)
        have hmem : (x, j) ∈ (gridColPath θ j).vertexSet ∩ (A ∩ B).vertexSet :=
          ⟨rfl, huA, hxB⟩
        exact (Set.notMem_empty (x, j) (hemp ▸ hmem)).elim
  have hiA : (i, j) ∈ A.vertexSet := hwalk (preconnected_pathGraph θ h i) hh
  have hmem : (i, j) ∈ (gridColPath θ j).vertexSet ∩ (A ∩ B).vertexSet :=
    ⟨rfl, hiA, hi⟩
  exact Set.notMem_empty (i, j) (hemp ▸ hmem)

/-- **Graph Minors X, (7.3)** (page 173):
"Given a $\theta$-grid $G$ with $P_1, \dots, P_\theta, Q_1, \dots, Q_\theta$ as before, let
$\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $<\theta$ such that $E(A)$ is
small.
(7.3) *$\mathscr{T}$ is a tangle in $G$ of order $\theta$.*" -/
theorem theorem_7_3_proof {θ : ℕ} (hθ : 2 ≤ θ) :
    IsTangle (gridHypergraph θ) θ (gridTangle θ) where
  one_le := by omega
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A B hsep hord := by
    have hBA : (edgeBoundary (gridHypergraph θ) A.edgeSet).ncard < θ :=
      (Set.ncard_le_ncard (edgeBoundary_edgeSet_subset_inter hsep)
        (A ∩ B).vertexSet_finite).trans_lt hord
    have hBB : (edgeBoundary (gridHypergraph θ) B.edgeSet).ncard < θ := by
      have hord' : separationOrder B A < θ := by rwa [separationOrder_comm]
      exact (Set.ncard_le_ncard (edgeBoundary_edgeSet_subset_inter hsep.symm)
        (B ∩ A).vertexSet_finite).trans_lt hord'
    by_cases hsmallA : IsSmallEdgeSet θ A.edgeSet
    · exact Or.inl ⟨hsep, hord, hsmallA⟩
    · right
      refine ⟨hsep.symm, by rwa [separationOrder_comm], ⟨hBB, ?_⟩⟩
      intro i hiB
      have hhA_ex : ∃ h : Fin θ, (gridRowPath θ h).edgeSet ⊆ A.edgeSet := by
        by_contra! hno
        exact hsmallA ⟨hBA, hno⟩
      obtain ⟨h, hhA⟩ := hhA_ex
      have hmeet : ∀ j : Fin θ,
          ((gridColPath θ j).vertexSet ∩ (A ∩ B).vertexSet).Nonempty := by
        intro j
        obtain ⟨e₁, he₁P, hinc₁⟩ := exists_mem_gridRowPath_inc hθ h j
        obtain ⟨e₂, he₂P, hinc₂⟩ := exists_mem_gridRowPath_inc hθ i j
        have hh_mem : (h, j) ∈ A.vertexSet :=
          A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le (hhA he₁P)).2 hinc₁)
        have hi_mem : (i, j) ∈ B.vertexSet :=
          B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le (hiB he₂P)).2 hinc₂)
        exact gridColPath_inter_separation_nonempty hsep j hh_mem hi_mem
      have hsum : ∑ _j : Fin θ, 1 ≤
          ∑ j : Fin θ, ((gridColPath θ j).vertexSet ∩ (A ∩ B).vertexSet).ncard := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        exact Nat.one_le_iff_ne_zero.2 (Set.ncard_ne_zero_of_mem (hmeet j).some_mem)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one,
        ← ncard_eq_sum_gridColPath_inter] at hsum
      rw [separationOrder] at hord
      omega
  axiom2 A₁ B₁ A₂ B₂ A₃ B₃ h₁ h₂ h₃ hU := by
    have hEU : A₁.edgeSet ∪ A₂.edgeSet ∪ A₃.edgeSet = (gridHypergraph θ).edgeSet :=
      congrArg Hypergraph.edgeSet hU
    exact theorem_7_2_proof hθ hEU ⟨h₁.2.2, h₂.2.2, h₃.2.2⟩
  axiom3 A B h hVA := by
    rcases h with ⟨hsep, hord, hsmallA⟩
    dsimp only at hsep hord hsmallA
    have hVB_eq : (A ∩ B).vertexSet = B.vertexSet := by
      rw [inter_vertexSet, hVA, Set.inter_eq_right.2 hsep.right_le.vertexSet_subset]
    have hB_card : B.vertexSet.ncard < θ := by
      rwa [separationOrder, hVB_eq] at hord
    have hex_row : ∃ i : Fin θ, Disjoint (gridRowPath θ i).vertexSet B.vertexSet := by
      by_contra hno_disj
      have hmeet : ∀ i : Fin θ, ∃ v, v ∈ (gridRowPath θ i).vertexSet ∧ v ∈ B.vertexSet := by
        intro i
        by_contra! h
        exact hno_disj ⟨i, Set.disjoint_left.2 h⟩
      choose f hf using hmeet
      have hinj : Function.Injective f := by
        intro i₁ i₂ heq
        have h₁ : (f i₁).1 = i₁ := (hf i₁).1
        have h₂ : (f i₂).1 = i₂ := (hf i₂).1
        rw [← h₁, ← h₂, heq]
      have hsub : Set.range f ⊆ B.vertexSet := by
        rintro _ ⟨i, rfl⟩
        exact (hf i).2
      have hcard_range : (Set.range f).ncard = θ := by
        rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
      have hle : (Set.range f).ncard ≤ B.vertexSet.ncard :=
        Set.ncard_le_ncard hsub B.vertexSet_finite
      omega
    obtain ⟨i, hdisj⟩ := hex_row
    apply hsmallA.2 i
    intro e heP
    have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union.symm ▸ heP.1
    rcases heAB with heA | heB
    · exact heA
    · exfalso
      obtain ⟨a, ha, rfl⟩ := mem_gridRowPath_edgeSet_iff.1 heP
      have hvB : (i, ⟨a, Nat.lt_of_succ_lt ha⟩) ∈ B.vertexSet :=
        B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le heB).2 (rowEdge_inc_left i a ha))
      exact Set.disjoint_left.1 hdisj rfl hvB

end GraphMinor.GM10

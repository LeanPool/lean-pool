/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.Split
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Fin.VecNotation

/-!
# Forbidden induced subgraphs of split graphs

This file proves the necessary direction of the classical Földes–Hammer
characterization. Obstructions use Mathlib graph sums, cycle graphs, and
`IsIndContained`. The converse characterization is not assumed here.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Every edge of a split graph has an endpoint in the clique part. -/
theorem SplitPartition.mem_clique_or_mem_clique_of_adj (P : SplitPartition G)
    {a b : V} (hab : G.Adj a b) : a ∈ P.clique ∨ b ∈ P.clique := by
  rcases P.mem_clique_or_mem_independent a with ha | ha
  · exact Or.inl ha
  rcases P.mem_clique_or_mem_independent b with hb | hb
  · exact Or.inr hb
  exact False.elim (P.isIndepSet ha hb hab.ne hab)

/-- Two disjoint edges cannot have all four cross pairs nonadjacent in a split graph. -/
theorem SplitPartition.not_two_disjoint_edges (P : SplitPartition G) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hnac : ¬G.Adj a c) (hnad : ¬G.Adj a d)
    (hnbc : ¬G.Adj b c) (hnbd : ¬G.Adj b d) : False := by
  rcases P.mem_clique_or_mem_clique_of_adj hab with ha | hb <;>
    rcases P.mem_clique_or_mem_clique_of_adj hcd with hc | hd
  · exact hnac (P.isClique ha hc hac)
  · exact hnad (P.isClique ha hd had)
  · exact hnbc (P.isClique hb hc hbc)
  · exact hnbd (P.isClique hb hd hbd)

/-- Split membership pulls back along native induced-containment certificates. -/
theorem IsSplit.of_isIndContained (h : G.IsSplit) (hf : H.IsIndContained G) :
    H.IsSplit := by
  obtain ⟨f⟩ := hf
  have h' := h.comap f.toEmbedding
  change (G.comap f).IsSplit at h'
  rwa [f.comap_eq] at h'

/-- A pair of disjoint edges with no cross edges supplies a native induced embedding. -/
theorem twoK2_isIndContained_of_adj {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hnac : ¬G.Adj a c) (hnad : ¬G.Adj a d)
    (hnbc : ¬G.Adj b c) (hnbd : ¬G.Adj b d) :
    ((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G := by
  have habNe := hab.ne
  have hcdNe := hcd.ne
  let f : Fin 2 ⊕ Fin 2 → V := Sum.elim ![a, b] ![c, d]
  have hf : Function.Injective f := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨⟨f, hf⟩, ?_⟩⟩
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hcd, hnac, hnad, hnbc, hnbd, G.adj_comm]

/-- The disjoint union of two edges is not split. -/
theorem not_isSplit_twoK2 :
    ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsSplit := by
  rintro ⟨P⟩
  exact P.not_two_disjoint_edges (a := .inl 0) (b := .inl 1)
    (c := .inr 0) (d := .inr 1)
    (by simp) (by simp) (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)

/-- The four-cycle is not split: its complement contains the two opposite edges. -/
theorem not_isSplit_cycleGraph_four : ¬(cycleGraph 4).IsSplit := by
  rintro ⟨P⟩
  exact P.compl.not_two_disjoint_edges (a := 0) (b := 2) (c := 1) (d := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- The five-cycle is not split. Its edge and nonedge constraints exclude every partition. -/
theorem not_isSplit_cycleGraph_five : ¬(cycleGraph 5).IsSplit := by
  rintro ⟨P⟩
  have he (a b : Fin 5) (hab : (cycleGraph 5).Adj a b) :=
    P.mem_clique_or_mem_clique_of_adj hab
  have hn (a b : Fin 5) (hab : a ≠ b) (hnab : ¬(cycleGraph 5).Adj a b) :
      ¬(a ∈ P.clique ∧ b ∈ P.clique) := by
    rintro ⟨ha, hb⟩
    exact hnab (P.isClique ha hb hab)
  have h01 := he 0 1 (by decide)
  have h12 := he 1 2 (by decide)
  have h23 := he 2 3 (by decide)
  have h34 := he 3 4 (by decide)
  have h40 := he 4 0 (by decide)
  have h02 := hn 0 2 (by decide) (by decide)
  have h03 := hn 0 3 (by decide) (by decide)
  have h13 := hn 1 3 (by decide) (by decide)
  have h14 := hn 1 4 (by decide) (by decide)
  have h24 := hn 2 4 (by decide) (by decide)
  tauto

/-- Split graphs exclude an induced disjoint pair of edges. -/
theorem IsSplit.not_twoK2_isIndContained (h : G.IsSplit) :
    ¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G :=
  fun hf => not_isSplit_twoK2 (h.of_isIndContained hf)

/-- Split graphs exclude induced four-cycles. -/
theorem IsSplit.not_cycleGraph_four_isIndContained (h : G.IsSplit) :
    ¬(cycleGraph 4).IsIndContained G :=
  fun hf => not_isSplit_cycleGraph_four (h.of_isIndContained hf)

/-- Split graphs exclude induced five-cycles. -/
theorem IsSplit.not_cycleGraph_five_isIndContained (h : G.IsSplit) :
    ¬(cycleGraph 5).IsIndContained G :=
  fun hf => not_isSplit_cycleGraph_five (h.of_isIndContained hf)

end SimpleGraph

/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Directed

import LeanPool.GraphMinor.GM20.Section10cProved

import LeanPool.GraphMinor.GM20.Section10l

import LeanPool.GraphMinor.GM20.Section8b

/-!
# Graph Minors XX, Section 10, (10.5)

This file proves (10.5) of Graph Minors XX (`GM20.theorem_10_5_proof`, pages 355–356): for every
countable
sequence $G_i$ of finite directed graphs, there exist $j > i$ such that $G_i$ is isomorphic to a
directed minor of $G_j$.

Following the proof on pages 355–356:
- Let $p = 2|E(G_1)| + |V(G_1)|$; if for some $i \ge 2$ the underlying undirected graph $G_i'$ of
  $G_i$ has a minor isomorphic to $K_p$, then $G_i$ has a directed minor isomorphic to $G_1$
  (`isDirMinorModel_of_hasCliqueMinor` in `GraphMinor/GM20/Directed.lean`).
- Otherwise, for $i \ge 2$ let $P_i = (H_i, \mu, \Delta, \phi)$ be `digraphPatchwork (G i)`, where
  $\mu(e)$ enumerates the ends of $e$ tail first, $\Delta(e) = \{N_X, K_X\}$, and $\phi(e) = ()$.
  Then each $P_i$ is a free rootless $\Omega$-patchwork (`isFree_digraphPatchwork`), so
  `theorem_10_4`
  gives $j > i \ge 2$ such that $P_i$ is simulated in $P_j$, and `isDirMinorModel_of_simulated` and
  `isIsoMinor_of_isDirMinorModel` turn that simulation into a directed minor.
- Finally, `wagner_conjecture_undirected_proof` follows immediately by orienting each undirected
  graph via
  `Digraph.ofGraph` and projecting the directed minor to the underlying undirected graphs via
  `Digraph.IsIsoMinor.toGraph`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Graph GraphMinor.GM18 GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-- Proof of (10.5) of Graph Minors XX (pages 355–356) for finite directed graphs on `ℕ`, producing
a directed minor model of `G i` in `G j` for some `i < j`. -/
theorem exists_isDirMinorModel_nat
    (G : ℕ → Digraph ℕ ℕ) (hV : ∀ n, V((G n).toGraph).Finite)
    (hE : ∀ n, E((G n).toGraph).Finite) :
    ∃ i j, i < j ∧ ∃ (ηv : ℕ → Set ℕ) (ηe : ℕ → ℕ), IsDirMinorModel (G i) (G j) ηv ηe := by
  let p := V((G 0).toGraph).ncard + 2 * E((G 0).toGraph).ncard
  by_cases hc : ∃ i, HasCliqueMinor (Hypergraph.ofGraph (G (i + 1)).toGraph (hV _) (hE _)) p
  · obtain ⟨i, hi⟩ := hc
    obtain ⟨ηv, ηe, hm⟩ :=
      isDirMinorModel_of_hasCliqueMinor (hV 0) (hE 0) (hV _) (hE _) le_rfl hi
    exact ⟨0, i + 1, Nat.succ_pos i, ηv, ηe, hm⟩
  · push Not at hc
    obtain ⟨i, j, hij, hsim⟩ := theorem_10_4_proof wellQuasiOrderedLE_unit p
      (fun i ↦ digraphPatchwork (G (i + 1)) (hV _) (hE _))
      (fun i ↦ isFree_digraphPatchwork _ _ _)
      (fun i ↦ Set.eq_empty_of_forall_notMem fun x hx ↦ List.not_mem_nil hx) hc
    obtain ⟨ηv, ηe, hm⟩ := isDirMinorModel_of_simulated hsim
    exact ⟨i + 1, j + 1, by omega, ηv, ηe, hm⟩

/-- Graph Minors XX, (10.5) (page 355):
"**10.5.** *Let* $G_i$ $(i = 1, 2, \dots)$ *be a countable sequence of directed graphs. Then there
exist* $j > i \ge 1$ *such that* $G_i$ *is isomorphic to a minor of* $G_j$." -/
theorem theorem_10_5_proof
    (G : ℕ → Digraph α β) (hV : ∀ n, V((G n).toGraph).Finite)
    (hE : ∀ n, E((G n).toGraph).Finite) :
    ∃ i j, i < j ∧ (G i).IsIsoMinor (G j) := by
  choose G' hV' hE' hiso using fun n ↦ exists_digraph_iso_nat (G n) (hV n) (hE n)
  obtain ⟨i, j, hij, ηv', ηe', hm'⟩ := exists_isDirMinorModel_nat G' hV' hE'
  obtain ⟨φᵢ⟩ := hiso i
  obtain ⟨φⱼ⟩ := hiso j
  obtain ⟨ηv, ηe, hm⟩ := hm'.transport_iso φᵢ φⱼ
  exact ⟨i, j, hij, isIsoMinor_of_isDirMinorModel hm⟩

/-- Graph Minors XX, Section 10 (page 355), the standard form of Wagner's conjecture for undirected
graphs ("As a corollary, we deduce the following form of Wagner’s conjecture for directed graphs
(which immediately implies the standard form of the conjecture for undirected graphs)."):
for every countable sequence `Gᵢ` of finite undirected graphs, there exist `j > i` such that `Gᵢ` is
isomorphic to a minor of `Gⱼ`. -/
theorem wagner_conjecture_undirected_proof
    (G : ℕ → Graph α β) (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  obtain ⟨i, j, hij, h⟩ := theorem_10_5_proof (fun n ↦ Digraph.ofGraph (G n)) hV hE
  exact ⟨i, j, hij, h.toGraph⟩

end GraphMinor.GM20

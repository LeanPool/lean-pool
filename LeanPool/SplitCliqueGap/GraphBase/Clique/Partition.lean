/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Clique partitions and fractional clique partitions

For a finite simple graph `G`:

* `G.IsCliquePartition P`: `P` is a family of cliques of order at least two such that every edge of
`G` lies in
  exactly one member of `P`;
* `G.cliquePartitionNumber`: the least size of a clique partition (`cp(G)`);
* `G.cliqueSets`: the finite set of cliques of order at least two;
* `G.IsFracCliquePartition x`: a nonnegative weighting of the vertex sets, supported on cliques of
order at least
  two, giving every edge total weight exactly one;
* `G.fracCliquePartitionNumber`: the infimum of the total weight of a fractional clique partition
(`cp*(G)`).

## Provenance

The definitions `IsCliquePartition` and `IsFracCliquePartition` are those of `IsCliquePartition` and
`IsFracPartition` in `PaperVIChallenge.lean` of PALOMAR-2026-11-01-000006 (repository
`jtraverso/erdos81-optimal-clique-partitions` @ `719e39b`), where `cp_{≤ r}` and the fractional
value are also
defined. The infimum `fracCliquePartitionNumber` and the API below are new here; the proofs follow
`GapExtremal/Defs.lean` and `GapExtremal/SplitUpper.lean` of the gap-extremal project, except
`exists_isCliquePartition_card_eq_edgeFinset`, whose proof is that of
`exists_isCliqueEdgePartition_card_eq` in
Formal Conjectures (`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Chordal.lean` @
`7bdc4a4`, Apache-2.0).
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*}

/-- A clique partition of `G`: cliques of order at least two such that every edge of `G` lies in
exactly one of
them. -/
structure IsCliquePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop where
  two_le : ∀ B ∈ P, 2 ≤ B.card
  isClique : ∀ B ∈ P, G.IsClique (B : Set V)
  existsUnique : ∀ u v, G.Adj u v → ∃! B, B ∈ P ∧ u ∈ B ∧ v ∈ B

/-- The clique partition number `cp(G)`: the least size of a clique partition. -/
noncomputable def cliquePartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ P, G.IsCliquePartition P ∧ P.card = k}

variable [Fintype V]

open Classical in
/-- The cliques of `G` of order at least two, as a `Finset`. -/
noncomputable def cliqueSets (G : SimpleGraph V) : Finset (Finset V) :=
  univ.filter fun Q => 2 ≤ Q.card ∧ G.IsClique (Q : Set V)

/-- A fractional clique partition: nonnegative weights on vertex sets, supported on cliques of
  order at least
two, with total weight exactly one on every edge. -/
structure IsFracCliquePartition [DecidableEq V] (G : SimpleGraph V) (x : Finset V → ℝ) : Prop where
  nonneg : ∀ Q, 0 ≤ x Q
  support : ∀ Q, x Q ≠ 0 → 2 ≤ Q.card ∧ G.IsClique (Q : Set V)
  edge : ∀ u v, G.Adj u v → ∑ Q ∈ univ.filter (fun Q : Finset V => u ∈ Q ∧ v ∈ Q), x Q = 1

/-- The fractional clique partition number `cp*(G)`. -/
noncomputable def fracCliquePartitionNumber [DecidableEq V] (G : SimpleGraph V) : ℝ :=
  sInf {r | ∃ x, G.IsFracCliquePartition x ∧ ∑ Q, x Q = r}

variable {G : SimpleGraph V}

theorem mem_cliqueSets {Q : Finset V} : Q ∈ G.cliqueSets ↔ 2 ≤ Q.card ∧ G.IsClique (Q : Set V) := by
  classical
  simp [cliqueSets]

section Integral

variable [DecidableEq V]

omit [DecidableEq V] in
/-- The edges, as two-element sets, form a clique partition with `|E(G)|` members. -/
theorem exists_isCliquePartition_card_eq_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, G.IsCliquePartition P ∧ P.card = G.edgeFinset.card := by
  classical
  refine ⟨G.edgeFinset.image Sym2.toFinset, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [Finset.mem_image, mem_edgeFinset]
    rintro s ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he
      rw [Sym2.toFinset_mk_eq, Finset.card_pair he.ne]
  · simp only [Finset.mem_image, mem_edgeFinset]
    rintro s ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he
      rw [Sym2.toFinset_mk_eq, Finset.coe_pair]
      exact isClique_pair.mpr (fun _ => he)
  · intro u v huv
    refine ⟨s(u, v).toFinset,
      ⟨Finset.mem_image.mpr ⟨s(u, v), by simpa using huv, rfl⟩, by simp, by simp⟩, ?_⟩
    rintro s ⟨hs, hu, hv⟩
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Sym2.mem_toFinset] at hu hv
    rw [(Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩]
  · apply Finset.card_image_of_injOn
    intro e he e' _ h
    simp only [mem_edgeFinset, Finset.mem_coe] at he
    induction e using Sym2.ind with
    | h a b =>
      have hab := (mem_edgeSet G).mp he
      have ha : a ∈ e'.toFinset := by rw [← h]; simp
      have hb : b ∈ e'.toFinset := by rw [← h]; simp
      rw [Sym2.mem_toFinset] at ha hb
      exact ((Sym2.mem_and_mem_iff hab.ne).mp ⟨ha, hb⟩).symm

omit [Fintype V] [DecidableEq V] in
/-- The edges, as pairs, form a clique partition. -/
theorem exists_isCliquePartition [Finite V] (G : SimpleGraph V) : ∃ P, G.IsCliquePartition P := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨P, hP, _⟩ := exists_isCliquePartition_card_eq_edgeFinset G
  exact ⟨P, hP⟩

omit [Fintype V] [DecidableEq V] in
theorem cliquePartitionNumber_le {P : Finset (Finset V)} (hP : G.IsCliquePartition P) :
    G.cliquePartitionNumber ≤ P.card :=
  Nat.sInf_le ⟨P, hP, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem exists_isCliquePartition_card_eq [Finite V] (G : SimpleGraph V) :
    ∃ P, G.IsCliquePartition P ∧ P.card = G.cliquePartitionNumber := by
  obtain ⟨P, hP⟩ := exists_isCliquePartition G
  exact Nat.sInf_mem (s := {k | ∃ P, G.IsCliquePartition P ∧ P.card = k}) ⟨P.card, P, hP, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem le_cliquePartitionNumber [Finite V] {k : ℕ} (h : ∀ P, G.IsCliquePartition P → k ≤ P.card) :
    k ≤ G.cliquePartitionNumber := by
  obtain ⟨P, hP, hc⟩ := exists_isCliquePartition_card_eq G
  exact hc ▸ h P hP

omit [Fintype V] [DecidableEq V] in
theorem cliquePartitionNumber_eq_of [Finite V] {k : ℕ} (hlow : ∀ P, G.IsCliquePartition P → k
  ≤ P.card)
    (hup : ∃ P, G.IsCliquePartition P ∧ P.card ≤ k) : G.cliquePartitionNumber = k := by
  obtain ⟨P, hP, hPk⟩ := hup
  exact le_antisymm ((cliquePartitionNumber_le hP).trans hPk) (le_cliquePartitionNumber hlow)

omit [Fintype V] [DecidableEq V] in
theorem exists_isCliquePartition_card_le [Finite V] (G : SimpleGraph V) :
    ∃ P, G.IsCliquePartition P ∧ P.card ≤ G.cliquePartitionNumber := by
  obtain ⟨P, hP, hc⟩ := exists_isCliquePartition_card_eq G
  exact ⟨P, hP, hc.le⟩

omit [Fintype V] [DecidableEq V] in
theorem cliquePartitionNumber_le_iff [Finite V] (G : SimpleGraph V) {m : ℕ} :
    G.cliquePartitionNumber ≤ m ↔ ∃ P, G.IsCliquePartition P ∧ P.card ≤ m := by
  constructor
  · intro h
    obtain ⟨P, hP, hc⟩ := exists_isCliquePartition_card_eq G
    exact ⟨P, hP, hc.le.trans h⟩
  · rintro ⟨P, hP, hc⟩
    exact (cliquePartitionNumber_le hP).trans hc

omit [DecidableEq V] in
/-- The members of a clique partition are cliques of order at least two. -/
theorem IsCliquePartition.subset_cliqueSets {P : Finset (Finset V)} (hP : G.IsCliquePartition P) :
    P ⊆ G.cliqueSets := fun Q hQ => mem_cliqueSets.mpr ⟨hP.two_le Q hQ, hP.isClique Q hQ⟩

end Integral

section Fractional

variable [DecidableEq V]

theorem fracCliquePartitionNumber_le {x : Finset V → ℝ} (hx : G.IsFracCliquePartition x) :
    G.fracCliquePartitionNumber ≤ ∑ Q, x Q :=
  csInf_le ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact sum_nonneg fun Q _ => hy.nonneg Q⟩ ⟨x, hx, rfl⟩

/-- The total weight of a fractional clique partition is carried by `cliqueSets`. -/
theorem IsFracCliquePartition.sum_cliqueSets {x : Finset V → ℝ} (hx : G.IsFracCliquePartition x) :
    ∑ Q ∈ G.cliqueSets, x Q = ∑ Q, x Q := by
  refine sum_subset (subset_univ _) fun Q _ hQ => ?_
  by_contra h
  exact hQ (mem_cliqueSets.mpr (hx.support Q h))

/-- The indicator of a clique partition is a fractional clique partition. -/
theorem IsCliquePartition.isFracCliquePartition {P : Finset (Finset V)}
    (hP : G.IsCliquePartition P) :
    G.IsFracCliquePartition (fun Q => if Q ∈ P then 1 else 0) := by
  refine ⟨fun Q => by split_ifs <;> norm_num, fun Q hQ => ?_, fun u v huv => ?_⟩
  · have : Q ∈ P := by by_contra h; simp [h] at hQ
    exact ⟨hP.two_le Q this, hP.isClique Q this⟩
  · obtain ⟨B, ⟨hB, huB, hvB⟩, huniq⟩ := hP.existsUnique u v huv
    rw [sum_eq_single_of_mem B (by simp [huB, hvB]) fun Q hQ hne => ?_]
    · simp [hB]
    · simp only [mem_filter, mem_univ, true_and] at hQ
      rw [ite_eq_right_iff]
      intro hQP
      exact absurd (huniq Q ⟨hQP, hQ.1, hQ.2⟩) hne

/-- `cp*(G) ≤ cp(G)`. -/
theorem fracCliquePartitionNumber_le_cliquePartitionNumber (G : SimpleGraph V) :
    G.fracCliquePartitionNumber ≤ G.cliquePartitionNumber := by
  obtain ⟨P, hP, hc⟩ := exists_isCliquePartition_card_eq G
  refine (fracCliquePartitionNumber_le hP.isFracCliquePartition).trans_eq ?_
  rw [← hc, ← sum_filter]
  simp

theorem nonempty_fracCliquePartition (G : SimpleGraph V) :
    ∃ x, G.IsFracCliquePartition x := by
  obtain ⟨P, hP⟩ := exists_isCliquePartition G
  exact ⟨_, hP.isFracCliquePartition⟩

theorem le_fracCliquePartitionNumber {r : ℝ}
    (h : ∀ x, G.IsFracCliquePartition x → r ≤ ∑ Q, x Q) : r ≤ G.fracCliquePartitionNumber := by
  obtain ⟨x, hx⟩ := nonempty_fracCliquePartition G
  exact le_csInf ⟨_, x, hx, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

theorem fracCliquePartitionNumber_nonneg (G : SimpleGraph V) :
    0 ≤ G.fracCliquePartitionNumber :=
  le_fracCliquePartitionNumber fun _ hx => sum_nonneg fun Q _ => hx.nonneg Q

theorem fracCliquePartitionNumber_eq_of {r : ℝ}
    (hlow : ∀ x, G.IsFracCliquePartition x → r ≤ ∑ Q, x Q)
    {x : Finset V → ℝ} (hx : G.IsFracCliquePartition x) (hxr : ∑ Q, x Q = r) :
    G.fracCliquePartitionNumber = r :=
  IsLeast.csInf_eq ⟨⟨x, hx, hxr⟩, by rintro _ ⟨y, hy, rfl⟩; exact hlow y hy⟩

end Fractional

end SimpleGraph

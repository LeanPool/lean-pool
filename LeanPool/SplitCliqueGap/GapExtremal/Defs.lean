/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GraphBase.Clique.CliqueSets

/-!
# The integrality gap (ledger §0.1)

Clique partitions, `cp`, fractional clique partitions and `cp*` are GraphBase's
(`SimpleGraph.IsCliquePartition`, `cliquePartitionNumber`, `IsFracCliquePartition`,
`fracCliquePartitionNumber`,
`cliqueSets`). Migrated 2026-11-18; until then this file had its own copies (from the B16 "PAIR"
development).

* `gap G = cp G − cp* G`, the object of the paper;
* `IsClq G Q`: a convenience form of `Q ∈ G.cliqueSets` (`mem_cliqueSets_iff_isClq`), whose second
component
  takes its arguments explicitly.
-/

@[expose] public section

open Finset

namespace GapExtremal

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Q` has at least two vertices, all pairwise adjacent. Equivalent to `Q ∈ G.cliqueSets`. -/
def IsClq (G : SimpleGraph V) (Q : Finset V) : Prop :=
  2 ≤ Q.card ∧ ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → G.Adj u v

omit [Fintype V] [DecidableEq V] in
theorem isClq_iff {G : SimpleGraph V} {Q : Finset V} : IsClq G Q ↔ 2 ≤ Q.card ∧ G.IsClique (Q :
  Set V) :=
  ⟨fun h => ⟨h.1, fun u hu v hv huv => h.2 u hu v hv huv⟩,
    fun h => ⟨h.1, fun _ hu _ hv huv => h.2 hu hv huv⟩⟩

omit [DecidableEq V] in
theorem mem_cliqueSets_iff_isClq {G : SimpleGraph V} {Q : Finset V} : Q ∈ G.cliqueSets ↔ IsClq G Q
  :=
  SimpleGraph.mem_cliqueSets.trans isClq_iff.symm

omit [Fintype V] [DecidableEq V] in
/-- The members of a GraphBase clique partition satisfy `IsClq`. -/
theorem _root_.SimpleGraph.IsCliquePartition.isClq {G : SimpleGraph V} {P : Finset (Finset V)}
    (hP : G.IsCliquePartition P) {Q : Finset V} (hQ : Q ∈ P) : IsClq G Q :=
  isClq_iff.mpr ⟨hP.two_le Q hQ, hP.isClique Q hQ⟩

/-- The integrality gap `D G = cp G − cp* G`. -/
noncomputable def gap (G : SimpleGraph V) : ℝ :=
  (G.cliquePartitionNumber : ℝ) - G.fracCliquePartitionNumber

end General

end GapExtremal

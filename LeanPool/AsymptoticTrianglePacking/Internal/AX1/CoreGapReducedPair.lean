/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the regularity-reduced graph agrees with `G` on a good cluster pair

`SimpleGraph.regularityReduced P G ep de` keeps exactly the edges of `G` whose endpoints lie in two
*distinct* parts of `P` that are `ep`-uniform of density at least `de`.  In particular, on such a
pair `(U, W)` the reduced graph **is** `G`, so all uniformity and density data of the pair — and of
all its sub-blocks — transfer verbatim.  The deterministic grid construction needs exactly that:
its blocks are uniform and dense for `G`, but the design it has to produce is a design for the
reduced graph.

* `Nibble.AX1.regularityReduced_adj_iff_of_goodPair` — the adjacency agrees;
* `Nibble.AX1.interedges_regularityReduced`, `Nibble.AX1.edgeDensity_regularityReduced` — the
  interedges and densities of sub-blocks agree;
* `Nibble.AX1.isUniform_regularityReduced` — uniformity of a pair of sub-blocks transfers.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularCover

/-! # CoreGapReducedPair -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **On a good cluster pair the reduced graph agrees with `G`.** -/
theorem regularityReduced_adj_iff_of_goodPair (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {U W : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    {x y : V} (hx : x ∈ U) (hy : y ∈ W) :
    (G.regularityReduced P ep de).Adj x y ↔ G.Adj x y := by
  constructor
  · intro h; exact h.1
  · intro h
    exact ⟨h, U, hU, W, hW, hx, hy, hUW, hu, hd⟩

/-- The interedges of two sub-blocks of a good cluster pair are the same in `G` and in the reduced
graph. -/
theorem interedges_regularityReduced (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {U W A B : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    (hA : A ⊆ U) (hB : B ⊆ W) :
    (G.regularityReduced P ep de).interedges A B = G.interedges A B := by
  ext p
  obtain ⟨x, y⟩ := p
  simp only [SimpleGraph.mk_mem_interedges_iff]
  constructor
  · rintro ⟨hx, hy, hadj⟩
    exact ⟨hx, hy, hadj.1⟩
  · rintro ⟨hx, hy, hadj⟩
    exact ⟨hx, hy,
      (regularityReduced_adj_iff_of_goodPair G P hU hW hUW hu hd (hA hx) (hB hy)).mpr hadj⟩

/-- The densities of two sub-blocks of a good cluster pair are the same in `G` and in the reduced
graph. -/
theorem edgeDensity_regularityReduced (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {U W A B : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    (hA : A ⊆ U) (hB : B ⊆ W) :
    (G.regularityReduced P ep de).edgeDensity A B = G.edgeDensity A B := by
  rw [SimpleGraph.edgeDensity_def, SimpleGraph.edgeDensity_def,
    interedges_regularityReduced G P hU hW hUW hu hd hA hB]

/-- **Uniformity of a pair of sub-blocks transfers to the reduced graph.** -/
theorem isUniform_regularityReduced (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de ε : ℝ} {U W A B : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hUW : U ≠ W)
    (hu : G.IsUniform ep U W) (hd : de ≤ (G.edgeDensity U W : ℝ))
    (hA : A ⊆ U) (hB : B ⊆ W) (h : G.IsUniform ε A B) :
    (G.regularityReduced P ep de).IsUniform ε A B := by
  intro A' hA' B' hB' hcA hcB
  have h1 : (G.regularityReduced P ep de).edgeDensity A' B' = G.edgeDensity A' B' :=
    edgeDensity_regularityReduced G P hU hW hUW hu hd (hA'.trans hA) (hB'.trans hB)
  have h2 : (G.regularityReduced P ep de).edgeDensity A B = G.edgeDensity A B :=
    edgeDensity_regularityReduced G P hU hW hUW hu hd hA hB
  rw [h1, h2]
  exact h hA' hB' hcA hcB

end Nibble.AX1

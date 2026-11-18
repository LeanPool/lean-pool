/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import LeanPool.FiniteRamsey.InfiniteRamseyKUniform
import LeanPool.FiniteRamsey.MonochromaticKUniform

/-!
# The infinite Ramsey theorem for pairs

Every other file in this series is finite-vertex. This file proves the classical infinite Ramsey
theorem instead: any finite colouring of the edges of the complete graph on an infinite vertex
set contains an infinite monochromatic clique. Nothing in mathlib proves this: the library's other
two results named "Ramsey," Hindman's theorem and the Hales–Jewett theorem, are different
theorems.

## Main declarations

* `SimpleGraph.exists_infinite_monochromatic`: the theorem itself, for `[Finite K]`, a colouring
  `C : TopEdgeLabeling V K`, and an infinite `X0 : Set V`, there is a colour `k` and an infinite
  `H ⊆ X0` with `(C.labelGraph k).IsClique H`.

## Proof

A thin corollary of `InfiniteRamseyKUniform.lean`'s general `k`-uniform infinite Ramsey theorem, at
`k = 2`: pairs from an infinite set are exactly `2`-element `Finset`s, so it only remains to bridge
vocabulary between `TopEdgeLabeling`'s `V → V → K`-shaped colouring of edges and the general
theorem's `Finset V → K`-shaped colouring of `2`-element subsets. That bridge (`pairColouring`,
`pairColouring_eq`) lives in `MonochromaticKUniform.lean`, not here: it is finite/infinite-agnostic
content in its own right, shared with that file's other use of it (relating `u = 2` monochromatic
`Finset`-cliques to ordinary graph cliques in the finite case).
`exists_infinite_monochromatic` unpacks the general theorem's `col`/`H`/`hmono` directly into the
`IsClique` conclusion.

## Implementation notes

Stated for `V K : Type` rather than `Type*`, inherited from `ExistsInfiniteMonochromaticKUniform`'s
own universe restriction (see `InfiniteRamseyKUniform.lean`'s implementation notes); a
universe-polymorphic version of the general theorem, and hence of this corollary, is not currently
available.

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2) 30 (1930), 264-286.
  (Ramsey's original theorem is stated and proved for infinite sets; the finite case is derived
  from it in the same paper.)

## Tags

ramsey theory, infinite combinatorics, pigeonhole principle
-/

@[expose] public section

namespace SimpleGraph

variable {V K : Type} [Finite K]

/-- The infinite Ramsey theorem for pairs. Any finite colouring of the edges of the complete graph
on an infinite vertex set has an infinite monochromatic clique. -/
theorem exists_infinite_monochromatic (C : TopEdgeLabeling V K) {X0 : Set V} (hX0 : X0.Infinite) :
    ∃ (k : K) (H : Set V), H ⊆ X0 ∧ H.Infinite ∧ (C.labelGraph k).IsClique H := by
  classical
  obtain ⟨p, hp⟩ := hX0.nonempty
  obtain ⟨q, hq⟩ := (hX0.sdiff (Set.finite_singleton p)).nonempty
  have hqp : q ≠ p := by simpa using hq.2
  obtain ⟨col, H, hHsub, hHinf, hmono⟩ :=
    existsInfiniteMonochromaticKUniform 2 (pairColouring C (C.get q p hqp)) hX0
  refine ⟨col, H, hHsub, hHinf, fun x hx y hy hxy => ?_⟩
  have hval := hmono {x, y} (by simp [Set.insert_subset_iff, hx, hy])
    (Finset.card_pair_eq_two_iff.mpr hxy)
  rw [pairColouring_eq C (C.get q p hqp) hxy] at hval
  exact (TopEdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, hval⟩

/-- A concrete edge labelling of the complete graph on `ℕ`, by the parity of the sum of the two
endpoints. -/
noncomputable def parityLabeling : TopEdgeLabeling ℕ Bool :=
  EdgeLabeling.mk (fun x y _ => decide (Even (x + y))) (fun x y _ => by rw [Nat.add_comm])

/-- Worked example: colouring the edges of the complete graph on `ℕ` by the parity of the sum of
their endpoints, some parity is attained on every edge of a fixed infinite clique. An instance of
`exists_infinite_monochromatic`. -/
theorem exists_infinite_monochromatic_parity_example :
    ∃ (col : Bool) (H : Set ℕ), H.Infinite ∧ (parityLabeling.labelGraph col).IsClique H :=
  let ⟨col, H, _, hH, hmono⟩ := exists_infinite_monochromatic parityLabeling Set.infinite_univ
  ⟨col, H, hH, hmono⟩

end SimpleGraph

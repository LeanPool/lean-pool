/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.RamseyProperty
public import LeanPool.FiniteRamsey.BinomialBound
import LeanPool.FiniteRamsey.MonochromaticClique

/-!
# Ramsey's theorem for graphs

This file proves, unconditionally, that classical two-colour graph Ramsey numbers exist
(Ramsey's theorem for graphs), together with the classical recursive bound and the
Erdős–Szekeres binomial upper bound. It builds on the `RamseyProperty` API (definition,
colour-swap symmetry, monotonicity) from `RamseyProperty.lean` and the generic
`Combinatorics.Ramsey.le_binomialBound_of_pascalRecursive` induction skeleton from
`BinomialBound.lean`: the classical two-colour clique-Ramsey predicate is Pascal-recursive
(`ramseyProperty_recursive` below supplies the recursive step), so the binomial bound and
existence are immediate instances, not a second copy of the induction.

## Main declarations

* `SimpleGraph.ramseyProperty_recursive`: the classical recursive bound. If a host of size `m`
  has the `(r, s+1)` property and a host of size `n` has the `(r+1, s)` property, a host of size
  `m + n` has the `(r+1, s+1)` property: the pigeonhole argument splitting on one vertex's
  red/blue degree that drives everything below.
* `SimpleGraph.ramseyBinomialBound r s`: the classical bound `(r + s - 2).choose (r - 1)`, an
  abbreviation for `Combinatorics.Ramsey.binomialBound r s`.
* `SimpleGraph.ramsey_upper_bound`: `RamseyProperty (ramseyBinomialBound r s) r s`, an instance of
  `Combinatorics.Ramsey.le_binomialBound_of_pascalRecursive`.
* `SimpleGraph.exists_ramseyProperty r s : ∃ n, RamseyProperty n r s`: Ramsey's theorem for
  graphs, unconditionally, for every pair of clique sizes.

## Proof outline

The classical Erdős–Szekeres argument. Fix a vertex `v` of a host of size `m + n`; by a pigeonhole
count on its red/blue degree split (`card_red_add_blue_neighborFinset`), `v` has at least `m` red
neighbours or at least `n` blue neighbours. In the first case, the `(r, s+1)`-property on those `m`
red neighbours finds either the desired blue `(s+1)`-clique directly, or a red `r`-clique among
them that extends by `v` to a red `(r+1)`-clique (`v` is red-adjacent to all of them); symmetrically
in the second case. This is exactly `le_binomialBound_of_pascalRecursive`'s recursive-step
hypothesis, and the degenerate base cases match its remaining hypotheses directly, so
`RamseyProperty` holding at the binomial bound, in particular existence, falls out of the generic
induction skeleton with no further induction needed here.

## Scope

This file covers only the recursive bound, the binomial bound, and existence, not the
parity-refined recursive bound (a one-less-vertex improvement when both recursive host sizes are
even, needing a red/blue-degree-sum parity argument on top of what is here). Colour-swap symmetry,
monotonicity in the clique-size parameters, and the least-Ramsey-number definition built on top of
existence are separate concerns, not repeated here beyond what existence itself needs.

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2) 30 (1930), 264-286.
* P. Erdős, G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935), 463-470.

## Tags

ramsey theory, combinatorics, graph coloring
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-! ### Degenerate base cases -/

theorem ramseyProperty_red_zero (n s : ℕ) : RamseyProperty n 0 s := fun _ =>
  Or.inl ⟨∅, by simp⟩

theorem ramseyProperty_blue_zero (n r : ℕ) : RamseyProperty n r 0 := fun _ =>
  Or.inr ⟨∅, by simp⟩

/-! ### The one-vertex recursive step -/

section RecursiveStep

variable [Fintype V] [DecidableEq V]

/-- The red neighbours of `v` under a two-colouring `C`, as a `Finset`. -/
noncomputable def redNeighborFinset (C : TwoColoring V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => (C.labelGraph true).Adj v w

/-- The blue neighbours of `v` under a two-colouring `C`, as a `Finset`. -/
noncomputable def blueNeighborFinset (C : TwoColoring V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => (C.labelGraph false).Adj v w

@[simp]
theorem mem_redNeighborFinset {C : TwoColoring V} {v w : V} :
    w ∈ redNeighborFinset C v ↔ (C.labelGraph true).Adj v w := by
  classical
  simp [redNeighborFinset]

@[simp]
theorem mem_blueNeighborFinset {C : TwoColoring V} {v w : V} :
    w ∈ blueNeighborFinset C v ↔ (C.labelGraph false).Adj v w := by
  classical
  simp [blueNeighborFinset]

/-- A `TwoColoring`'s two label graphs at a fixed vertex partition every other vertex into "red
neighbour" or "blue neighbour": these two sets are disjoint. -/
theorem redNeighborFinset_disjoint_blueNeighborFinset (C : TwoColoring V) (v : V) :
    Disjoint (redNeighborFinset C v) (blueNeighborFinset C v) :=
  Finset.disjoint_left.mpr fun _ ↦ by simp_all

/-- Every vertex other than `v` is a red neighbour or a blue neighbour of `v`. -/
theorem red_blue_neighborFinset_union_eq_erase (C : TwoColoring V) (v : V) :
    redNeighborFinset C v ∪ blueNeighborFinset C v = Finset.univ.erase v := by
  ext w
  rcases eq_or_ne v w with rfl | h
  · simp
  · simp [h, h.symm]

/-- **The red/blue-degree pigeonhole count.** Every vertex other than `v` is counted exactly once
as a red or blue neighbour of `v`, so the two neighbour-counts sum to `|V| - 1`. -/
theorem card_red_add_blue_neighborFinset (C : TwoColoring V) (v : V) :
    (redNeighborFinset C v).card + (blueNeighborFinset C v).card = Fintype.card V - 1 := by
  classical
  rw [← Finset.card_union_of_disjoint (redNeighborFinset_disjoint_blueNeighborFinset C v),
    red_blue_neighborFinset_union_eq_erase]
  simp

/-- **Pigeonhole.** If a host has exactly `m + n` vertices, every vertex has at least `m` red
neighbours or at least `n` blue neighbours. -/
theorem red_or_blue_neighborFinset_large (C : TwoColoring V) (v : V) (m n : ℕ)
    (hcard : Fintype.card V = m + n) :
    m ≤ (redNeighborFinset C v).card ∨ n ≤ (blueNeighborFinset C v).card := by
  have := card_red_add_blue_neighborFinset C v
  omega

end RecursiveStep

section Pullback

variable {W : Type*}

/-- **Extending a clique by one vertex.** If a set of vertices, pulled back along an embedding
whose range is contained in `v`'s red neighbourhood, has a red `n`-clique, then `v` together with
its image is a red `(n + 1)`-clique of the original colouring. -/
theorem hasRedClique_succ_of_pullback_redClique_of_range_subset_redNeighbor
    [Fintype W] [DecidableEq W] (C : TwoColoring W) (f : V ↪ W) (v : W) {n : ℕ}
    (hrange : Set.range f ⊆ (redNeighborFinset C v : Set W))
    (h : HasRedClique (C.pullback f) n) : HasRedClique C (n + 1) :=
  let ⟨_, hs⟩ := h
  ⟨_, (monochromaticClique_map_pullback C f true hs).insert fun _ hw ↦
    let ⟨x, _, hx⟩ := Finset.mem_map.mp hw; mem_redNeighborFinset.mp (hx ▸ hrange ⟨x, rfl⟩)⟩

/-- The blue analogue of `hasRedClique_succ_of_pullback_redClique_of_range_subset_redNeighbor`. -/
theorem hasBlueClique_succ_of_pullback_blueClique_of_range_subset_blueNeighbor
    [Fintype W] [DecidableEq W] (C : TwoColoring W) (f : V ↪ W) (v : W) {n : ℕ}
    (hrange : Set.range f ⊆ (blueNeighborFinset C v : Set W))
    (h : HasBlueClique (C.pullback f) n) : HasBlueClique C (n + 1) :=
  let ⟨_, hs⟩ := h
  ⟨_, (monochromaticClique_map_pullback C f false hs).insert fun _ hw ↦
    let ⟨x, _, hx⟩ := Finset.mem_map.mp hw; mem_blueNeighborFinset.mp (hx ▸ hrange ⟨x, rfl⟩)⟩

end Pullback

/-! ### The recursive bound -/

/-- If a host of size `m` handles `(r, s + 1)`, then any vertex `v` of a larger host with `≥ m`
red neighbours either directly finds a blue `(s + 1)`-clique, or finds a red `r`-clique among
those neighbours which extends by `v` to a red `(r + 1)`-clique. -/
theorem ramseyProperty_of_large_redNeighbor [Fintype V] [DecidableEq V]
    (C : TwoColoring V) (v : V) {m r s : ℕ} (hlarge : m ≤ (redNeighborFinset C v).card)
    (hRamsey : RamseyProperty m r s) : HasRedClique C (r + 1) ∨ HasBlueClique C s :=
  let ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin m) (by simpa using hlarge)
  (hRamsey (C.pullback f)).imp
    (hasRedClique_succ_of_pullback_redClique_of_range_subset_redNeighbor C f v hf)
    (EdgeLabeling.hasMonochromaticClique_map_pullback C f false)

/-- The blue analogue of `ramseyProperty_of_large_redNeighbor`. -/
theorem ramseyProperty_of_large_blueNeighbor [Fintype V] [DecidableEq V]
    (C : TwoColoring V) (v : V) {m r s : ℕ} (hlarge : m ≤ (blueNeighborFinset C v).card)
    (hRamsey : RamseyProperty m r s) : HasRedClique C r ∨ HasBlueClique C (s + 1) :=
  let ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin m) (by simpa using hlarge)
  (hRamsey (C.pullback f)).imp (EdgeLabeling.hasMonochromaticClique_map_pullback C f true)
    (hasBlueClique_succ_of_pullback_blueClique_of_range_subset_blueNeighbor C f v hf)

/-- **The classical recursive Ramsey bound.** If a host of size `m` handles `(r, s + 1)` and a
host of size `n` handles `(r + 1, s)`, then a nonempty host of size `m + n` handles `(r + 1,
s + 1)`: fix any vertex, split on its red/blue degree by pigeonhole
(`red_or_blue_neighborFinset_large`), and apply whichever of the two one-vertex-extension lemmas
above matches. -/
theorem ramseyProperty_recursive (m n r s : ℕ) (hpos : 0 < m + n)
    (hred : RamseyProperty m r (s + 1)) (hblue : RamseyProperty n (r + 1) s) :
    RamseyProperty (m + n) (r + 1) (s + 1) := fun C ↦
  (red_or_blue_neighborFinset_large C ⟨0, hpos⟩ m n (by simp)).elim
    (ramseyProperty_of_large_redNeighbor C _ · hred)
    (ramseyProperty_of_large_blueNeighbor C _ · hblue)

/-! ### The binomial bound and existence -/

/-- **The classical binomial Ramsey bound**, `(r + s - 2).choose (r - 1)`: the Erdős–Szekeres
upper bound on the least `n` making `RamseyProperty n r s` hold. An abbreviation for
`Combinatorics.Ramsey.binomialBound`, kept under a Ramsey-domain name for readability in the
statements below. -/
abbrev ramseyBinomialBound (r s : ℕ) : ℕ :=
  Combinatorics.Ramsey.binomialBound r s

/-- **Ramsey's theorem for graphs, the binomial upper bound.** Every host of size
`ramseyBinomialBound r s` has the `(r, s)` Ramsey property. The classical two-colour clique-Ramsey
predicate `RamseyProperty` satisfies `le_binomialBound_of_pascalRecursive`'s hypotheses — the
degenerate base cases are `ramseyProperty_red_zero`/`_blue_zero`/`ramseyProperty_one_red`/
`_one_blue`, and the recursive step is exactly `ramseyProperty_recursive` — so the binomial bound
is an immediate instance of the generic induction skeleton. -/
theorem ramsey_upper_bound (r s : ℕ) : RamseyProperty (ramseyBinomialBound r s) r s :=
  Combinatorics.Ramsey.le_binomialBound_of_pascalRecursive ramseyProperty_red_zero
    ramseyProperty_blue_zero ramseyProperty_one_red ramseyProperty_one_blue
    (fun {m n r s} => ramseyProperty_recursive m n r s) r s

/-- **Ramsey's theorem for graphs.** For every pair of clique sizes `r, s`, some finite host size
`n` makes every two-colouring of `K_n`'s edges contain a red `r`-clique or a blue `s`-clique.
Unconditional existence, with an explicit witness (`ramseyBinomialBound r s`). -/
theorem exists_ramseyProperty (r s : ℕ) : ∃ n, RamseyProperty n r s :=
  ⟨ramseyBinomialBound r s, ramsey_upper_bound r s⟩

/-! ### A worked example -/

/-- A concrete instance of the binomial upper bound: `RamseyProperty 6 3 3` holds, since
`ramseyBinomialBound 3 3 = 6`. This is the upper half of the classical fact `R(3, 3) = 6`. -/
theorem ramseyProperty_six_three_three : RamseyProperty 6 3 3 :=
  ramsey_upper_bound 3 3

end SimpleGraph

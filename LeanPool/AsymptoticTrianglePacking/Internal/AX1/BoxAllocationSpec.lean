/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **small-box allocation residual** of the coarse-cell route

`Nibble.AX1.BlockCoverResidualCoupled` (`Nibble.CoreGapBlockCoverCoupled`) is reduced, in
`Nibble.CoarseCellCoupled`, to a purely combinatorial *allocation* statement about a grid of coarse
cells, stated here.

The picture.  Every cluster is cut into `P` coarse cells.  A *copy* `c` (one member of the family to
be built) lives on a triple of distinct clusters `cl c 0, cl c 1, cl c 2` and has to occupy, in the
cluster `cl c a`, a set `I c a` of exactly `sz c a` coarse cells — the prescribed size, `sz c a`
being dictated by the density of the pair *opposite* to `a`.  The *same* set `I c a` is seen by both
cluster pairs through `cl c a`, which is the three-way coherence of the allocation.  Two copies
sharing a cluster pair must occupy disjoint rectangles of the cell grid of that pair; by
`Nibble.AX1.boxCompat_iff_disjoint_product` that is the disjunction

    Disjoint (I c a) (I c' a')  ∨  Disjoint (I c b) (I c' b')

for the two positions `a, b` of `c` and `a', b'` of `c'` carrying the shared pair.

`Nibble.AX1.boxDemand` is the total area demanded in one ordered cluster pair, and the hypothesis of
the residual is that it is below a `(1 - ε)` fraction of the capacity `P²` of the grid of the pair.
The conclusion allows a set `bad` of copies to be left unplaced, of total area at most
`ε·(#clusters)²·P²` — the loss this produces in the covering sum of the residual.

The restriction `s₀ ≤ θ·P` to **small boxes** is essential and is what the reduction supplies:
`Nibble.AX1.box_allocation_infeasible` (`Nibble.CellBoxAllocation`) shows that a `P × 1` box and a
`1 × P` box can never be placed compatibly, so no allocation statement without a smallness
restriction can hold.  In the reduction the prescribed sizes are `⌈K·d/δ⌉ ≤ ⌈K/δ⌉`, a constant, while
the number `P` of cells per cluster grows with the accuracy, so the restriction is met.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CellBoxAllocation
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Bound

/-! # BoxAllocationSpec -/

@[expose] public section

open Finset

namespace Nibble.AX1

/-- **The area demanded in the ordered cluster pair `(S, T)`**: every copy through both clusters
contributes the product of its two prescribed sizes there. -/
def boxDemand {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ) (S T : ι) : ℝ :=
  ∑ c : κ, ∑ a : ZMod 3, ∑ b : ZMod 3,
    if cl c a = S ∧ cl c b = T then (sz c a : ℝ) * (sz c b : ℝ) else 0

/-- **The small-box allocation residual.**  For every accuracy `ε` and every box bound `s₀` there is
a smallness threshold `θ` such that, whenever the prescribed sizes are at most `s₀ ≤ θ·P` and the
demand of every cluster pair is at most `(1 - ε)·P²`, all copies can be given cell sets of the
prescribed sizes, three-way coherent by construction, so that any two copies sharing a cluster pair
occupy disjoint rectangles of the cell grid of that pair — apart from a set `bad` of copies of total
area at most `ε·(#clusters)²·P²`.

The threshold `θ` is allowed to depend on the box bound `s₀` as well as on `ε`.  This is what the
reduction of `Nibble.CoarseCellCoupled` supplies (there `s₀ = ⌈K/δ⌉` is fixed by the accuracy of the
block-cover residual, while the number `P` of cells per cluster is driven to infinity afterwards),
and it is what a nibble proof needs: the placement hypergraph has uniformity of order `s₀²`, and the
codegree threshold of `Nibble.fracNibbleWeighted_nearPerfect` degrades with the uniformity, so `θ`
cannot be chosen before `s₀` is known. -/
def BoxAllocationResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ s₀ : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    ∀ P : ℕ, 0 < P → (s₀ : ℝ) ≤ θ * (P : ℝ) →
    ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ),
      (∀ c, Function.Injective (cl c)) →
      (∀ c a, 1 ≤ sz c a) → (∀ c a, sz c a ≤ s₀) →
      (∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (1 - ε) * (P : ℝ) ^ 2) →
      ∃ (bad : Finset κ) (I : κ → ZMod 3 → Finset (Fin P)),
        (∀ c a, #(I c a) = sz c a) ∧
        (∀ c ∉ bad, ∀ c' ∉ bad, c ≠ c' → ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' →
          cl c a = cl c' a' → cl c b = cl c' b' →
          Disjoint (I c a) (I c' a') ∨ Disjoint (I c b) (I c' b')) ∧
        (∑ c ∈ bad, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
          ≤ ε * (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2

end Nibble.AX1

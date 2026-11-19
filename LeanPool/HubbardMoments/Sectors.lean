/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Combinatorics.Subsets
public import LeanPool.HubbardMoments.Defs
import Mathlib.Tactic.NormNum

/-!
# Sector dimensions

Proofs about `HubbardMoments.sector` (defined in `HubbardMoments.Defs`).

A basis state of `a` spin-up and `b` spin-down electrons on a finite set of sites `V`
is a pair `(u, d)` of subsets of `V` with `|u| = a` and `|d| = b`: the sites holding an
up electron and the sites holding a down electron. Its doublon number is `|u ∩ d|`,
the number of doubly occupied sites. The `k`-doublon sector is the set of basis states
with doublon number `k`.

## Main results

* `card_sector`: if `k ≤ b`, the `k`-doublon sector has
  `C(N, a) · C(a, k) · C(N - a, b - k)` states, where `N = |V|`.
* `card_sector'`: the same number written as `C(N, k) · C(N - k, a - k) · C(N - a, b - k)`
  (place the doublons, then the remaining up electrons, then the remaining down
  electrons), for `k ≤ a`.
* `sector_dims_L4_two_two`, `sector_dims_L5_two_one`: the sector dimensions quoted
  with the sector-counting figure of the paper: 10920, 3360 and 120 states with 0, 1
  and 2 doublons for two up and two down electrons on the 4 × 4 lattice, and 6900 and
  600 states with 0 and 1 doublon for two up and one down electron on the 5 × 5
  lattice.

## Not covered

This file counts basis states only. It says nothing about the energies of the sectors
or about their separation at large `U`.
-/

@[expose] public section

namespace HubbardMoments

open Finset

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- The `k`-doublon sector has `C(N, a) · C(a, k) · C(N - a, b - k)` states. -/
theorem card_sector (a b k : ℕ) (hkb : k ≤ b) :
    (sector V a b k).card =
      (Fintype.card V).choose a * a.choose k * (Fintype.card V - a).choose (b - k) := by
  calc (sector V a b k).card
      = ∑ u ∈ powersetCard a (univ : Finset V),
          ((powersetCard b univ).filter (fun d => (u ∩ d).card = k)).card := by
        rw [sector, card_filter, sum_product]
        refine sum_congr rfl fun u _ => ?_
        rw [card_filter]
    _ = ∑ _u ∈ powersetCard a (univ : Finset V),
          a.choose k * (Fintype.card V - a).choose (b - k) := by
        refine sum_congr rfl fun u hu => ?_
        rw [mem_powersetCard] at hu
        rw [card_trace_card_eq u b k hkb, hu.2]
    _ = (Fintype.card V).choose a * a.choose k * (Fintype.card V - a).choose (b - k) := by
        rw [sum_const, card_powersetCard, card_univ, smul_eq_mul, mul_assoc]

/-- The same count in the order "doublons, then single up electrons, then single down
electrons": `C(N, k) · C(N - k, a - k) · C(N - a, b - k)`. -/
theorem card_sector' (a b k : ℕ) (hka : k ≤ a) (hkb : k ≤ b) :
    (sector V a b k).card =
      (Fintype.card V).choose k * (Fintype.card V - k).choose (a - k) *
        (Fintype.card V - a).choose (b - k) := by
  rw [card_sector V a b k hkb, Nat.choose_mul hka]

/-- Two up and two down electrons on the 4 × 4 lattice: 10920, 3360 and 120 states
with 0, 1 and 2 doublons. -/
theorem sector_dims_L4_two_two :
    (sector (Fin 4 × Fin 4) 2 2 0).card = 10920 ∧
      (sector (Fin 4 × Fin 4) 2 2 1).card = 3360 ∧
      (sector (Fin 4 × Fin 4) 2 2 2).card = 120 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [card_sector _ _ _ _ (by norm_num), Fintype.card_prod, Fintype.card_fin] <;>
    decide

/-- Two up and one down electron on the 5 × 5 lattice: 6900 and 600 states with 0 and
1 doublon. -/
theorem sector_dims_L5_two_one :
    (sector (Fin 5 × Fin 5) 2 1 0).card = 6900 ∧
      (sector (Fin 5 × Fin 5) 2 1 1).card = 600 := by
  refine ⟨?_, ?_⟩ <;>
    rw [card_sector _ _ _ _ (by norm_num), Fintype.card_prod, Fintype.card_fin] <;>
    decide

end HubbardMoments

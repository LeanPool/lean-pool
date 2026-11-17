/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# The block family of an integer packing

Given multiplicities `k S : ℕ` (`S : Finset ι`), the block family is indexed by
`Σ S : Finset ι, Fin (k S)` with block map `b ↦ b.1`: the set `S` occurs `k S` times.
It is the list of blocks used in the proof of the packing bound (Lemma 6.5 of the paper).

* `card_blocks` : the number of blocks containing `i` is `∑_{S ∋ i} k S`;
* `sum_blocks`  : a sum over the family of a function of the block is `∑_S k S * g S`.
-/

@[expose] public section

namespace AaronsonAmbainis.Pack

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The number of blocks of the family `Σ S, Fin (k S)` which contain `i`. -/
theorem card_blocks (k : Finset ι → ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin (k S)) => i ∈ b.1).card
      = ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), k S := by
  rw [Finset.card_filter, Fintype.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : i ∈ S
  · simp [h]
  · simp [h]

omit [DecidableEq ι] in
/-- A sum over the family `Σ S, Fin (k S)` of a function of the block. -/
theorem sum_blocks (k : Finset ι → ℕ) (g : Finset ι → ℝ) :
    ∑ b : (Σ S : Finset ι, Fin (k S)), g b.1 = ∑ S, (k S : ℝ) * g S := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  change ∑ _y : Fin (k S), g S = (k S : ℝ) * g S
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end AaronsonAmbainis.Pack

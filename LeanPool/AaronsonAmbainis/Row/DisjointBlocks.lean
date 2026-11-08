/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.NormNum
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# Pairwise disjoint blocks, and the sensitivity at every point

For pairwise disjoint blocks the block inequality (`BlockInequality`, Lemma 6.4 of the paper)
applies with `N = 1` and `m = 1`, where `1 - cos (π / 1) = 2`, and gives the bound `4 d²`
(`Row.disjoint_blocks_of_block`). For the blocks `{j}` this is the sensitivity bound at every
point (Corollary 6.10 of the paper), `∑_j |f(x) - f(x^j)| ≤ 4 d²`
(`sensitivity_of_block : BlockInequality → SensitivityBound`).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

namespace Row

/-- For pairwise disjoint blocks `S b`, `∑_b |f(x) - f(x^{S b})| ≤ 4 d²`. -/
theorem disjoint_blocks_of_block (hBlock : BlockInequality) (ι : Type) [Fintype ι]
    [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d)
    (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι)
    (hS : ∀ b b' : β, b ≠ b' → Disjoint (S b) (S b')) :
    ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 := by
  have hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ 1 := by
    intro i
    rw [Finset.card_le_one]
    intro b hb b' hb'
    by_contra hne
    exact Finset.disjoint_left.mp (hS b b' hne) (Finset.mem_filter.mp hb).2
      (Finset.mem_filter.mp hb').2
  have hc : ((1 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((1 : ℕ) : ℝ))) ≤ 2 := by
    rw [Nat.cast_one, div_one, Real.cos_pi]
    norm_num
  have h := hBlock ι d f hf hdeg x β S 1 1 Nat.one_pos hN hc
  simpa using h

end Row

/-- The sensitivity bound at every point (Corollary 6.10 of the paper), from the block inequality
(Lemma 6.4): the blocks `{j}` are pairwise disjoint. -/
theorem sensitivity_of_block : BlockInequality → SensitivityBound := by
  intro hBlock ι _ _ d f hf hdeg x
  exact Row.disjoint_blocks_of_block hBlock ι d f hf hdeg x ι (fun j => {j})
    (fun b b' hne => Finset.disjoint_singleton.mpr hne)

end AaronsonAmbainis

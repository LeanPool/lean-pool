/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Ring.Basic
public import LeanPool.AaronsonAmbainis.Average.Coordinate
public import LeanPool.AaronsonAmbainis.Level.Basic

/-!
# Averaging over a set of coordinates

`exists_avg_set` (Lemma 8.2 of the paper): let `f` have a row of cost at most `K` at every
point, and let `R` be a set of coordinates. Averaging `f` over the coordinates of `R`, one after
the other, gives a function `g` with rows of cost at most `K` such that

* `Var f ≤ Var g + ∑_{j ∈ R} Inf_j f`,
* `Inf_k g ≤ Inf_k f` and `L_k g ≤ L_k f` for every coordinate `k`,
* `L_j g = 0` for `j ∈ R`.

(`g` is the average of `f` over the coordinates in `R`, that is, the conditional expectation of
`f` given the coordinates outside `R`; only the listed properties are used, so the function is
not named.) Induction on `R` with the lemmas of `Coordinate.lean`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Average

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Averaging over the coordinates of a set `R` (Lemma 8.2 of the paper): a function `g` with
rows of the same cost, with `Var f ≤ Var g + ∑_{j ∈ R} Inf_j f`, with influences and mean
absolute increments not larger than those of `f`, and with `L_j g = 0` for `j ∈ R`. -/
theorem exists_avg_set (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ} (ha : ∀ x i, 0 ≤ a x i)
    (hsum : ∀ x, ∑ i, a x i ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (R : Finset ι) :
    ∃ (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ),
      (∀ x i, 0 ≤ b x i) ∧ (∀ x, ∑ i, b x i ≤ K) ∧
      (∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) ∧
      variance f ≤ variance g + ∑ j ∈ R, inflR f j ∧
      (∀ k, inflR g k ≤ inflR f k) ∧ (∀ k, meanAbsIncr g k ≤ meanAbsIncr f k) ∧
      (∀ j ∈ R, meanAbsIncr g j = 0) := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨f, a, ha, hsum, hrow, ?_, fun k => le_refl _, fun k => le_refl _,
      fun j hj => absurd hj (Finset.notMem_empty j)⟩
    rw [Finset.sum_empty, add_zero]
  | insert j R hjR ih =>
    obtain ⟨g, b, hb0, hbK, hbrow, hvar, hR2, hL1, hzero⟩ := ih
    obtain ⟨hb0', hbK', hbrow'⟩ := rows_avg j hb0 hbK hbrow
    refine ⟨avg j g, fun x i => (b x i + b (flipSet x {j}) i) / 2, hb0', hbK', hbrow',
      ?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_insert hjR]
      have h1 := variance_avg j g
      have h2 := hR2 j
      linarith
    · intro k
      exact le_trans (inflR_avg_le j k g) (hR2 k)
    · intro k
      exact le_trans (meanAbsIncr_avg_le j k g) (hL1 k)
    · intro i hi
      rcases Finset.mem_insert.mp hi with h | hiR
      · rw [h]
        exact meanAbsIncr_avg_self j g
      · exact le_antisymm (le_trans (meanAbsIncr_avg_le j i g) (le_of_eq (hzero i hiR)))
          (Level.meanAbsIncr_nonneg _ _)

end Average
end AaronsonAmbainis

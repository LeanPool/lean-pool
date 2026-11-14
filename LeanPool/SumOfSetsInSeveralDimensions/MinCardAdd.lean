/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim
public import LeanPool.SumOfSetsInSeveralDimensions.LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import LeanPool.SumOfSetsInSeveralDimensions.AffineDimSumset
import LeanPool.SumOfSetsInSeveralDimensions.Construction
import LeanPool.SumOfSetsInSeveralDimensions.LowerBound

/-!
# The least size of a sumset in `ℝ^d`

Ruzsa's paper defines `F_d(m, n)` as the least `|A + B|` over sets `A, B ⊆ ℝ^d` with `|A| = m`,
`|B| = n` and `A + B` of affine dimension `d`, and `F'_d(m, n)` as the same minimum with `B` of
affine dimension `d` instead. Theorem 2 of the paper states that `F_d(m, n) = F'_d(m, n) =
G_d(m, n)` for `1 ≤ m ≤ n`, unless `n < d + 1` or `m ≤ n - m ≤ d`. The sets of Section 3 attain
`G_d(m, n)` for all `1 ≤ m ≤ n` with `d + 1 ≤ n`, so the equalities hold for these pairs, which
include those excluded by the second condition.

## Main definitions

* `minCardAdd d m n`: the function `F_d(m, n)`.
* `minCardAddOfDimRight d m n`: the function `F'_d(m, n)`.

## Main statements

* `minCardAdd_eq_sumsetCardLowerBound`, `minCardAddOfDimRight_eq_sumsetCardLowerBound`: Theorem 2.
* `sInf_card_add_eq_add_sum_min`, `sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min`:
  Theorem 2 with `F_d`, `F'_d` and `G_d` unfolded and the affine dimension written as the
  dimension of the span of the differences.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

/-- `F_d(m, n)`: the least size of `A + B` for `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `A + B`
of affine dimension `d`. -/
noncomputable def minCardAdd (d m n : ℕ) : ℕ :=
  sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ (A + B).affineDim = d ∧
    #(A + B) = k}

/-- `F'_d(m, n)`: the least size of `A + B` for `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `B`
of affine dimension `d`. -/
noncomputable def minCardAddOfDimRight (d m n : ℕ) : ℕ :=
  sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ B.affineDim = d ∧ #(A + B) = k}

variable {d m n : ℕ}

private lemma sumsetCardLowerBound_le_card_add {A B : Finset (Fin d → ℝ)} (hm : 1 ≤ m)
    (hmn : m ≤ n) (hA : #A = m) (hB : #B = n) (hdim : (A + B).affineDim = d) :
    sumsetCardLowerBound d m n ≤ #(A + B) := by
  have h := card_add_sum_min_le_card_add (d := d) (A := B) (B := A) (card_pos.1 (by grind))
    (by grind) (by rwa [add_comm])
  rwa [add_comm B, hA, hB, ← sumsetCardLowerBound_eq] at h

/-- **Theorem 2 of Ruzsa, for `F_d`.** For `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`,
`F_d(m, n) = G_d(m, n)`. -/
theorem minCardAdd_eq_sumsetCardLowerBound (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) : minCardAdd d m n = sumsetCardLowerBound d m n := by
  obtain ⟨A, B, hA, hB, hBdim, hAB⟩ := exists_card_add_eq_sumsetCardLowerBound hd hm hmn hn
  have hdim : (A + B).affineDim = d := by
    rw [add_comm]
    exact affineDim_add_eq_of_left_eq (card_pos.1 (by grind)) hBdim
  refine le_antisymm (Nat.sInf_le ⟨A, B, hA, hB, hdim, hAB⟩)
    (le_csInf ⟨_, A, B, hA, hB, hdim, rfl⟩ ?_)
  rintro k ⟨A', B', hA', hB', hdim', rfl⟩
  exact sumsetCardLowerBound_le_card_add hm hmn hA' hB' hdim'

/-- **Theorem 2 of Ruzsa, for `F'_d`.** For `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`,
`F'_d(m, n) = G_d(m, n)`. -/
theorem minCardAddOfDimRight_eq_sumsetCardLowerBound (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) : minCardAddOfDimRight d m n = sumsetCardLowerBound d m n := by
  obtain ⟨A, B, hA, hB, hBdim, hAB⟩ := exists_card_add_eq_sumsetCardLowerBound hd hm hmn hn
  refine le_antisymm (Nat.sInf_le ⟨A, B, hA, hB, hBdim, hAB⟩)
    (le_csInf ⟨_, A, B, hA, hB, hBdim, rfl⟩ ?_)
  rintro k ⟨A', B', hA', hB', hBdim', rfl⟩
  refine sumsetCardLowerBound_le_card_add hm hmn hA' hB' ?_
  rw [add_comm]
  exact affineDim_add_eq_of_left_eq (card_pos.1 (by grind)) hBdim'

/-- Theorem 2 of Ruzsa for `F_d`, with `F_d` and `G_d` unfolded and the affine dimension of
`A + B` written as the dimension of the span of `(A + B) - (A + B)`. -/
theorem sInf_card_add_eq_add_sum_min (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin d → ℝ))) = d ∧
      #(A + B) = k} = n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) := by
  simp_rw [← affineDim_eq_finrank_span_sub, ← sumsetCardLowerBound_eq]
  exact minCardAdd_eq_sumsetCardLowerBound hd hm hmn hn

/-- Theorem 2 of Ruzsa for `F'_d`, with `F'_d` and `G_d` unfolded and the affine dimension of `B`
written as the dimension of the span of `B - B`. -/
theorem sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑B - ↑B : Set (Fin d → ℝ))) = d ∧ #(A + B) = k} =
      n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) := by
  simp_rw [← affineDim_eq_finrank_span_sub, ← sumsetCardLowerBound_eq]
  exact minCardAddOfDimRight_eq_sumsetCardLowerBound hd hm hmn hn

end SumOfSetsInSeveralDimensions

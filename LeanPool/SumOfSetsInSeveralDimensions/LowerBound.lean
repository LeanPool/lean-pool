/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import LeanPool.SumOfSetsInSeveralDimensions.GeometricDeletion
import LeanPool.SumOfSetsInSeveralDimensions.LowerBoundFunction
import LeanPool.SumOfSetsInSeveralDimensions.Normalize
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sum of sets in several dimensions

Theorem 1 of Ruzsa, *Sum of sets in several dimensions*, Combinatorica 14 (1994): if
`A, B ⊆ ℝ^D` are finite sets with `B` nonempty and `|B| ≤ |A|`, and `A + B` has affine dimension
`d`, then `|A + B| ≥ |A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t)`.

The proof is by induction on `|A| + |B|`. Both sets are translated so that their
lexicographically least element is `0`. If `|B| ≥ 2`, the lemma `geometric_deletion_cases` removes
`0` from one or both of the sets, and the inequalities of `LowerBoundFunction.lean` compare the
bound for the smaller sets with the bound for `A` and `B`.

## Main statements

* `card_add_sum_min_le_card_add`: Ruzsa's theorem.
* `card_add_sum_min_le_card_add_of_le`: the same bound for every `d` at most the affine dimension
  of `A + B`.
* `card_add_sum_min_le_card_add_of_finrank_span_sub_eq`: Ruzsa's theorem, with the affine
  dimension written as the dimension of the span of `(A + B) - (A + B)`.
-/

public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

/-- The inductive step for sets `X` and `Y` that contain `0` and whose other elements are
lexicographically positive, given the bound for all pairs of sets with fewer points. -/
private lemma sumsetCardLowerBound_le_card_add_of_zero_mem {D d : ℕ} {X Y : Finset (Fin D → ℝ)}
    (ih : ∀ {e m n : ℕ} {X' Y' : Finset (Fin D → ℝ)}, #X' = m → #Y' = n →
      m + n < #X + #Y → 1 ≤ m → m ≤ n → (X' + Y').affineDim = e →
      sumsetCardLowerBound e m n ≤ #(X' + Y'))
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y) (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) (hX : 2 ≤ #X) (hXY : #X ≤ #Y)
    (hdim : (X + Y).affineDim = d) :
    sumsetCardLowerBound d #X #Y ≤ #(X + Y) := by
  obtain ⟨hd, hcard⟩ | ⟨hd, hcard⟩ | ⟨hd, hcard⟩ | ⟨hd, hcard⟩ :=
    geometric_deletion_cases h0X h0Y hposX hposY hX (hX.trans hXY) hdim
  · refine sumsetCardLowerBound_of_full_case hX ?_ hcard
    exact ih (card_erase_of_mem h0X) (card_erase_of_mem h0Y) (by grind) (by grind) (by grind) hd
  · refine sumsetCardLowerBound_of_large_case hX hXY ?_ hcard
    exact ih (card_erase_of_mem h0X) (card_erase_of_mem h0Y) (by grind) (by grind) (by grind) hd
  · refine sumsetCardLowerBound_of_small_case hX hXY ?_ hcard
    exact ih (card_erase_of_mem h0X) rfl (by grind) (by grind) (by grind) hd
  obtain hXY | hXY := hXY.eq_or_lt
  · rw [add_comm X (Y.erase 0)] at hd hcard
    rw [← hXY]
    refine sumsetCardLowerBound_of_equal_right_case hX ?_ hcard
    exact ih (by grind [card_erase_of_mem h0Y]) rfl (by grind) (by grind) (by grind) hd
  · refine sumsetCardLowerBound_of_strict_right_case (by grind) hXY ?_ hcard
    exact ih rfl (card_erase_of_mem h0Y) (by grind) (by grind) (by grind) hd

private lemma sumsetCardLowerBound_le_card_add {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : (A + B).affineDim = d) :
    sumsetCardLowerBound d #B #A ≤ #(A + B) := by
  generalize hn : #A + #B = n
  induction n using Nat.strong_induction_on generalizing d A B with
  | _ n ih =>
  obtain hB1 | hB2 : #B = 1 ∨ 2 ≤ #B := by grind [hB.card_pos]
  · rw [sumsetCardLowerBound_eq, hB1]
    simpa using card_le_card_add_right hB
  have hA : A.Nonempty := card_pos.1 (by grind)
  rw [← normalize_add_card hA hB, ← normalize_card hB, ← normalize_card hA, add_comm]
  refine sumsetCardLowerBound_le_card_add_of_zero_mem ?_ (zero_mem_normalize hB)
    (zero_mem_normalize hA) (fun x hx hx0 ↦ normalize_pos_of_ne_zero hB hx hx0)
    (fun y hy hy0 ↦ normalize_pos_of_ne_zero hA hy hy0) (by simpa [normalize_card] using hB2)
    (by simpa [normalize_card] using hBA) (by rwa [add_comm, normalize_add_dim])
  rintro e m k X Y rfl rfl hlt hm hmk hdim'
  rw [add_comm X] at hdim' ⊢
  exact ih _ (by grind [normalize_card hA, normalize_card hB]) (card_pos.1 hm) hmk hdim' rfl

/-- **Ruzsa's theorem.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty, `|B| ≤ |A|` and `A + B` has
affine dimension `d`, then `|A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t) ≤ |A + B|`. -/
theorem card_add_sum_min_le_card_add {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : (A + B).affineDim = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by
  rw [← sumsetCardLowerBound_eq]
  exact sumsetCardLowerBound_le_card_add hB hBA hdim

/-- Ruzsa's theorem for every `d` at most the affine dimension of `A + B`. -/
lemma card_add_sum_min_le_card_add_of_le {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hd : d ≤ (A + B).affineDim) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by
  refine le_trans ?_ (card_add_sum_min_le_card_add hB hBA rfl)
  gcongr

/-- Ruzsa's theorem, with the affine dimension of `A + B` written as the dimension of the span of
`(A + B) - (A + B)`. -/
theorem card_add_sum_min_le_card_add_of_finrank_span_sub_eq {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add hB hBA ((affineDim_eq_finrank_span_sub _).trans hdim)

end SumOfSetsInSeveralDimensions

/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import LeanPool.AaronsonAmbainis.DetLow.Main

/-!
# DetLow: two corollaries of `lowestBound`

Neither of them is used in the proof of `DetInequality`.

* `exists_lowest_le_bdry` — `LowestBound` is not vacuous: the determinant of the agreement
  matrix has a monomial of least total degree, and its exponent in each variable `j` is at
  most `bdry g j`.
* `exists_monomial_weight_le` — a weighted form: for nonnegative lengths `ℓ`, the determinant
  has a monomial of `ℓ`-weight at most `∑ j, ℓ j * bdry g j`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

theorem exists_lowest_le_bdry {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) :
    ∃ m : ι →₀ ℕ, IsLowest (agMatrix g).det m ∧ ∀ j, m j ≤ bdry g j := by
  obtain ⟨hne, hb⟩ := lowestBound ι g
  obtain ⟨m, hm⟩ := exists_isLowest _ hne
  exact ⟨m, hm, hb m hm⟩

theorem exists_monomial_weight_le {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool)
    (ℓ : ι → ℝ) (hℓ : ∀ j, 0 ≤ ℓ j) :
    ∃ m ∈ (agMatrix g).det.support,
      ∑ j, ℓ j * (m j : ℝ) ≤ ∑ j, ℓ j * (bdry g j : ℝ) := by
  obtain ⟨m, hm, hb⟩ := exists_lowest_le_bdry g
  refine ⟨m, hm.1, Finset.sum_le_sum fun j _ => ?_⟩
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb j) (hℓ j)

end DetLow
end AaronsonAmbainis

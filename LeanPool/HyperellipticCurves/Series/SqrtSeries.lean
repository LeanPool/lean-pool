/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Square roots of formal power series

Over any commutative ring `O`, a power series `c : O⟦X⟧` whose constant coefficient is a square
`a₀²` with `2a₀` a unit has a square root: `ChabautyColeman.sqrtSeries c a₀ v` (with `v` a chosen
inverse of `2a₀`) satisfies `(sqrtSeries c a₀ v)² = c` and has constant coefficient `a₀`
(`ChabautyColeman.sqrtSeries_sq`, `ChabautyColeman.constantCoeff_sqrtSeries`). The construction is
the coefficient recursion `aₙ = (cₙ - ∑_{0<i,j,\ i+j=n} aᵢaⱼ)/(2a₀)`; no completeness is needed.

`ChabautyColeman.exists_sqrtSeries` packages the existence statement for use over a local ring of
residue characteristic `≠ 2` (`lem:sqrt-series`).

## Main definitions

* `ChabautyColeman.sqrtSeries`: the formal square root with prescribed constant coefficient.

## Main statements

* `ChabautyColeman.sqrtSeries_sq`: `(sqrtSeries c a₀ v)² = c` when `a₀² = c(0)` and `2a₀·v = 1`.
* `ChabautyColeman.exists_sqrtSeries`: existence of a square root when `2a₀` is a unit.

Blueprint node: `lem:sqrt-series`.
-/

@[expose] public section

open PowerSeries Finset

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

/-- Coefficients of the formal square root, by strong recursion: `a₀` at `0`, and
`aₙ = (cₙ - ∑_{0<i,j,\ i+j=n} aᵢaⱼ) · v` for `n ≥ 1` (with `v` an inverse of `2a₀`). -/
noncomputable def sqrtAux (c : O⟦X⟧) (a₀ v : O) : ℕ → O
  | n =>
    if n = 0 then a₀
    else
      (coeff n c - ∑ x ∈ antidiagonal n,
        if _ : x.1 < n ∧ x.2 < n then sqrtAux c a₀ v x.1 * sqrtAux c a₀ v x.2 else 0) * v
  termination_by n => n
  decreasing_by · exact ‹_ ∧ _›.1
                · exact ‹_ ∧ _›.2

theorem sqrtAux_zero (c : O⟦X⟧) (a₀ v : O) : sqrtAux c a₀ v 0 = a₀ := by rw [sqrtAux]; simp

theorem sqrtAux_succ (c : O⟦X⟧) (a₀ v : O) (n : ℕ) :
    sqrtAux c a₀ v (n + 1) =
      (coeff (n + 1) c - ∑ x ∈ antidiagonal (n + 1),
        if _ : x.1 < n + 1 ∧ x.2 < n + 1 then
          sqrtAux c a₀ v x.1 * sqrtAux c a₀ v x.2 else 0) * v := by
  rw [sqrtAux, ite_eq_right (Nat.succ_ne_zero n)]

/-- The formal square root of `c`, with prescribed constant coefficient `a₀` (a square root of
`c(0)`) and `v` an inverse of `2a₀`. Correct when `a₀² = c(0)` and `2a₀·v = 1`
(`sqrtSeries_sq`). -/
noncomputable def sqrtSeries (c : O⟦X⟧) (a₀ v : O) : O⟦X⟧ := PowerSeries.mk (sqrtAux c a₀ v)

@[simp] theorem coeff_sqrtSeries (c : O⟦X⟧) (a₀ v : O) (n : ℕ) :
    coeff n (sqrtSeries c a₀ v) = sqrtAux c a₀ v n := coeff_mk n _

@[simp] theorem constantCoeff_sqrtSeries (c : O⟦X⟧) (a₀ v : O) :
    constantCoeff (sqrtSeries c a₀ v) = a₀ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_sqrtSeries, sqrtAux_zero]

theorem sqrtSeries_sq (c : O⟦X⟧) {a₀ v : O} (ha : a₀ ^ 2 = constantCoeff c)
    (hv : 2 * a₀ * v = 1) : (sqrtSeries c a₀ v) ^ 2 = c := by
  ext n
  rw [pow_two, coeff_mul]
  simp only [coeff_sqrtSeries]
  obtain _ | m := n
  · rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp only [sqrtAux_zero, coeff_zero_eq_constantCoeff_apply]
    rw [← pow_two, ha]
  · have hfilter : (antidiagonal (m + 1)).filter (fun x ↦ ¬(x.1 < m + 1 ∧ x.2 < m + 1))
        = {((0 : ℕ), m + 1), (m + 1, (0 : ℕ))} := by
      ext x
      simp only [Finset.mem_filter, mem_antidiagonal, Finset.mem_insert, Finset.mem_singleton,
        Prod.ext_iff]
      lia
    set S := ∑ x ∈ (antidiagonal (m + 1)).filter (fun x ↦ x.1 < m + 1 ∧ x.2 < m + 1),
        sqrtAux c a₀ v x.1 * sqrtAux c a₀ v x.2 with hS_def
    have ham : sqrtAux c a₀ v (m + 1) = (coeff (m + 1) c - S) * v := by
      rw [sqrtAux_succ, hS_def]
      simp only [dite_eq_ite]
      rw [Finset.sum_filter]
    have hfull : ∑ x ∈ antidiagonal (m + 1), sqrtAux c a₀ v x.1 * sqrtAux c a₀ v x.2
        = S + (sqrtAux c a₀ v 0 * sqrtAux c a₀ v (m + 1)
              + sqrtAux c a₀ v (m + 1) * sqrtAux c a₀ v 0) := by
      rw [hS_def, ← Finset.sum_filter_add_sum_filter_not (antidiagonal (m + 1))
            (fun x ↦ x.1 < m + 1 ∧ x.2 < m + 1), hfilter, Finset.sum_pair (by simp)]
    rw [hfull, sqrtAux_zero, ham]
    linear_combination (coeff (m + 1) c - S) * hv

/-- **Square-root series** (`lem:sqrt-series`). If `a₀² = c(0)` and `2a₀` is a unit (e.g. `O`
local with residue characteristic `≠ 2` and `c(0)` a unit square), there is a power series `η`
with `η² = c` and prescribed constant coefficient `a₀`. -/
theorem exists_sqrtSeries {c : O⟦X⟧} {a₀ : O} (ha : a₀ ^ 2 = constantCoeff c)
    (hu : IsUnit (2 * a₀)) : ∃ η : O⟦X⟧, η ^ 2 = c ∧ constantCoeff η = a₀ :=
  ⟨sqrtSeries c a₀ (Ring.inverse (2 * a₀)),
    sqrtSeries_sq c ha (Ring.mul_inverse_cancel _ hu),
    constantCoeff_sqrtSeries c a₀ _⟩

end ChabautyColeman

end

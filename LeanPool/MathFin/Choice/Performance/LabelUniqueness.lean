/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-!
# Per-observation uniqueness bound for overlapping-label samples

López de Prado (*Advances in Financial Machine Learning*, ch. 4) measures how
much an overlapping-label observation `i` (with span `[t0 i, t1 i]`) overlaps
its peers via the concurrency `c_t = Σᵢ 1[t ∈ [t0 i, t1 i]]` and the
per-observation uniqueness `u_{t,i} = 1[t ∈ span i] / c_t`.

This file states both over a finite index type `ι` and proves the basic bound
used to justify uniqueness-weighted sampling: whenever `i`'s span actually
contains `t`, `u_{t,i} ∈ (0, 1]`. The average uniqueness of observation `i` (the
mean of `u_{t,i}` over `i`'s span) is not defined here.

## Main definitions

* `concurrency`: the number of observations whose span `[t0 i, t1 i]` contains `t`.
* `uniqueness`: the per-observation uniqueness at `t`, `1 / c_t` if the span of `i` contains `t`
  and `0` otherwise.

## Main results

* `concurrency_pos`: `c_t > 0` whenever some span contains `t`.
* `uniqueness_mem_Ioc`: `u_{t,i} ∈ (0, 1]` whenever `t ∈ span i`.
* `concurrency_sumElim`: the concurrency of a pooled sample `ι ⊕ κ` is the sum of the two
  samples' concurrencies (used by `Choice/Performance/PurgedCV.lean`).

## Tags

overlapping labels, sample uniqueness, concurrency, López de Prado, sample weights, MSC 62M10,
JEL C58
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} [Fintype ι]

/-- Concurrency at time `t`: the number of observations whose span
`[t0 i, t1 i]` contains `t`. -/
noncomputable def concurrency (t0 t1 : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if t ∈ Set.Icc (t0 i) (t1 i) then (1 : ℝ) else 0

/-- Per-observation uniqueness at time `t`: `1 / c_t` if `i`'s span contains
`t`, else `0`. -/
noncomputable def uniqueness (t0 t1 : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  (if t ∈ Set.Icc (t0 i) (t1 i) then (1 : ℝ) else 0) / concurrency t0 t1 t

theorem one_le_concurrency (t0 t1 : ι → ℝ) {t : ℝ} {i : ι}
    (hi : t ∈ Set.Icc (t0 i) (t1 i)) : 1 ≤ concurrency t0 t1 t := by
  have h := Finset.single_le_sum
    (f := fun j ↦ if t ∈ Set.Icc (t0 j) (t1 j) then (1 : ℝ) else 0)
    (fun j _ ↦ by split <;> norm_num) (Finset.mem_univ i)
  rwa [ite_eq_left hi] at h

theorem concurrency_pos (t0 t1 : ι → ℝ) {t : ℝ} {i : ι}
    (hi : t ∈ Set.Icc (t0 i) (t1 i)) : 0 < concurrency t0 t1 t :=
  zero_lt_one.trans_le (one_le_concurrency t0 t1 hi)

/-- The headline bound: an observation whose span contains `t` has uniqueness
strictly positive and at most `1`. -/
theorem uniqueness_mem_Ioc (t0 t1 : ι → ℝ) {t : ℝ} {i : ι}
    (hi : t ∈ Set.Icc (t0 i) (t1 i)) : uniqueness t0 t1 t i ∈ Set.Ioc (0 : ℝ) 1 := by
  have hpos := concurrency_pos t0 t1 hi
  refine ⟨?_, ?_⟩
  · rw [uniqueness, ite_eq_left hi]
    exact div_pos one_pos hpos
  · rw [uniqueness, ite_eq_left hi, div_le_one hpos]
    exact one_le_concurrency t0 t1 hi

/-- **Concurrency of a pooled sample**: the labels of `ι ⊕ κ` active at `t` are those of `ι`
and those of `κ`, so the concurrencies add. -/
theorem concurrency_sumElim {κ : Type*} [Fintype κ] (t0 t1 : ι → ℝ) (t0' t1' : κ → ℝ)
    (t : ℝ) :
    concurrency (Sum.elim t0 t0') (Sum.elim t1 t1') t =
      concurrency t0 t1 t + concurrency t0' t1' t := by
  unfold concurrency
  rw [Fintype.sum_sum_type]
  rfl

end MathFin

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The uniform partition of `[0, T]`

The library's one equipartition: `unifPart T n k = (k/n)·T`, the `k`-th of the `n + 1` nodes
`0 = t₀ ≤ … ≤ tₙ = T` that cut `[0, T]` into `n` cells of length `T/n`. Every Riemann sum,
Riemann–Stieltjes sum and quadratic-variation sum of the Itô stack runs along it, so the
facts about it are proved here once: monotone, `≤ T`, endpoints, cell length, the telescoping
`∑ (t_{k+1} − t_k) = T`.

`unifPartIcc s t` is the same partition of `[s, t]`, shifted to start at `s`.

## Main definitions

* `unifPart`: the uniform partition of `[0, T]` into `n` cells, `unifPart T n k = (k/n)·T`.
* `unifPartIcc`: the uniform partition of `[s, t]` into `n` cells, `unifPart (t − s) n k` shifted
  to start at `s`.

## Main results

* `unifPart_mono`, `unifPart_le_T`, `unifPart_zero`, `unifPart_self` — monotone, bounded by
  `T`, and the endpoints `0` and `T`.
* `unifPart_succ_sub`, `unifPart_mesh_sum` — every cell has length `T/n`, and the lengths
  telescope to `T`.
* `tendsto_inv_sqrt_nat_add`, `one_div_sqrt_le_two` — the `1/√n` mesh rate of the `O(√mesh)`
  bounds: a null sequence, and the shift comparison `1/√n ≤ 2/√(n+1)`.

## Tags

uniform partition, equipartition, mesh size, Riemann sum grid, time discretisation, MSC 60H05
-/

@[expose] public section

namespace MathFin

open Filter Topology
open scoped NNReal

/-- The uniform partition of `[0, T]`: the `n`-th refinement places its `k`-th node at `kT/n`. -/
noncomputable def unifPart (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (n : ℝ≥0) * T

@[simp] lemma unifPart_zero (T : ℝ≥0) (n : ℕ) : unifPart T n 0 = 0 := by simp [unifPart]

/-- The last node of the uniform partition into `n ≠ 0` cells is `T`. -/
lemma unifPart_self (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : unifPart T n n = T := by
  have hn0 : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp [unifPart, hn0]

/-- The partition points `unifPart T n = (k/n)·T` are monotone in `k`. -/
lemma unifPart_mono (T : ℝ≥0) (n : ℕ) : Monotone (unifPart T n) :=
  fun _ _ hab ↦ by unfold unifPart; gcongr

/-- A partition point `unifPart T n j ≤ T` whenever `j ≤ n`. -/
lemma unifPart_le_T {T : ℝ≥0} {n j : ℕ} (hj : j ≤ n) : unifPart T n j ≤ T := by
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl := Nat.le_zero.1 hj; simp
  · exact (unifPart_mono T n hj).trans_eq (unifPart_self T hn)

/-- The cells of the uniform partition have length `T/n`. -/
lemma unifPart_succ_sub (T : ℝ≥0) (n k : ℕ) :
    ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n := by
  push_cast [unifPart]
  ring

/-- The uniform-partition mesh telescopes: `∑_{k<n} (t_{k+1} − t_k) = T` for `n ≠ 0`. -/
lemma unifPart_mesh_sum (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) := by
  rw [Finset.sum_range_sub (fun k ↦ (unifPart T n k : ℝ)), unifPart_self T hn, unifPart_zero]
  simp

/-! ### The uniform partition of `[s, t]` -/

/-- The uniform partition of `[s, t]` into `n` cells: the library's `unifPart` of `[0, t − s]`,
shifted to start at `s`. -/
noncomputable def unifPartIcc (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 := s + unifPart (t - s) n k

lemma unifPartIcc_mono (s t : ℝ≥0) (n : ℕ) : Monotone (unifPartIcc s t n) :=
  fun _ _ hij ↦ by unfold unifPartIcc; gcongr; exact unifPart_mono _ n hij

lemma unifPartIcc_zero (s t : ℝ≥0) (n : ℕ) : unifPartIcc s t n 0 = s := by
  simp [unifPartIcc]

lemma unifPartIcc_self {s t : ℝ≥0} (hst : s ≤ t) {n : ℕ} (hn : n ≠ 0) :
    unifPartIcc s t n n = t := by
  rw [unifPartIcc, unifPart_self _ hn, add_tsub_cancel_of_le hst]

lemma unifPartIcc_succ_sub {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) :
    ((unifPartIcc s t n (k + 1) : ℝ) - unifPartIcc s t n k) = ((t : ℝ) - s) / n := by
  rw [unifPartIcc, unifPartIcc, NNReal.coe_add, NNReal.coe_add, add_sub_add_left_eq_sub,
    unifPart_succ_sub, NNReal.coe_sub hst]

/-! ### The `1/√n` rate -/

/-- The `1/√(n+1)` null sequence over the naturals: the square root of Mathlib's
`tendsto_one_div_add_atTop_nhds_zero_nat`. -/
theorem tendsto_inv_sqrt_nat_add :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt

/-- The `1/√n ≤ 2/√(n+1)` comparison for `n ≥ 1`. -/
theorem one_div_sqrt_le_two {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / Real.sqrt ((n : ℝ)) ≤ 2 / Real.sqrt (((n : ℝ)) + 1) := by
  have hne : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos1 : (0 : ℝ) < Real.sqrt ((n : ℝ)) := Real.sqrt_pos.mpr hne
  have hpos2 : (0 : ℝ) < Real.sqrt (((n : ℝ)) + 1) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (((n : ℝ)) + 1) ≤ 2 * Real.sqrt ((n : ℝ)) := by
    have hnm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    refine le_trans (Real.sqrt_le_sqrt (show ((n : ℝ)) + 1 ≤ 4 * (n : ℝ) from by nlinarith)) ?_
    rw [show (2 : ℝ) * Real.sqrt ((n : ℝ)) = Real.sqrt (4 * (n : ℝ)) from by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num]
  rw [div_le_div_iff₀ hpos1 hpos2]
  simpa using hsq

end MathFin

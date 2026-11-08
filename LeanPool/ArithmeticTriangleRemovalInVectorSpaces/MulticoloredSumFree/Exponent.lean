/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The exponents `c p` and `C p`, and the thresholds of Theorem 1

The exponent `c p` of Kleinberg, Sawin and Speyer is defined by
`p ^ (1 - c p) = ⨅ x : Set.Ioo 0 1, x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j`. A multicolored
sum-free family in `Fin n → ZMod p` has at most `p ^ ((1 - c p) * n)` members, and the exponent of
the arithmetic triangle removal lemma in `Fin n → ZMod p` is `C p = 1 + 1 / c p`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.c p`: the exponent `c p`.
* `ArithmeticTriangleRemovalInVectorSpaces.C p`: the exponent `C p = 1 + 1 / c p`.
* `ArithmeticTriangleRemovalInVectorSpaces.n₀ p η`: the dimension from which on there are
  multicolored sum-free families with at least `p ^ ((1 - c p - η) * n)` members.
* `ArithmeticTriangleRemovalInVectorSpaces.ε₀ p η`: the bound below which `δ ≤ ε ^ (C p - η)` in
  the arithmetic triangle removal lemma.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.rpow_one_sub_c_le`: `p ^ (1 - c p)` is at most the
  value of `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` at each `x ∈ Set.Ioo 0 1`.
* `ArithmeticTriangleRemovalInVectorSpaces.le_rpow_one_sub_c`: it is the largest such number.
* `ArithmeticTriangleRemovalInVectorSpaces.c_pos` and
  `ArithmeticTriangleRemovalInVectorSpaces.c_lt_one`: `0 < c p` and `c p < 1` for `2 ≤ p`.
-/

@[expose] public section

open Finset Filter Topology

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The exponent `c p` of Kleinberg, Sawin and Speyer, defined by
`p ^ (1 - c p) = ⨅ x : Set.Ioo 0 1, x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j`. -/
noncomputable def c (p : ℕ) : ℝ :=
  1 - Real.logb p
    (⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, (x : ℝ) ^ j)

/-- The exponent `C p = 1 + 1 / c p` of the arithmetic triangle removal lemma in
`Fin n → ZMod p`. -/
noncomputable def C (p : ℕ) : ℝ :=
  1 + 1 / c p

/-- The dimension `n₀ p η = ⌈(2 ^ (p + 3) * p ^ 10 / η) ^ 2⌉ + p ^ 4 + 1` from which on
`Fin n → ZMod p` contains a multicolored sum-free family with at least `p ^ ((1 - c p - η) * n)`
members. -/
noncomputable def n₀ (p : ℕ) (η : ℝ) : ℕ :=
  ⌈(2 ^ (p + 3) * p ^ 10 / η) ^ 2⌉₊ + p ^ 4 + 1

/-- The bound `ε₀ p η = p ^ (-(n₀ p η' + 1))` with `η' = c p * min (1 - c p) (c p * η / 2) / 2`.
For `0 < ε < ε₀ p η`, every `δ` that works with `ε` in the arithmetic triangle removal lemma in
`Fin n → ZMod p` for every `n` satisfies `δ ≤ ε ^ (C p - η)`. -/
noncomputable def ε₀ (p : ℕ) (η : ℝ) : ℝ :=
  ((p : ℝ) ^ (n₀ p (c p * min (1 - c p) (c p * η / 2) / 2) + 1))⁻¹

lemma pow_four_lt_n₀ (p : ℕ) (η : ℝ) : p ^ 4 < n₀ p η := by
  grind [n₀]

lemma sq_add_one_le_n₀ (p : ℕ) (η : ℝ) : (2 ^ (p + 3) * p ^ 10 / η) ^ 2 + 1 ≤ n₀ p η := by
  rw [n₀]
  push_cast
  gcongr ?_ + 1
  exact (Nat.le_ceil _).trans (le_add_of_nonneg_right (by positivity))

variable {p : ℕ}

/-- For `0 < x < 1` and `2 ≤ p`, `3 / 2 ≤ x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j`. -/
lemma three_div_two_le_rpow_mul_sum (hp : 2 ≤ p) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    3 / 2 ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j := by
  have hroot : x ^ (1 / 3 : ℝ) ≤ 1 + 1 / 3 * (x - 1) := by
    simpa using rpow_one_add_le_one_add_mul_self (by linarith : -1 ≤ x - 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  have hneg : 3 / (2 + x) ≤ x ^ (-((p : ℝ) - 1) / 3) := by
    grw [← Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁.le
      (by linarith [(Nat.ofNat_le_cast.2 hp : (2 : ℝ) ≤ p)] : -((p : ℝ) - 1) / 3 ≤ -(1 / 3))]
    rw [Real.rpow_neg hx₀.le, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    linarith
  have hsum : 1 + x ≤ ∑ j ∈ range p, x ^ j := by
    grw [← sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hp) fun j _ _ ↦ by positivity]
    simp [add_comm]
  grw [← hneg, ← hsum]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- The value of the infimum defining `c p`. -/
private lemma rpow_one_sub_c (hp : 2 ≤ p) :
    (p : ℝ) ^ (1 - c p) =
      ⨅ x : Set.Ioo (0 : ℝ) 1, (x : ℝ) ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, (x : ℝ) ^ j := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  rw [c, sub_sub_cancel, Real.rpow_logb (by positivity)
    (by exact_mod_cast (by grind : p ≠ 1))]
  refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2) (le_ciInf ?_)
  rintro ⟨x, hx₀, hx₁⟩
  exact three_div_two_le_rpow_mul_sum hp hx₀ hx₁

/-- `p ^ (1 - c p)` is at most `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` for `0 < x < 1`. -/
lemma rpow_one_sub_c_le (hp : 2 ≤ p) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    (p : ℝ) ^ (1 - c p) ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j := by
  rw [rpow_one_sub_c hp]
  refine ciInf_le ⟨0, ?_⟩ (⟨x, hx₀, hx₁⟩ : Set.Ioo (0 : ℝ) 1)
  rintro _ ⟨⟨y, hy₀, -⟩, rfl⟩
  positivity

/-- `p ^ (1 - c p)` is the largest lower bound of `x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` on
`Set.Ioo 0 1`. -/
lemma le_rpow_one_sub_c (hp : 2 ≤ p) {b : ℝ}
    (h : ∀ x : ℝ, 0 < x → x < 1 → b ≤ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) :
    b ≤ (p : ℝ) ^ (1 - c p) := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  rw [rpow_one_sub_c hp]
  apply le_ciInf
  rintro ⟨x, hx₀, hx₁⟩
  exact h x hx₀ hx₁

/-- The function `fun x ↦ x ^ (-(p - 1) / 3) * ∑ j ∈ range p, x ^ j` takes a value smaller than
`p` on `Set.Ioo 0 1`: its value at `1` is `p` and its derivative there is `p * (p - 1) / 6`, which
is positive. -/
private lemma exists_rpow_mul_sum_lt (hp : 2 ≤ p) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j < p := by
  have hderiv : HasDerivAt (fun x : ℝ ↦ x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j)
      (p * (p - 1) / 6) 1 := by
    have h := sum_range_id_mul_two p
    rw [← Nat.cast_inj (R := ℝ)] at h
    push_cast [Nat.cast_sub (by grind : 1 ≤ p)] at h
    convert (Real.hasDerivAt_rpow_const (p := -((p : ℝ) - 1) / 3) (Or.inl one_ne_zero)).fun_mul
      (HasDerivAt.fun_sum fun j (_ : j ∈ range p) ↦ hasDerivAt_pow j (1 : ℝ)) using 1
    simp
    linarith
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left
    (nhdsWithin_mono _ fun y (hy : y ∈ Set.Iio 1) ↦ hy.ne)
  obtain ⟨x, hslope, hx₀, hx₁⟩ := ((hslope.eventually (lt_mem_nhds
    (by nlinarith [(Nat.ofNat_le_cast.2 hp : (2 : ℝ) ≤ p)] : (0 : ℝ) < p * (p - 1) / 6))).and
    (Ioo_mem_nhdsLT one_pos)).exists
  refine ⟨x, hx₀, hx₁, ?_⟩
  rw [slope_def_field, lt_div_iff_of_neg (by linarith), zero_mul, sub_neg] at hslope
  simpa using hslope

/-- The exponent `c p` is positive. -/
lemma c_pos (hp : 2 ≤ p) : 0 < c p := by
  obtain ⟨x, hx₀, hx₁, hx⟩ := exists_rpow_mul_sum_lt hp
  by_contra! hc
  have := Real.self_le_rpow_of_one_le (Nat.one_le_cast.2 (by grind) : (1 : ℝ) ≤ p)
    (by linarith : 1 ≤ 1 - c p)
  linarith [rpow_one_sub_c_le hp hx₀ hx₁]

/-- The exponent `c p` is less than one. -/
lemma c_lt_one (hp : 2 ≤ p) : c p < 1 := by
  by_contra! hc
  linarith [le_rpow_one_sub_c hp fun _ ↦ three_div_two_le_rpow_mul_sum hp,
    Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 (by grind) : (1 : ℝ) ≤ p)
      (by linarith : 1 - c p ≤ 0)]

end ArithmeticTriangleRemovalInVectorSpaces

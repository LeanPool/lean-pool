/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Basis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The growth facts

Śliwa (p. 628) fixes a growth condition on `d` and derives a list of inequalities between the
`aₙ`, `bₙ` and `vₙ`. The proofs only ever use those inequalities, so they are collected here as
hypotheses (`ReadL1.GrowthHyp`), extending the three the partition needs. They are proved for an
explicit sequence at the end.
-/

@[expose] public section

namespace ReadL1

/-- The growth facts used in the proofs (Śliwa p. 628, and consequences). -/
structure GrowthHyp (d : ℕ → ℕ) : Prop extends PartitionHyp d where
  /-- `aₘ₊₁ ≥ 2aₘ` (Śliwa: `8m bₘ < aₘ₊₁` and `aₘ < bₘ`). -/
  a_double : ∀ m, 1 ≤ m → 2 * seqA d m ≤ seqA d (m + 1)
  /-- `bₘ ≥ 2` (`d` is increasing from `d₀ = 2`). -/
  two_le_b : ∀ m, 2 ≤ seqB d m
  /-- `8(vₖ + 1) < aₙ` for `k < n` (Śliwa: `8(vₙ₋₁ + 1) < aₙ`, and `v` increases). -/
  v_small : ∀ n k, k < n → 8 * (seqV d k + 1) < seqA d n
  /-- `8n aₙ < bₙ`. -/
  a_small : ∀ n, 1 ≤ n → 8 * n * seqA d n < seqB d n
  /-- `8n bₙ < aₙ₊₁`. -/
  b_small : ∀ n, 1 ≤ n → 8 * n * seqB d n < seqA d (n + 1)
  /-- `n² aₙ² < bₙ`. -/
  a_sq : ∀ n, 1 ≤ n → n ^ 2 * seqA d n ^ 2 < seqB d n
  /-- `aₙ ≥ α⁴ = 4096`. -/
  a_big : ∀ n, 1 ≤ n → 4096 ≤ seqA d n
  /-- `α aₙ² < α^{√aₙ / 4}`. -/
  rpow_a : ∀ n, 1 ≤ n → alpha * (seqA d n : ℝ) ^ 2 < alpha ^ (Real.sqrt (seqA d n) / 4)
  /-- `α bₙ² < α^{√bₙ / 4}`. -/
  rpow_b : ∀ n, 1 ≤ n → alpha * (seqB d n : ℝ) ^ 2 < alpha ^ (Real.sqrt (seqB d n) / 4)
  /-- `bₙ^{4n} < α^{√bₙ / 4}`. -/
  pow_b : ∀ n, 1 ≤ n → (seqB d n : ℝ) ^ (4 * n) < alpha ^ (Real.sqrt (seqB d n) / 4)
  /-- `α^{√bₘ} + 2 ≤ α^{√aₘ₊₁}` (implicit in Śliwa's Lemma 1 (a); `aₘ₊₁ ≥ α^{2bₘ}`). -/
  rpow_b_add_two_le : ∀ m, 1 ≤ m →
    alpha ^ Real.sqrt (seqB d m) + 2 ≤ alpha ^ Real.sqrt (seqA d (m + 1))
  /-- `3 bₙⁿ α^{√aₙ} ≤ α^{√bₙ}` (implicit in Śliwa's Lemma 1 (a); `bₙ ≥ α^{2aₙ}`). -/
  three_pow_rpow_a_le : ∀ n, 1 ≤ n →
    3 * (seqB d n : ℝ) ^ n * alpha ^ Real.sqrt (seqA d n) ≤ alpha ^ Real.sqrt (seqB d n)
  /-- `aₘ Bₘ₋₁ ≤ √Aₘ`, i.e. `aₘ α^{√bₘ₋₁} ≤ α^{√aₘ/2}` (Śliwa p. 632, the bound on `Qₘ`). -/
  q_bound : ∀ m, 2 ≤ m →
    (seqA d m : ℝ) * alpha ^ Real.sqrt (seqB d (m - 1)) ≤ alpha ^ (Real.sqrt (seqA d m) / 2)
  /-- `4bₘ² < aₘ₊₁` (Śliwa p. 633: `s < 2bₘ < √aₙ`). -/
  four_sq_b_lt_a : ∀ m, 1 ≤ m → 4 * seqB d m ^ 2 < seqA d (m + 1)
  /-- `α^{2bₘ} ≤ aₘ₊₁`: Śliwa's growth condition `dₙ ≥ α^{2dₙ₋₁}` itself, at `n = 2m + 1`. -/
  alpha_pow_two_b_le : ∀ m, 1 ≤ m → alpha ^ (2 * seqB d m) ≤ seqA d (m + 1)
  /-- `Aₙ = α^{√aₙ} ≤ bₙ` (Śliwa p. 634; `bₙ ≥ α^{2aₙ}`). -/
  rpow_a_le_b : ∀ n, 1 ≤ n → alpha ^ Real.sqrt (seqA d n) ≤ seqB d n

variable {d : ℕ → ℕ}

/-- `a` grows at least geometrically: `aₘ₊ⱼ ≥ 2ʲ aₘ`. -/
lemma pow_two_mul_le_seqA (h : GrowthHyp d) {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    2 ^ j * seqA d m ≤ seqA d (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc 2 ^ (j + 1) * seqA d m = 2 * (2 ^ j * seqA d m) := by ring
      _ ≤ 2 * seqA d (m + j) := Nat.mul_le_mul_left _ ih
      _ ≤ seqA d (m + j + 1) := h.a_double _ (by omega)

/-! ### Powers of `α` -/

lemma one_le_alpha : 1 ≤ alpha := by norm_num [alpha]

lemma alpha_rpow_le {x y : ℝ} (hxy : x ≤ y) : alpha ^ x ≤ alpha ^ y :=
  Real.rpow_le_rpow_of_exponent_le one_le_alpha hxy

lemma sqrt_four_mul (c : ℝ) : Real.sqrt (4 * c) = 2 * Real.sqrt c := by
  rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ### The weights -/

/-- The inverse weight is `α^{-((2r - 1)c - 2i)/√(4c)}`. -/
lemma inv_weight (c r i : ℕ) :
    (weight c r i)⁻¹ = alpha ^ (-(((2 * (r : ℝ) - 1) * c - 2 * i) / Real.sqrt (4 * c))) := by
  rw [weight, Real.rpow_neg alpha_pos.le]

/-- **If the numerator of the exponent is at least `c / 2`, the inverse weight is at most
`α^{-√c/4}`.** This is how every "`≤ α^{-√aₙ/4}`" in Śliwa's case analysis arises. -/
lemma inv_weight_le {c r i : ℕ} (hc : 0 < c)
    (hE : (c : ℝ) / 2 ≤ (2 * (r : ℝ) - 1) * c - 2 * i) :
    (weight c r i)⁻¹ ≤ alpha ^ (-(Real.sqrt c / 4)) := by
  rw [inv_weight]
  refine alpha_rpow_le (neg_le_neg ?_)
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc)
  rw [sqrt_four_mul, le_div_iff₀ (by positivity)]
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt (by positivity)
  nlinarith

/-- Consecutive weights differ by `α^{1/√c}`: `weight i = α^{1/√c} · weight (i + 1)`. -/
lemma weight_eq_mul_succ {c : ℕ} (hc : 0 < c) (r i : ℕ) :
    weight c r i = alpha ^ (1 / Real.sqrt c) * weight c r (i + 1) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc)
  rw [weight, weight, ← Real.rpow_add alpha_pos, sqrt_four_mul]
  congr 1
  push_cast
  field_simp
  ring

end ReadL1

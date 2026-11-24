/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.BCH.Basic
public import Mathlib.Algebra.Lie.OfAssociative
import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialProduct
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The commutator expansion of the BCH element

The following estimates give the error in approximating `bch a b` by `a + b` and identify its
leading correction. Both hold for `s = ‖a‖ + ‖b‖ < log 2`, where the logarithm converges.

## Main results

* `norm_bch_sub_add_le` — **quadratic**: `‖bch a b - (a + b)‖ ≤ 3 s² / (2 - eˢ)`, i.e. the linear
  part of `bch a b` is `a + b`.
* `norm_bch_sub_add_sub_bracket_le` — **cubic (commutator extraction)**:
  `‖bch a b - (a + b) - ½(a * b - b * a)‖ ≤ 10 s³ / (2 - eˢ)`, which identifies the leading
  non-commutative correction as the Lie bracket `½[a, b]`. Mathlib identifies
  `⁅a, b⁆ = a * b - b * a` and `norm_bch_sub_add_sub_lie_le` is the same bound in `⁅·,·⁆` notation.

In the symmetric Strang product the leading commutator cancels.
See `FQFP.Analysis.Normed.Algebra.BCH.Symmetric` for the resulting cubic bound.

## Provenance and design

Ported from `Lean-BCH/BCH/Basic.lean` (`norm_bch_sub_add_le`,
`norm_bch_sub_add_sub_bracket_le`, `norm_bch_sub_add_sub_lie_le`). The proofs use the finite
logarithm remainder bound and the Taylor remainders of the ordered exponential product.

The source's `norm_bch_sub_add_le'` is deliberately not ported: it is the quadratic bound verbatim
under a second name.
-/

@[expose] public section

open NormedSpace

namespace FQFP.BCH

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
/-! ### The quadratic bound for `bch`

`‖bch a b - (a + b)‖ ≤ 3 s² / (2 - eˢ)` where `s = ‖a‖ + ‖b‖`. The proof splits
`bch a b - (a + b)` into the logarithm's remainder at `exp a * exp b - 1` and the exponential's own
remainder `exp a * exp b - 1 - (a + b)`, bounds each, and uses `eˢ ≤ 1 + s + s²` (for `s < 1`,
where `1 + s ≤ eˢ < 2`) to absorb the result into `3 s² / (2 - eˢ)`. The bound diverges at
`s = log 2`, the boundary of this sufficient convergence range. -/

/-- **The quadratic BCH bound**: `‖bch a b - (a + b)‖ ≤ 3 s² / (2 - eˢ)` for
`s = ‖a‖ + ‖b‖ < log 2`, with the leading non-commutative correction `⁅a, b⁆/2` left inside the
remainder. -/
theorem norm_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b)‖ ≤ 3 * (‖a‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  obtain ⟨hd, -⟩ := exp_log_two_denominator_bounds hs hab
  have hs1 : s ≤ 1 := by linarith only [hd, Real.add_one_le_exp s]
  have ht := real_exp_sub_one_sub_id_le_sq hs hs1
  have he := real_exp_sub_one_le_two_mul hs hs1
  apply (norm_bch_sub_le_of_logPartialSum a b (a + b) 2 hab
    (by simpa only [logPartialSum_two] using norm_exp_mul_exp_sub_one_sub_add_le a b)).trans
  rw [div_add' _ _ _ hd.ne', div_le_div_iff_of_pos_right hd]
  nlinarith only [ht, mul_le_mul_of_nonneg_left he hs]

/-! ### The cubic bound

For `y = exp a * exp b - 1` and `z = a + b`, the quadratic logarithm approximation
is `y - y²/2`. Subtracting the BCH polynomial leaves the exponential product's cubic
remainder and the correction `-(y² - z²)/2`.
-/

/-- **Commutator extraction (H1)**: `bch a b` agrees with `a + b + ½(a * b - b * a)` up to
`10 s³ / (2 - eˢ)`, so the leading non-commutative correction to `bch` is the Lie bracket
`½[a, b]`. -/
theorem norm_bch_sub_add_sub_bracket_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a)‖ ≤
      10 * (‖a‖ + ‖b‖) ^ 3 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  let y := exp a * exp b - 1
  let z := a + b
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hs34 : s ≤ 3 / 4 := by linarith only [hab, Real.log_two_lt_d9]
  have hs1 : s ≤ 1 := by linarith only [hs34]
  have hy : ‖y‖ ≤ 2 * s := (norm_exp_mul_exp_sub_one_le a b).trans
    (real_exp_sub_one_le_two_mul hs hs1)
  have hyz : ‖y - z‖ ≤ s ^ 2 := (norm_exp_mul_exp_sub_one_sub_add_le a b).trans
    (real_exp_sub_one_sub_id_le_sq hs hs1)
  have hsq : ‖y ^ 2 - z ^ 2‖ ≤ 3 * s ^ 3 := calc
    _ ≤ (‖y‖ + ‖z‖) * ‖y - z‖ := norm_sq_sub_sq_le y z
    _ ≤ (2 * s + s) * s ^ 2 :=
      mul_le_mul (add_le_add hy (norm_add_le a b)) hyz (norm_nonneg _) (by positivity)
    _ = _ := by ring
  have hprod : ‖y - z - expMulTerm a b 2‖ ≤ s ^ 3 := by
    rw [expMulTerm_two]
    exact (norm_exp_mul_exp_sub_quadratic_le a b).trans
      (real_exp_third_order_le_cube hs (by linarith only [hs34]))
  have hpoly : ‖logPartialSum 𝔸 3 y - (z + (2 : ℚ)⁻¹ • (a * b - b * a))‖ ≤ 4 * s ^ 3 := by
    have hsplit : logPartialSum 𝔸 3 y - (z + (2 : ℚ)⁻¹ • (a * b - b * a)) =
        (y - z - expMulTerm a b 2) - (2 : ℚ)⁻¹ • (y ^ 2 - z ^ 2) := by
      simp only [logPartialSum_three, expMulTerm_two, z, pow_two, add_mul, mul_add,
        smul_add, smul_sub]
      module
    rw [hsplit]
    have hhalf : ‖(2 : ℚ)⁻¹‖ ≤ 1 := by rw [norm_inv, ← Rat.norm_cast_real]; norm_num
    have hcorr : ‖(2 : ℚ)⁻¹ • (y ^ 2 - z ^ 2)‖ ≤ 3 * s ^ 3 :=
      (norm_smul_le _ _).trans (by simpa using mul_le_mul hhalf hsq (norm_nonneg _) zero_le_one)
    exact (norm_sub_le_of_le hprod hcorr).trans_eq (by ring)
  simpa only [z, sub_add_eq_sub_sub] using
    norm_bch_sub_le_div_of_logPartialSum a b _ 3 hab (by norm_num) hpoly
      (real_exp_sub_one_pow_le_of_le hs hs34 (by norm_num) 3) (by norm_num : _ ≤ (10 : ℝ))

/-! ### The Lie bracket

The local instance `LieRing.ofAssociativeRing` gives the bracket
`⁅a, b⁆ = a * b - b * a` by `Ring.lie_def`. -/

end

section CubicBoundLie

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

attribute [local instance] LieRing.ofAssociativeRing

/-- **Commutator extraction, Lie bracket form**: `bch a b = a + b + ½⁅a, b⁆ + O(s³)`, the source's
main statement of H1 in Mathlib's Lie-bracket notation. -/
theorem norm_bch_sub_add_sub_lie_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • ⁅a, b⁆‖ ≤
      10 * (‖a‖ + ‖b‖) ^ 3 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  rw [Ring.lie_def]
  exact norm_bch_sub_add_sub_bracket_le a b hab

end CubicBoundLie

end FQFP.BCH

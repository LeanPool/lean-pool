/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.BCH.Composition
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialProductTriple

/-!
# Symmetric BCH and its homogeneous approximations

The symmetric product `exp (a/2) * exp b * exp (a/2)` — equivalently `exp (bch (bch (a/2) b) (a/2))`
— differs from `exp (a + b)` by `O(s³)` rather than `O(s²)`:

`‖bch (bch (a/2) b) (a/2) - (a + b)‖ ≤ 300 s³`, for `s = ‖a‖ + ‖b‖ < 1/4`.

This is why the Strang splitting is a *second-order* integrator. The mechanism is a cancellation:
`BCHCommutator.norm_bch_sub_add_sub_bracket_le` applied twice exhibits `½[a/2, b]` from the first
application and `½[z, a/2]` from the second, and the ring identity

`(z * a' - a' * z) + (a' * b - b * a') = δ * a' - a' * δ`,   `δ = z - (a' + b)`,  `a' = a/2`,

turns their sum into a single commutator whose first factor `δ` is only `O(s²)`. The three
remaining pieces are then bounded by `10 s₂³ / (2 - e^{s₂})`, `(3 s² / (2 - e^{s₁})) · (s / 2)` and
`10 s₁³ / (2 - e^{s₁})` where `s₁ = ‖a'‖ + ‖b‖` and `s₂ = ‖z‖ + ‖a'‖`, giving
`240 + 24/11 + 160/11 ≈ 256.7` in place of the stated `300`.

## Main results

* `symmetricBch_eq_log_exp_mul_exp_mul_exp`: the three-factor logarithm representation.
* `norm_symmetricBch_sub_sum_le`: a finite homogeneous approximation at any truncation order.
* `norm_symmetric_bch_sub_add_le`: the cubic Strang splitting error bound.

## Provenance and design

Ported from `Lean-BCH/BCH/Basic.lean` (`norm_symmetric_bch_sub_add_le`). The real-arithmetic
input control is shared with higher-order compositions through `BCHComposition`; the remaining
bookkeeping is isolated in `symmetric_bch_real_core`, each estimate
being an explicit chain of order-theoretic steps rather than one large `linarith`.

`symmetricBch` names the nested BCH element itself. Its exponential-product identity
provides the logarithm representation used by higher-order symmetric expansions.

The source's `norm_symmetric_bch_sub_add_lie_le` is deliberately not ported: it is this statement
verbatim under a second name.
-/

@[expose] public section

open NormedSpace Finset

namespace FQFP.BCH

noncomputable section

/-- The BCH element of the symmetric three-factor product with two half steps. -/
def symmetricBch {A : Type*} [Ring A] [Algebra ℚ A] [TopologicalSpace A]
    [IsTopologicalRing A] (a b : A) : A :=
  bch (bch ((2 : ℚ)⁻¹ • a) b) ((2 : ℚ)⁻¹ • a)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The symmetric BCH element is the logarithm of its ordered exponential product. -/
theorem symmetricBch_eq_log_exp_mul_exp_mul_exp (a b : 𝔸)
    (hab : ‖(2 : ℚ)⁻¹ • a‖ + ‖b‖ < Real.log 2) :
    symmetricBch a b =
      log (exp ((2 : ℚ)⁻¹ • a) * exp b * exp ((2 : ℚ)⁻¹ • a)) := by
  rw [symmetricBch, bch, exp_bch _ _ hab]

/-- Bound the symmetric BCH element by its finite homogeneous logarithm approximation
at any truncation order, using the total norm of the two full inputs. -/
theorem norm_symmetricBch_sub_sum_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) (n : ℕ) :
    ‖symmetricBch a b - ∑ k ∈ range n, logCoeff k • positivePowerTrunc
      (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k n‖ ≤
      ((n : ℝ) * 2 ^ (n - 1) + 2 ^ (n + 1)) * (‖a‖ + ‖b‖) ^ n := by
  let h := (2 : ℚ)⁻¹ • a
  let s := ‖a‖ + ‖b‖
  let r := ‖h‖ + ‖b‖ + ‖h‖
  have hr0 : 0 ≤ r := by positivity
  have hr : r ≤ s := by
    dsimp only [r, h, s]
    linarith only [two_mul_norm_half_smul_add_norm_le a b]
  have hinner : ‖h‖ + ‖b‖ < Real.log 2 := by
    have hi : ‖h‖ + ‖b‖ ≤ s := by
      dsimp only [r] at hr
      linarith only [hr, norm_nonneg h]
    exact hi.trans_lt (hab.trans ((by norm_num : (1 : ℝ) / 4 < 1 / 2).trans half_lt_log_two))
  rw [symmetricBch_eq_log_exp_mul_exp_mul_exp a b hinner]
  exact (norm_log_exp_mul_exp_mul_exp_sub_sum_le h b h (hr.trans_lt hab) n).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr n) (by positivity))

/-! ### The scalar bounds

The denominator estimates and control of the second BCH input come from `BCHComposition`.
The remaining scalar estimate assembles the three cubic error terms. -/

/-- **The real-arithmetic core of the Strang bound**: with `s₂ ≤ 2 s`, the three pieces
`10 s₂³/(2 - e^{s₂})`, `(3 s²/(2 - e^{s₁}))·(s/2)` and `10 s₁³/(2 - e^{s₁})` sum to at most
`300 s³`. The denominators are bounded by `1/3` (at `s₂`, via `s₂ < 1/2`) and `11/16` (at `s₁`),
giving `240 + 24/11 + 160/11 ≈ 256.7 ≤ 300`. -/
private lemma symmetric_bch_real_core {s s₁ s₂ : ℝ} (hs_nn : 0 ≤ s) (hs14 : s < 1 / 4)
    (hs₁_nn : 0 ≤ s₁) (hs₁_le : s₁ ≤ s) (hs₂_nn : 0 ≤ s₂) (hs₂_le : s₂ ≤ 2 * s) :
    10 * s₂ ^ 3 / (2 - Real.exp s₂) + 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) +
      10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 300 * s ^ 3 := by
  have hdenom₁_lb := eleven_sixteenths_le_two_sub_exp hs_nn hs14 hs₁_le
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith only [hdenom₁_lb]
  have hdenom₂_lb : (1 : ℝ) / 3 ≤ 2 - Real.exp s₂ :=
    one_third_le_two_sub_exp (by linarith only [hs₂_le, hs14])
  have hdenom₂ : 0 < 2 - Real.exp s₂ := by linarith
  -- the three pieces
  have hterm1 : 10 * s₂ ^ 3 / (2 - Real.exp s₂) ≤ 240 * s ^ 3 := by
    rw [div_le_iff₀ hdenom₂]
    have hs₂3 : s₂ ^ 3 ≤ 8 * s ^ 3 := by
      have h := pow_le_pow_left₀ hs₂_nn hs₂_le 3
      rwa [show (2 * s) ^ 3 = 8 * s ^ 3 from by ring] at h
    have h1 : 240 * s ^ 3 * (1 / 3) ≤ 240 * s ^ 3 * (2 - Real.exp s₂) :=
      mul_le_mul_of_nonneg_left hdenom₂_lb (by positivity)
    have h2 : 10 * s₂ ^ 3 ≤ 240 * s ^ 3 * (1 / 3) := by linarith [pow_nonneg hs_nn 3]
    linarith
  have hterm2 : 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) ≤ 24 / 11 * s ^ 3 := by
    have hdiv : 3 * s ^ 2 / (2 - Real.exp s₁) ≤ 3 * s ^ 2 / (11 / 16) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hdenom₁_lb
    calc 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2)
        ≤ 3 * s ^ 2 / (11 / 16) * (s / 2) := mul_le_mul_of_nonneg_right hdiv (by linarith)
      _ = 24 / 11 * s ^ 3 := by ring
  have hterm3 : 10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 := by
    rw [div_le_iff₀ hdenom₁]
    have hs₁3 : s₁ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs₁_nn hs₁_le 3
    have h1 : 10 * s₁ ^ 3 ≤ 10 * s ^ 3 := mul_le_mul_of_nonneg_left hs₁3 (by norm_num)
    have h2 : 160 / 11 * s ^ 3 * (11 / 16) = 10 * s ^ 3 := by ring
    have h3 : 160 / 11 * s ^ 3 * (11 / 16) ≤ 160 / 11 * s ^ 3 * (2 - Real.exp s₁) :=
      mul_le_mul_of_nonneg_left hdenom₁_lb (by positivity)
    linarith
  linarith [hterm1, hterm2, hterm3, pow_nonneg hs_nn 3]

/-! ### The Strang bound -/

/-- **Symmetric BCH (Strang splitting)**: `bch (bch (a/2) b) (a/2) = a + b + O(s³)`, with an
explicit constant: `‖· - (a + b)‖ ≤ 300 s³` for `s = ‖a‖ + ‖b‖ < 1/4`.

The second-order commutators `½[a/2, b]` and `½[bch (a/2) b, a/2]` cancel, which is exactly what
makes the Strang splitting a second-order integrator. -/
theorem norm_symmetric_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖bch (bch ((2 : ℚ)⁻¹ • a) b) ((2 : ℚ)⁻¹ • a) - (a + b)‖ ≤ 300 * (‖a‖ + ‖b‖) ^ 3 := by
  set a' : 𝔸 := (2 : ℚ)⁻¹ • a with ha'_def
  set s : ℝ := ‖a‖ + ‖b‖ with hs_def
  have ha'_le : ‖a'‖ ≤ ‖a‖ / 2 := norm_half_smul_le a
  have hs_nn : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hs14 : s < 1 / 4 := hab
  have hweighted : 2 * ‖a'‖ + ‖b‖ ≤ s := two_mul_norm_half_smul_add_norm_le a b
  set s₁ : ℝ := ‖a'‖ + ‖b‖ with hs₁_def
  have hs₁_le : s₁ ≤ s := by
    dsimp [s₁]
    linarith only [hweighted, norm_nonneg a']
  have hs₁_nn : 0 ≤ s₁ := add_nonneg (norm_nonneg a') (norm_nonneg b)
  have ha_le_s : ‖a‖ ≤ s := le_add_of_nonneg_right (norm_nonneg b)
  have hdenom₁_lb := eleven_sixteenths_le_two_sub_exp hs_nn hs14 hs₁_le
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith only [hdenom₁_lb]
  have hs₁_log2 : s₁ < Real.log 2 := by
    have hhalf := half_lt_log_two
    linarith only [hs₁_le, hs14, hhalf]
  set z : 𝔸 := bch a' b with hz_def
  have hR₃' : ‖z - (a' + b) - (2 : ℚ)⁻¹ • (a' * b - b * a')‖ ≤
      10 * s₁ ^ 3 / (2 - Real.exp s₁) :=
    norm_bch_sub_add_sub_bracket_le a' b hs₁_log2
  set s₂ : ℝ := ‖z‖ + ‖a'‖ with hs₂_def
  have hs₂_le_2s : s₂ ≤ 2 * s := norm_bch_add_norm_le_two_mul a' b hweighted hs14
  have hs₂_nn : 0 ≤ s₂ := add_nonneg (norm_nonneg z) (norm_nonneg a')
  have hs₂_log2 : s₂ < Real.log 2 := norm_bch_add_norm_lt_log_two a' b hweighted hs14
  have hR₃'' : ‖bch z a' - (z + a') - (2 : ℚ)⁻¹ • (z * a' - a' * z)‖ ≤
      10 * s₂ ^ 3 / (2 - Real.exp s₂) :=
    norm_bch_sub_add_sub_bracket_le z a' hs₂_log2
  -- the cancellation identity and the algebraic decomposition
  set δ : 𝔸 := z - (a' + b) with hδ_def
  have hcomm_cancel : (z * a' - a' * z) + (a' * b - b * a') = δ * a' - a' * δ := by
    rw [hδ_def]
    noncomm_ring
  have ha'_add : a' + a' = a := by
    rw [ha'_def, ← add_smul, show (2 : ℚ)⁻¹ + (2 : ℚ)⁻¹ = 1 from by
      rw [← two_mul, mul_inv_cancel₀ (two_ne_zero : (2 : ℚ) ≠ 0)]]
    exact one_smul _ _
  have hfull : bch z a' - (a + b) =
      (bch z a' - (z + a') - (2 : ℚ)⁻¹ • (z * a' - a' * z)) +
      ((2 : ℚ)⁻¹ • (δ * a' - a' * δ)) +
      (z - (a' + b) - (2 : ℚ)⁻¹ • (a' * b - b * a')) := by
    have hsmul_expand : (2 : ℚ)⁻¹ • (δ * a' - a' * δ) =
        (2 : ℚ)⁻¹ • (z * a' - a' * z) + (2 : ℚ)⁻¹ • (a' * b - b * a') := by
      rw [← smul_add, ← hcomm_cancel]
    rw [hsmul_expand, ← ha'_add]
    abel
  -- the middle piece
  have hcomm_bound : ‖(2 : ℚ)⁻¹ • (δ * a' - a' * δ)‖ ≤ ‖δ‖ * ‖a'‖ :=
    norm_half_commutator_le δ a'
  have hδ_le : ‖δ‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    rw [hδ_def]
    exact norm_bch_sub_add_le a' b hs₁_log2
  have ha'_le_s2 : ‖a'‖ ≤ s / 2 := by linarith [ha'_le, ha_le_s]
  have hδ_cubic : ‖δ‖ * ‖a'‖ ≤ 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) := by
    have h1 : ‖δ‖ * ‖a'‖ ≤ (3 * s₁ ^ 2 / (2 - Real.exp s₁)) * (s / 2) :=
      mul_le_mul hδ_le ha'_le_s2 (norm_nonneg _) (div_nonneg (by positivity) hdenom₁.le)
    have hs₁2 : 3 * s₁ ^ 2 ≤ 3 * s ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs₁_nn hs₁_le 2) (by norm_num)
    have h2 : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 3 * s ^ 2 / (2 - Real.exp s₁) :=
      div_le_div_of_nonneg_right hs₁2 hdenom₁.le
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by linarith))
  -- assemble
  have hbound : ‖(bch z a' - (z + a') - (2 : ℚ)⁻¹ • (z * a' - a' * z)) +
        ((2 : ℚ)⁻¹ • (δ * a' - a' * δ)) +
        (z - (a' + b) - (2 : ℚ)⁻¹ • (a' * b - b * a'))‖ ≤
      10 * s₂ ^ 3 / (2 - Real.exp s₂) + 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) +
        10 * s₁ ^ 3 / (2 - Real.exp s₁) :=
    (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hR₃'' (hcomm_bound.trans hδ_cubic)))
        hR₃')
  rw [hfull]
  exact hbound.trans (symmetric_bch_real_core hs_nn hs14 hs₁_nn hs₁_le hs₂_nn hs₂_le_2s)

end

end FQFP.BCH

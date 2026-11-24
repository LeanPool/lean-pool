/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.BCH.Commutator

/-!
# Input and denominator control for nested BCH compositions

If `2 ‖x‖ + ‖y‖ ≤ s < 1/4`, the inner pair `x, y` is inside the BCH convergence range,
and the outer pair `bch x y, x` has total norm at most `2s`. The logarithm denominators
are bounded below by `11/16` at the inner scale and by `1/3` at the outer scale.
Taking `x = a/2`, `y = b` gives the input control shared by symmetric BCH estimates.

## Main results

* `norm_half_smul_le`, `norm_half_commutator_le`: half-scaled norm estimates.
* `eleven_sixteenths_le_two_sub_exp`, `one_third_le_two_sub_exp`: denominator bounds.
* `half_lt_log_two`: the outer scale `1/2` lies inside the sufficient logarithm radius.
* `norm_bch_add_norm_le_two_mul`: norm control for a nested BCH input.
* `norm_bch_add_norm_lt_log_two`: convergence of the outer BCH pair.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-! ### Scalar denominator estimates -/

/-- The exponential estimates the Strang bound consumes: `eˢ ≤ 1 + s + s²`,
`2 - e^{s₁} ≥ 11/16`, and the two power bounds `s² ≤ s/4`, `s³ ≤ s²/4` for `s ≤ 1/4`. -/
private lemma exp_bounds {s s₁ : ℝ} (hs_nn : 0 ≤ s) (hs14 : s < 1 / 4) (hs₁_le : s₁ ≤ s) :
    Real.exp s ≤ 1 + s + s ^ 2 ∧ (11 : ℝ) / 16 ≤ 2 - Real.exp s₁ ∧
      s ^ 2 ≤ s / 4 ∧ s ^ 3 ≤ s ^ 2 / 4 := by
  have hs56 : s < 5 / 6 := by linarith only [hs14]
  have hs_le : s ≤ 1 / 4 := le_of_lt hs14
  have hs2_le : s ^ 2 ≤ s / 4 :=
    calc s ^ 2 = s * s := by ring
      _ ≤ s * (1 / 4) := mul_le_mul_of_nonneg_left hs_le hs_nn
      _ = s / 4 := by ring
  have hs3_le : s ^ 3 ≤ s ^ 2 / 4 :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ s ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hs_le (sq_nonneg s)
      _ = s ^ 2 / 4 := by ring
  have hexp_le : Real.exp s ≤ 1 + s + s ^ 2 := by
    have hcube := real_exp_third_order_le_cube hs_nn hs56
    linarith only [hcube, hs3_le, sq_nonneg s]
  refine ⟨hexp_le, ?_, hs2_le, hs3_le⟩
  have h₁ : Real.exp s₁ ≤ Real.exp s := Real.exp_le_exp.mpr hs₁_le
  have h₂ : 1 + s + s ^ 2 ≤ 21 / 16 := by linarith only [hs2_le, hs_le]
  linarith only [h₁, h₂, hexp_le]

/-- The logarithm denominator is at least `11/16` below a nonnegative scale `s < 1/4`. -/
lemma eleven_sixteenths_le_two_sub_exp {s t : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 4)
    (ht : t ≤ s) : (11 : ℝ) / 16 ≤ 2 - Real.exp t :=
  (exp_bounds hs0 hs ht).2.1

/-- The logarithm denominator is at least `1/3` at every scale at most `1/2`. -/
lemma one_third_le_two_sub_exp {t : ℝ} (ht : t ≤ 1 / 2) :
    (1 : ℝ) / 3 ≤ 2 - Real.exp t := by
  have h := real_exp_third_order_le_div (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)
  have he : Real.exp t ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr ht
  norm_num at h
  linarith only [h, he]

/-- The scale `1/2` lies inside the sufficient logarithm convergence radius. -/
lemma half_lt_log_two : (1 : ℝ) / 2 < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
  have h := one_third_le_two_sub_exp (t := 1 / 2) le_rfl
  linarith only [h]

/-- The scalar facts used before the final assembly: `2 - e^{s₁}` is bounded below, the cubic
correction at scale `s₁` is at most `(160/11) s³`, and `s²/8 + (160/11) s³ ≤ s`. -/
private lemma bch_scale_bounds {s s₁ : ℝ} (hs_nn : 0 ≤ s) (hs14 : s < 1 / 4)
    (hs₁_nn : 0 ≤ s₁) (hs₁_le : s₁ ≤ s) :
    (11 : ℝ) / 16 ≤ 2 - Real.exp s₁ ∧
      10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 ∧
      s ^ 2 / 8 + 160 / 11 * s ^ 3 ≤ s := by
  obtain ⟨_, hdenom₁_lb, hs2_le, hs3_le⟩ := exp_bounds hs_nn hs14 hs₁_le
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith only [hdenom₁_lb]
  have hcubic_div_bound : 10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 := by
    rw [div_le_iff₀ hdenom₁]
    have hs₁3 : s₁ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs₁_nn hs₁_le 3
    have h1 : 10 * s₁ ^ 3 ≤ 10 * s ^ 3 := mul_le_mul_of_nonneg_left hs₁3 (by norm_num)
    have h2 : 160 / 11 * s ^ 3 * (11 / 16) = 10 * s ^ 3 := by ring
    have h3 : 160 / 11 * s ^ 3 * (11 / 16) ≤ 160 / 11 * s ^ 3 * (2 - Real.exp s₁) :=
      mul_le_mul_of_nonneg_left hdenom₁_lb (by positivity)
    linarith only [h1, h2, h3]
  refine ⟨hdenom₁_lb, hcubic_div_bound, ?_⟩
  have h1 : s ^ 2 / 8 ≤ s / 32 := by linarith only [hs2_le]
  have h2 : 160 / 11 * s ^ 3 ≤ 10 / 11 * s := by
    have h3 : s ^ 3 ≤ s / 16 := by linarith only [hs3_le, hs2_le]
    linarith only [h3]
  linarith only [h1, h2, hs_nn]

/-! ### Norm control for two consecutive BCH applications -/

section Norm

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

/-- Multiplication by the rational half contracts the norm by at least a factor of two. -/
lemma norm_half_smul_le (a : A) : ‖(2 : ℚ)⁻¹ • a‖ ≤ ‖a‖ / 2 := by
  calc
    _ ≤ ‖(2 : ℚ)⁻¹‖ * ‖a‖ := norm_smul_le _ _
    _ = ‖a‖ / 2 := by norm_num [← Rat.norm_cast_real, div_eq_mul_inv, mul_comm]

/-- A half-scaled first input satisfies the weighted bound for nested BCH. -/
lemma two_mul_norm_half_smul_add_norm_le (a b : A) :
    2 * ‖(2 : ℚ)⁻¹ • a‖ + ‖b‖ ≤ ‖a‖ + ‖b‖ := by
  have h := norm_half_smul_le a
  linarith only [h]

/-- The half-scaled commutator is bounded by the product of the two input norms. -/
lemma norm_half_commutator_le (x y : A) :
    ‖(2 : ℚ)⁻¹ • (x * y - y * x)‖ ≤ ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ‖x * y - y * x‖ / 2 := norm_half_smul_le _
    _ ≤ (‖x * y‖ + ‖y * x‖) / 2 :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ ≤ (‖x‖ * ‖y‖ + ‖y‖ * ‖x‖) / 2 :=
      div_le_div_of_nonneg_right (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) (by norm_num)
    _ = ‖x‖ * ‖y‖ := by ring

variable [CompleteSpace A] [NormOneClass A]

/-- A weighted input bound controls the norm of the pair for a second BCH application. -/
lemma norm_bch_add_norm_le_two_mul (x y : A) {s : ℝ}
    (hxy : 2 * ‖x‖ + ‖y‖ ≤ s) (hs : s < 1 / 4) :
    ‖bch x y‖ + ‖x‖ ≤ 2 * s := by
  let s₁ := ‖x‖ + ‖y‖
  have hs0 : 0 ≤ s := (by positivity : 0 ≤ 2 * ‖x‖ + ‖y‖).trans hxy
  have hs₁0 : 0 ≤ s₁ := add_nonneg (norm_nonneg x) (norm_nonneg y)
  have hs₁ : s₁ ≤ s := by
    dsimp [s₁]
    linarith only [hxy, norm_nonneg x]
  have hs₁_log : s₁ < Real.log 2 := by
    have hhalf := half_lt_log_two
    linarith only [hs₁, hs, hhalf]
  obtain ⟨_, hcubic, hscale⟩ := bch_scale_bounds hs0 hs hs₁0 hs₁
  have herr := norm_bch_sub_add_sub_bracket_le x y hs₁_log
  have hδ : ‖bch x y - (x + y)‖ ≤ ‖x‖ * ‖y‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    have hdecomp : bch x y - (x + y) =
        (bch x y - (x + y) - (2 : ℚ)⁻¹ • (x * y - y * x)) +
          (2 : ℚ)⁻¹ • (x * y - y * x) := by abel
    rw [hdecomp]
    exact (norm_add_le_of_le herr (norm_half_commutator_le x y)).trans_eq (by ring)
  have hz : ‖bch x y‖ ≤ s₁ + ‖x‖ * ‖y‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    have hdecomp : bch x y = (bch x y - (x + y)) + (x + y) := by abel
    rw [hdecomp]
    have hsum : ‖x + y‖ ≤ s₁ := norm_add_le _ _
    exact (norm_add_le_of_le hδ hsum).trans_eq (by ring)
  have hprod : ‖x‖ * ‖y‖ ≤ s ^ 2 / 8 := by
    have hsq : (2 * ‖x‖ + ‖y‖) ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (by positivity) hxy 2
    have hgm := four_mul_le_sq_add (2 * ‖x‖) ‖y‖
    nlinarith only [hsq, hgm]
  calc
    _ ≤ (s₁ + ‖x‖) + (‖x‖ * ‖y‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁)) := by
      linarith only [hz]
    _ ≤ s + (s ^ 2 / 8 + 160 / 11 * s ^ 3) := by
      dsimp only [s₁] at *
      linarith only [hxy, hprod, hcubic]
    _ ≤ 2 * s := by linarith only [hscale]

/-- The weighted input bound places the outer BCH pair in the logarithm convergence range. -/
lemma norm_bch_add_norm_lt_log_two (x y : A) {s : ℝ}
    (hxy : 2 * ‖x‖ + ‖y‖ ≤ s) (hs : s < 1 / 4) :
    ‖bch x y‖ + ‖x‖ < Real.log 2 := by
  have hnorm := norm_bch_add_norm_le_two_mul x y hxy hs
  have hhalf := half_lt_log_two
  linarith only [hnorm, hs, hhalf]

end Norm

end FQFP.BCH

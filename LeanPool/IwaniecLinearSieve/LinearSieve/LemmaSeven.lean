/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.LinearSieve.Defs
public import LeanPool.IwaniecLinearSieve.SieveFunctions.LemmaFive
import LeanPool.IwaniecLinearSieve.LinearSieve.Calculus
import LeanPool.IwaniecLinearSieve.SieveMajorants.Delay
import LeanPool.IwaniecLinearSieve.SieveMajorants.Lemmas
import LeanPool.IwaniecLinearSieve.SieveMajorants.Properties
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev

/-!
# [I71, Lemma 7]: `f_r(s) < M(s) < 4 𝔐(s)` for `s ≥ 2`

Here `M = MSieve = f + F + (3 - ·)⁺`. On `[2, 3]`, `M(s) = (F(3) + 3)(1 - log (s - 1))` by (3.9),
and `F(3) + 3 < 4` by `fSieve_four_add`. For `s > 3` we follow [I71]: at a first crossing `s`,
`(s-1) M(s) = ∫_{s-1}^s M ≤ 4 ∫_{s-1}^s 𝔐 ≤ 4 (s-1)² 𝔐(s) / s < 4 (s-1) 𝔐(s)`, using
`lemma5Q = 0` and (3.12).

The bound `M(s) ≤ 4𝔐(s)` fails for `s < 2`, where `M(s) = 5 + F(3) - s` grows and `𝔐 = 3`.

Consequences used in the induction of [I71, §4] (with Lemma 8 and the Corollary to Lemma 6):
`mainMaj_le_errMaj : 2 ≤ s → M lower (s) ≤ 12 G lower' (s)` and
`mainMaj_sub_one_le : 1 ≤ s → M lower (s - 1) ≤ 48 s² G lower' (s)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- `F(3) + 3 < 4`, from `f(4) + (F(3) + 3) log 3 = 4`. -/
theorem FSieve_three_add_lt_four : FSieve 3 + 3 < 4 := by
  have h := fSieve_four_add
  have h4 := fSieve_pos 4
  have hl := one_lt_log_three
  have hK : 0 < FSieve 3 + 3 := by linarith [FSieve_nonneg 3]
  nlinarith

theorem MSieve_eq_on_Icc {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    MSieve s = (FSieve 3 + 3) * (1 - log (s - 1)) := by
  rw [MSieve_of_le_three hs.2, fSieve_eq_on_Icc ⟨hs.1, by linarith [hs.2]⟩]; ring

theorem MSieve_lt_four_mul_bigM_of_le_three {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    MSieve s < 4 * bigM s := by
  rw [MSieve_eq_on_Icc hs, bigM_eq hs.1 hs.2]
  have h1 : 0 < s - 1 := by linarith [hs.1]
  have hl0 : 0 ≤ log (s - 1) := log_nonneg (by linarith [hs.1])
  have hl1 : log (s - 1) < 1 := by
    rw [log_lt_iff_lt_exp h1]; linarith [hs.2, exp_one_gt_d9]
  have hK := FSieve_three_add_lt_four
  have hinv : 0 < 1 / (s - 1) := by positivity
  nlinarith

/-- `(s - 1) M(s) = ∫_{s-1}^s M` for `s ≥ 3` (this is `lemma5Q s = 0`). -/
theorem sub_one_mul_MSieve {s : ℝ} (hs : 3 ≤ s) :
    (s - 1) * MSieve s = ∫ x in (s - 1)..s, MSieve x := by
  have h := lemma5Q_const hs
  rw [lemma5Q_three, lemma5Q] at h
  linarith

/-- `∫_{s-1}^s 𝔐 ≤ (s-1)² 𝔐(s)/s` for `s ≥ 3`, from (3.12). -/
theorem integral_bigM_le {s : ℝ} (hs : 3 ≤ s) :
    ∫ x in (s - 1)..s, bigM x ≤ (s - 1) ^ 2 * bigM s / s := by
  have hs0 : 0 < s := by linarith
  have hc : 0 < 1 - 1 / (2 * (s - 1) ^ 2) := by
    have : 1 / (2 * (s - 1) ^ 2) < 1 := by
      rw [div_lt_one (by nlinarith)]; nlinarith
    linarith
  have hle : ∫ x in (s - 1)..s, (1 - 1 / (2 * (s - 1) ^ 2)) * bigM x ≤
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (continuous_bigM.intervalIntegrable _ _ |>.const_mul _)
      ((continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)) fun x hx => ?_
    have hx1 : 0 < s - 1 := by linarith
    have : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have := hx.1; nlinarith
    exact mul_le_mul_of_nonneg_right (by linarith) (bigM_pos x).le
  rw [intervalIntegral.integral_const_mul, ← bigM_integral_identity hs] at hle
  have hkey : (1 - 1 / (2 * (s - 1) ^ 2)) * ((s - 1) ^ 2 * bigM s / s) =
      ((s - 1) ^ 2 - 1 / 2) * bigM s / s := by
    have h0 : s - 1 ≠ 0 := by linarith
    have : (1 - 1 / (2 * (s - 1) ^ 2)) * (s - 1) ^ 2 = (s - 1) ^ 2 - 1 / 2 := by
      field_simp
    calc _ = ((1 - 1 / (2 * (s - 1) ^ 2)) * (s - 1) ^ 2) * bigM s / s := by ring
      _ = _ := by rw [this]
  rw [← hkey] at hle
  exact le_of_mul_le_mul_left hle hc

/-- [I71, Lemma 7], upper bound: `M(s) < 4 𝔐(s)` for `s ≥ 2`. -/
theorem MSieve_lt_four_mul_bigM {s : ℝ} (hs : 2 ≤ s) : MSieve s < 4 * bigM s := by
  rcases le_total s 3 with h3 | h3
  · exact MSieve_lt_four_mul_bigM_of_le_three ⟨hs, h3⟩
  refine sub_pos.1 <| pos_of_first_crossing (f := fun s => 4 * bigM s - MSieve s) (a₀ := 2)
    (a := 3) ((continuous_bigM.const_smul (4 : ℝ)).sub continuous_MSieve).continuousOn
    (fun x hx => (sub_pos.2 (MSieve_lt_four_mul_bigM_of_le_three hx)).le)
    (sub_pos.2 (MSieve_lt_four_mul_bigM_of_le_three ⟨by norm_num, le_rfl⟩)) ?_ s h3
  intro s hs3 hnn _
  have hs0 : 0 < s := by linarith
  have hint : ∫ x in (s - 1)..s, MSieve x ≤ ∫ x in (s - 1)..s, 4 * bigM x :=
    intervalIntegral.integral_mono_on (by linarith) (continuous_MSieve.intervalIntegrable _ _)
      ((continuous_bigM.intervalIntegrable _ _).const_mul _) fun x hx => by
        linarith [hnn x ⟨by linarith [hx.1], hx.2⟩]
  rw [intervalIntegral.integral_const_mul, ← sub_one_mul_MSieve hs3.le] at hint
  have hB := integral_bigM_le hs3.le
  have hMs := bigM_pos s
  have h1 : (s - 1) * MSieve s ≤ 4 * ((s - 1) ^ 2 * bigM s / s) := by nlinarith
  have h2 : 4 * ((s - 1) ^ 2 * bigM s / s) < (s - 1) * (4 * bigM s) := by
    rw [div_eq_mul_inv]
    have : (s - 1) * s⁻¹ < 1 := by rw [← div_eq_mul_inv, div_lt_one hs0]; linarith
    have hs1 : 0 < s - 1 := by linarith
    nlinarith [mul_pos hs1 hMs]
  have := lt_of_le_of_lt h1 h2
  have hs1 : 0 < s - 1 := by linarith
  nlinarith

/-- [I71, Lemma 7]: `f_r(s) < M(s) ≤ 4 𝔐(s)` for `s ≥ 2`. -/
theorem lemma7 (r : ℕ) {s : ℝ} (hs : 2 ≤ s) : fr r s < MSieve s ∧ MSieve s ≤ 4 * bigM s :=
  ⟨fr_lt_MSieve r s, (MSieve_lt_four_mul_bigM hs).le⟩

theorem mainMaj_lt_four_mul_bigM (lower : Bool) {s : ℝ} (hs : 2 ≤ s) :
    mainMaj lower s < 4 * bigM s :=
  (mainMaj_le_MSieve lower s).trans_lt (MSieve_lt_four_mul_bigM hs)

/-- `M lower (s) ≤ 12 G lower' (s)` for `s ≥ 2`. -/
theorem mainMaj_le_errMaj (lower lower' : Bool) {s : ℝ} (hs : 2 ≤ s) :
    mainMaj lower s ≤ 12 * errMaj lower' s := by
  linarith [mainMaj_lt_four_mul_bigM lower hs, (errMaj_mem lower' s).1]

/-- `M(s - 1) < 16 s² 𝔐(s)` for `s ≥ 3` (Lemmas 7 and 8). -/
theorem MSieve_sub_one_lt {s : ℝ} (hs : 3 ≤ s) : MSieve (s - 1) < 16 * s ^ 2 * bigM s := by
  have h1 := MSieve_lt_four_mul_bigM (s := s - 1) (by linarith)
  have h2 := bigM_sub_one_lt hs
  linarith

theorem bigM_three_gt : 3 / 2 < bigM 3 := by
  rw [bigM_three]; linarith [log_two_lt_d9]

/-- The comparison of Corollary 1's error term with the error majorant:
`M lower (s - 1) ≤ 48 s² G lower' (s)` for `s ≥ 1` (any flags). -/
theorem mainMaj_sub_one_le (lower lower' : Bool) {s : ℝ} (hs : 1 ≤ s) :
    mainMaj lower (s - 1) ≤ 48 * s ^ 2 * errMaj lower' s := by
  have hG := (errMaj_mem lower' s).1
  have hM := mainMaj_le_MSieve lower (s - 1)
  rcases le_total 3 s with h3 | h3
  · have := MSieve_sub_one_lt h3
    nlinarith
  · have h0 : MSieve (s - 1) ≤ MSieve 0 := MSieve_antitone (by linarith)
    rw [MSieve_of_le_three (s := 0) (by norm_num), fSieve_of_le_two (by norm_num),
      fSieve_two] at h0
    have hK := FSieve_three_add_lt_four
    have hB : bigM 3 ≤ bigM s := bigM_antitone h3
    have := bigM_three_gt
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    have : 24 ≤ 48 * s ^ 2 * errMaj lower' s := by nlinarith
    linarith

end IwaniecLinearSieve

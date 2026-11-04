/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.MultivariableComparison
public import Mathlib.Algebra.Order.Star.Real

/-! # Uniformity of the corrected comparison

The comparison constant is bounded using only total degree, growth parameters,
and the restricted bad discriminant, as required by the main theorem.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem scalarComparisonBound_one_le {B ε : ℝ} (hB : 0 ≤ B) (hε : ε < 1) (g C : ℕ) :
    1 ≤ scalarComparisonBound B ε g C := by
  apply Real.one_le_exp_iff.mpr
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) (Nat.cast_nonneg C)) hB
    · exact sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  · exact tsum_nonneg (fun n => by positivity)

/-- Monotonicity permits all coordinate exponents and root bounds to be
replaced by the same total-degree bound. -/
theorem scalarComparisonBound_mono {B ε₁ ε₂ : ℝ} (hB : 0 ≤ B) (hε : ε₁ ≤ ε₂)
    (hε₂ : ε₂ < 1) (g : ℕ) {C₁ C₂ : ℕ} (hC : C₁ ≤ C₂) :
    scalarComparisonBound B ε₁ g C₁ ≤ scalarComparisonBound B ε₂ g C₂ := by
  apply Real.exp_le_exp.mpr
  have hd₂ : 0 < 1 - (2 : ℝ) ^ (ε₂ - 1) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hr : (2 : ℝ) ^ (ε₁ - 1) ≤ (2 : ℝ) ^ (ε₂ - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hnum₁ : 0 ≤ 2 * ((2 : ℝ) ^ g - 1) * C₁ * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) (Nat.cast_nonneg C₁)) hB
  have hcoeff : 2 * ((2 : ℝ) ^ g - 1) * C₁ * B / (1 - (2 : ℝ) ^ (ε₁ - 1)) ≤
      2 * ((2 : ℝ) ^ g - 1) * C₂ * B / (1 - (2 : ℝ) ^ (ε₂ - 1)) := by
    apply (div_le_div_of_nonneg_left hnum₁ hd₂ (by linarith)).trans
    apply div_le_div_of_nonneg_right _ hd₂.le
    apply mul_le_mul_of_nonneg_right _ hB
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hC)
      (mul_nonneg (by norm_num) (sub_nonneg.mpr (one_le_pow₀ (by norm_num))))
  have hsum : (∑' n : ℕ, (n : ℝ) ^ (ε₁ - 2)) ≤ ∑' n : ℕ, (n : ℝ) ^ (ε₂ - 2) := by
    apply Summable.tsum_le_tsum _ (Real.summable_nat_rpow.mpr (by linarith))
      (Real.summable_nat_rpow.mpr (by linarith))
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero, Real.zero_rpow (by linarith : ε₁ - 2 ≠ 0),
        Real.zero_rpow (by linarith : ε₂ - 2 ≠ 0), le_refl]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
        (by linarith)
  exact mul_le_mul hcoeff hsum (tsum_nonneg (fun n => by positivity))
    (div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))) (Nat.cast_nonneg C₂)) hB) hd₂.le)

/-- The constant depends on the polynomial system only through degree and
restricted discriminant. -/
noncomputable def totientComparisonBound (B ε : ℝ) (g D : ℕ) : ℝ :=
  scalarComparisonBound B ((g : ℝ) * ε) g (max g (D ^ 3)) ^ g

theorem totientComparisonBound_pos (B ε : ℝ) (g D : ℕ) : 0 < totientComparisonBound B ε g D :=
  pow_pos (scalarComparisonBound_pos _ _ _ _) _

theorem PolynomialSystem.totient_comparison_uniform {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hgε : (P.total.natDegree : ℝ) * ε < 1) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, NairTenenbaum.weight P.exponent P.discriminant F
      (fun i m => P.rootVector i m * totientTwist P.total.natDegree m) n) ≤
      totientComparisonBound B ε P.total.natDegree P.badDiscriminant *
        ∑ n ∈ positiveUpTo x, P.weight F n := by
  have hγε (i : Fin r) : (totalExponent P.exponent i : ℝ) * ε ≤ (P.total.natDegree : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast P.totalExponent_le_degree i) hε.le
  refine (P.totient_comparison hF hA hB hε (fun i => (hγε i).trans_lt hgε)
    P.total.natDegree x).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  calc
    _ ≤ ∏ _i : Fin r, scalarComparisonBound B ((P.total.natDegree : ℝ) * ε)
        P.total.natDegree (max P.total.natDegree (P.badDiscriminant ^ 3)) := by
      apply Finset.prod_le_prod₀ (fun i _ => (scalarComparisonBound_pos _ _ _ _).le)
      intro i _
      apply scalarComparisonBound_mono (zero_le_one.trans hB) (hγε i) hgε
      exact max_le_max (Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero)
          le_rfl
    _ ≤ _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, totientComparisonBound]
      exact pow_le_pow_right₀ (scalarComparisonBound_one_le (zero_le_one.trans hB) hgε _ _)
        P.factor_count_le_degree

/-- The small-exponent condition needed by the comparison follows from the
parameters of Theorem 1. -/
theorem comparison_exponent_of_theoremOne {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 < ε) (hεg : ε < 1 / (8 * (g : ℝ) ^ 2)) (hδ : δ ≤ 1) :
    (g : ℝ) * (ε * δ / 3) < 1 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hc : ε * (8 * (g : ℝ) ^ 2) < 1 :=
    (lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (g : ℝ) ^ 2)).mp hεg
  have hgg : (g : ℝ) ≤ 8 * (g : ℝ) ^ 2 := by nlinarith
  have he : ε * (g : ℝ) < 1 :=
    (mul_le_mul_of_nonneg_left hgg hε.le).trans_lt hc
  have hδ' : ε * δ / 3 ≤ ε := by nlinarith
  exact (mul_le_mul_of_nonneg_left hδ' (by positivity)).trans_lt (by nlinarith)

/-- The comparison is directly available with Theorem 1's admissibility
exponent; the extra local convergence condition is fully discharged. -/
theorem PolynomialSystem.totient_comparison_theoremOne_parameters {k r : ℕ} (P : PolynomialSystem
    k r)
    {A B ε δ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B (ε * δ / 3) F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hg : 0 < P.total.natDegree) (hε : 0 < ε)
    (hεg : ε < 1 / (8 * (P.total.natDegree : ℝ) ^ 2)) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, NairTenenbaum.weight P.exponent P.discriminant F
      (fun i m => P.rootVector i m * totientTwist P.total.natDegree m) n) ≤
      totientComparisonBound B (ε * δ / 3) P.total.natDegree P.badDiscriminant *
        ∑ n ∈ positiveUpTo x, P.weight F n :=
  P.totient_comparison_uniform hF hA hB (by positivity)
    (comparison_exponent_of_theoremOne hg hε hεg hδ₁) x

end NairTenenbaum

/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.SmallDivisorSieve

/-! # Uniform comparison with an independent totient exponent

Prime arguments add one totient power without changing the original
polynomial degrees or the admissibility exponent. Keeping these parameters
separate avoids imposing a stronger growth assumption on the arithmetic map.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The comparison constant for a separately specified totient exponent. -/
noncomputable def totientExponentComparisonBound (B ε : ℝ) (g h D : ℕ) : ℝ :=
  scalarComparisonBound B ((g : ℝ) * ε) h (max g (D ^ 3)) ^ g

theorem totientExponentComparisonBound_pos (B ε : ℝ) (g h D : ℕ) :
    0 < totientExponentComparisonBound B ε g h D :=
  pow_pos (scalarComparisonBound_pos _ _ _ _) _

/-- The degree and twist exponent are independent. Uniformity uses only
the degree bound, twist exponent, growth parameters, and bad discriminant. -/
theorem PolynomialSystem.totient_comparison_uniform_exponent {k r : ℕ}
    (P : PolynomialSystem k r) {g : ℕ} (hdeg : P.total.natDegree ≤ g)
    {A B ε : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hgε : (g : ℝ) * ε < 1)
    (h : ℕ) (x : ℝ) :
    (∑ n ∈ positiveUpTo x, NairTenenbaum.weight P.exponent P.discriminant F
      (fun i m => P.rootVector i m * totientTwist h m) n) ≤
      totientExponentComparisonBound B ε g h P.badDiscriminant *
        ∑ n ∈ positiveUpTo x, P.weight F n := by
  have hγε (i : Fin r) : (totalExponent P.exponent i : ℝ) * ε ≤ (g : ℝ) * ε :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast (P.totalExponent_le_degree i).trans hdeg) hε.le
  refine (P.totient_comparison hF hA hB hε (fun i => (hγε i).trans_lt hgε) h x).trans ?_
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  calc
    _ ≤ ∏ _i : Fin r, scalarComparisonBound B ((g : ℝ) * ε) h
        (max g (P.badDiscriminant ^ 3)) := by
      apply prod_le_prod₀ (fun i _ => (scalarComparisonBound_pos _ _ _ _).le)
      intro i _
      apply scalarComparisonBound_mono (zero_le_one.trans hB) (hγε i) hgε
      exact max_le_max
        ((Polynomial.natDegree_le_of_dvd (P.factor_dvd_total i) P.total_ne_zero).trans hdeg) le_rfl
    _ ≤ _ := by
      simp only [prod_const, card_univ, Fintype.card_fin, totientExponentComparisonBound]
      exact pow_le_pow_right₀ (scalarComparisonBound_one_le (zero_le_one.trans hB) hgε _ _)
        (P.factor_count_le_degree.trans hdeg)

theorem PolynomialSystem.totient_tuple_sum_le_exponent {k r : ℕ}
    (P : PolynomialSystem k r) {g : ℕ} (hdeg : P.total.natDegree ≤ g)
    {A B ε : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hgε : (g : ℝ) * ε < 1)
    (h : ℕ) (N : ℕ+) :
    (∑ v ∈ weightUpTo P.exponent P.discriminant N,
      rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist h (v i)) ≤
      totientExponentComparisonBound B ε g h P.badDiscriminant *
        ∑ n ∈ Icc 1 N, P.weight F n := by
  have H := P.totient_comparison_uniform_exponent hdeg hF hA hB hε hgε h (N : ℝ)
  rw [positiveUpTo_pnat] at H
  rw [← sum_weight_twist_eq_sum_weightUpTo P.exponent P.exponent_pos]
  exact H

end NairTenenbaum

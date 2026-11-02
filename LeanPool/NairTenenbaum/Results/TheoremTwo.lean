/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Results.TheoremTwoDivisorHits
public import LeanPool.NairTenenbaum.Results.TheoremTwoLogGain
public import LeanPool.NairTenenbaum.Results.TheoremTwoRoughMass
public import LeanPool.NairTenenbaum.Results.TheoremTwoValueBounds

/-! # Theorem 2: a large prime factor in a short polynomial-value product

The sharp small-prime logarithmic estimate leaves a linear error in the rough
mass. The unconditional divisor-hit estimate absorbs that error and supplies
the logarithmic exponential gain, with the strict exponent margin in the paper.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Real Finset Filter
open scoped Topology

theorem theoremTwo : TheoremTwo := by
  intro Q hQ hdeg k hk α hα
  have hk2 : 2 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hD : 0 < (k : ℝ) - 1 := by linarith
  let β : ℝ := (Q.natDegree : ℝ) / k
  have hβ : 0 < β := div_pos (by exact_mod_cast hdeg) hk0
  obtain ⟨η, hη, hη1, hαη⟩ := exists_divisorHit_exponent_margin_lt_one hα
  obtain ⟨A, C, hA1, hC1, hAC, hAC', Hsize⟩ := exists_theoremTwo_value_cutoff hk
  obtain ⟨x₁, B, hx₁, hB, HM⟩ := exists_theoremTwo_roughLogMass_lower_bound hQ hdeg hk hC1
  obtain ⟨c, x₂, hc, hx₂, HH⟩ := exists_theoremTwo_divisorHit_bound hQ hdeg hk hη
  obtain ⟨x₃, _, Hnonzero⟩ := exists_polynomial_eval_nonzero_on_shortInterval hQ.ne_zero
  have hgain := eventually_divisorHit_log_gain (B := B) hβ hc hη1 hD
  have hcoef : 0 < c * β / (4 * ((k : ℝ) - 1)) := by positivity
  have hstrict := eventually_greatestPrimeFactor_gain hαη hcoef
  have Hfinal : ∀ᶠ x : ℝ in atTop,
      let y : ℝ := x ^ β
      y * Real.exp ((Real.log x) ^ α) < (polynomialGreatestPrimeFactor Q x y : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop x₁,
      eventually_gt_atTop x₂, eventually_gt_atTop x₃, hgain, hstrict]
      with x hx hx₁' hx₂' hx₃' HG HS
    let y : ℝ := x ^ β
    let S := shortInterval x y
    have hy1 : 1 < y := Real.one_lt_rpow hx hβ
    have hy0 : 0 < y := by linarith
    have hx0 : 0 ≤ x := by linarith
    have hcard : (0 : ℝ) < S.card := by
      have H := (shortInterval_card_bounds hx0 hy0.le).1
      change 0 < ((shortInterval x y).card : ℝ)
      linarith
    have hSne : S.Nonempty := card_pos.mp (Nat.cast_pos.mp hcard)
    have hvalues (n : ℕ) (hn : n ∈ S) : (positivePolynomialValue Q n : ℕ) = (Q.eval (n :
        ℤ)).natAbs :=
      positivePolynomialValue_eq (Hnonzero x y hx₃' n hn)
    have hhits : ((S.filter (fun n => 0 < dyadicDivisorCount (positivePolynomialValue Q n)
        y)).card : ℝ) =
        polynomialDivisorHitCount Q x y := by
      unfold polynomialDivisorHitCount
      congr 2
      apply filter_congr
      intro n hn
      rw [hvalues n hn]
    have hprod : (∏ n ∈ S, (positivePolynomialValue Q n : ℕ)) = polynomialValueProduct Q x y := by
      exact prod_congr rfl hvalues
    have Hsize' : ∀ n ∈ S, (positivePolynomialValue Q n : ℝ) ≤ A * y ^ k := by
      intro n hn
      rw [hvalues n hn]
      exact Hsize x hx.le n hn
    have HG' := HG (polynomialDivisorHitCount Q x y) S.card (HH x hx₂') hcard
      (shortInterval_card_le_twice hx0 hy1.le)
    have Herror : B * y ≤
        ((S.filter (fun n => 0 < dyadicDivisorCount (positivePolynomialValue Q n) y)).card : ℝ) *
          Real.log y / 2 := by
      rw [hhits]
      exact HG'.1
    have Hmax := maxPrimeFac_prod_ge_exp_divisorHits S hSne (positivePolynomialValue Q) hk2
      hy1.le hC1 hAC (hAC' hk2) Hsize' (HM x hx₁') Herror
    rw [hhits, hprod] at Hmax
    change y * Real.exp ((Real.log x) ^ α) < _
    apply HS y (polynomialGreatestPrimeFactor Q x y) hy0
    calc
      _ ≤ y * Real.exp ((polynomialDivisorHitCount Q x y : ℝ) * Real.log y /
          (2 * (((k : ℝ) - 1) * S.card))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr HG'.2) hy0.le
      _ ≤ _ := Hmax
  obtain ⟨X, HX⟩ := eventually_atTop.mp Hfinal
  refine ⟨max 2 X, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun x hx => ?_⟩
  exact HX x ((le_max_right _ _).trans hx.le)

end NairTenenbaum

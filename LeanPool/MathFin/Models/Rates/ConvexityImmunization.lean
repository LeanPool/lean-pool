/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.Immunization

/-!
# Second-order bond portfolio immunization

The first-order immunization in `Immunization.lean` only neutralizes
`∂(A - L)/∂r` at the current rate. Larger parallel rate shifts are picked up
by the second-order term `(1/2) ∂²(A - L)/∂r² · (Δr)²`, governed by the
**convexity** of the cash-flow stream.

For each ZCB: `∂² B/∂r² = (T - t)² · B`. For a portfolio:

  `Conv_P · P = ∑_i w_i · (T_i - t)² · exp(-r(T_i - t))`,

and the derivative `∂_r (-Dur_P · P) = Conv_P · P`.

Second-order immunization: matching duration-times-value makes `∂(A − L)/∂r`
vanish (`Immunization.lean`), and matching convexity-times-value makes
`∂²(A − L)/∂r²` vanish, so together they leave the surplus flat to second order
at the current rate.

## Main definitions

* `bondPortfolioConv`: the convexity-times-value `Conv_P · P` of the bond portfolio,
  `∑_i w_i · (T_i − t)² · exp(−r(T_i − t))`.

## Main results

* `hasDerivAt_bondPortfolioDur_r`: `∂_r (Dur_P · P) = −Conv_P · P`.
* `hasDerivAt_neg_bondPortfolioDur_r`: `∂_r (−Dur_P · P) = Conv_P · P`.
* `hasDerivAt_deriv_bondPortfolioValue_r`: `∂²P/∂r² = Conv_P · P`, for the value
  itself.
* `bondPortfolio_immunization_second_order`: matching convexity-times-value gives
  `∂² (A − L)/∂r² = 0`, for the surplus itself.

## References

* [Fabozzi, *Fixed Income Mathematics*][FabozziFIM], Ch 5
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 4.11

## Tags

second-order immunization, bond convexity, duration matching, asset–liability management,
bond portfolio, rate sensitivity, MSC 91G30, JEL G11, JEL G12
-/

@[expose] public section

namespace MathFin

open Real

/-- Convexity-times-value `Conv_P · P` of the bond portfolio:
`∑_i w_i · (T_i − t)² · exp(−r(T_i − t))`. -/
noncomputable def bondPortfolioConv
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (T i - t) ^ 2 * Real.exp (-(r * (T i - t)))

/-- **Derivative of duration-times-value w.r.t. rate**:
`∂_r (Dur_P · P) = −Conv_P · P`. -/
lemma hasDerivAt_bondPortfolioDur_r
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) :
    HasDerivAt (fun r' ↦ bondPortfolioDur s w T t r')
      (-bondPortfolioConv s w T t r) r := by
  unfold bondPortfolioDur bondPortfolioConv
  have h_each : ∀ i ∈ s, HasDerivAt
      (fun r' ↦ w i * (T i - t) * Real.exp (-(r' * (T i - t))))
      (-(w i * (T i - t) ^ 2 * Real.exp (-(r * (T i - t))))) r := by
    intro i _
    -- each summand's rate-derivative is the ZCB duration atom `ZCB.hasDerivAt_zcb_r`
    -- scaled by the duration weight `w i · (T i − t)`.
    have h := (hasDerivAt_zcb_r t (T i) r).const_mul (w i * (T i - t))
    simp only [zcb] at h
    convert h using 1; ring
  have h_raw := HasDerivAt.fun_sum h_each
  rw [Finset.sum_neg_distrib] at h_raw
  exact h_raw

/-- **The second-derivative formula**: the r-derivative of `∂P/∂r = −Dur_P · P` is
`Conv_P · P`. The second derivative of the value itself is
`hasDerivAt_deriv_bondPortfolioValue_r`. -/
lemma hasDerivAt_neg_bondPortfolioDur_r
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) :
    HasDerivAt (fun r' ↦ -bondPortfolioDur s w T t r')
      (bondPortfolioConv s w T t r) r :=
  (hasDerivAt_bondPortfolioDur_r s w T t r).neg.congr_deriv (neg_neg _)

/-- **Second derivative of portfolio value**: `∂²P/∂r² = Conv_P · P`, for the value itself:
`∂P/∂r = −Dur_P · P` at every rate (`hasDerivAt_bondPortfolioValue_r`), and its derivative is
the formula of `hasDerivAt_neg_bondPortfolioDur_r`. -/
theorem hasDerivAt_deriv_bondPortfolioValue_r {ι : Type*} (s : Finset ι) (w T : ι → ℝ)
    (t r : ℝ) :
    HasDerivAt (deriv fun r' ↦ bondPortfolioValue s w T t r') (bondPortfolioConv s w T t r) r :=
  hasDerivAt_deriv_of_eventually
    (.of_forall (hasDerivAt_bondPortfolioValue_r s w T t))
    (hasDerivAt_neg_bondPortfolioDur_r s w T t r)

/-- **Single-bond convexity**: a single-bond portfolio's convexity-times-value
equals `w · (T − t)² · exp(−r(T − t))`. -/
lemma bondPortfolio_single_bond_conv
    {ι : Type*} (i : ι) (w T : ι → ℝ) (t r : ℝ) :
    bondPortfolioConv {i} w T t r =
      w i * (T i - t) ^ 2 * Real.exp (-(r * (T i - t))) := by
  unfold bondPortfolioConv
  simp

/-- **Second-order immunization**: matching convexity-times-value gives
`∂²(P_A − P_L)/∂r² = 0` at the current rate, for the surplus itself. The second derivative of
each side is its convexity-times-value (`hasDerivAt_neg_bondPortfolioDur_r`), so matching those
cancels it. Matching duration-times-value is the separate first-order condition,
`bondPortfolio_immunization_first_order`. -/
theorem bondPortfolio_immunization_second_order {ι κ : Type*} (sA : Finset ι)
    (wA TA : ι → ℝ) (sL : Finset κ) (wL TL : κ → ℝ) (t r : ℝ)
    (h_match_conv : bondPortfolioConv sA wA TA t r = bondPortfolioConv sL wL TL t r) :
    HasDerivAt
      (deriv fun r' ↦ bondPortfolioValue sA wA TA t r' - bondPortfolioValue sL wL TL t r') 0 r :=
  hasDerivAt_deriv_of_eventually
    (.of_forall fun r' ↦
      (hasDerivAt_bondPortfolioValue_r sA wA TA t r').sub
        (hasDerivAt_bondPortfolioValue_r sL wL TL t r'))
    (((hasDerivAt_neg_bondPortfolioDur_r sA wA TA t r).sub
      (hasDerivAt_neg_bondPortfolioDur_r sL wL TL t r)).congr_deriv
        (sub_eq_zero_of_eq h_match_conv))

end MathFin

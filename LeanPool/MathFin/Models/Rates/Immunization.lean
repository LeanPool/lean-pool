/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.ZCB

/-!
# Bond portfolio immunization under a deterministic short rate

A portfolio of zero-coupon bonds with face values `w i` and maturities `T i`,
indexed by a finite set `s`:

  `P(r) = ∑_{i ∈ s} w_i · exp(−r · (T_i − t))`,   `t` fixed (today).

The Macaulay-duration-times-value of the portfolio is

  `D_P · P(r) = ∑_{i ∈ s} w_i · (T_i − t) · exp(−r · (T_i − t))`.

First-order rate sensitivity: `∂P/∂r = −D_P · P`.

A portfolio is **first-order immunized** against a liability `L(r)` with duration
`D_L` if the duration-weighted asset value matches that of the liability, in
which case `∂(P − L)/∂r = 0` at the current rate.

## Main definitions

* `bondPortfolioValue`: the value of a zero-coupon bond portfolio at rate `r`.
* `bondPortfolioDur`: the duration-times-value `D_P · P` of the bond portfolio.

## Main results

* `hasDerivAt_bondPortfolioValue_r`: `∂P/∂r = −D_P · P`.
* `bondPortfolio_single_bond_dur`: a single-bond portfolio's duration-value
  equals `w · (T − t) · exp(−r·(T − t))`, recovering the ZCB result in
  `ZCB.lean`.
* `bondPortfolio_immunization_first_order`: when the duration-weighted asset
  and liability values match, the net portfolio's first-order rate sensitivity
  is zero.

## References

* [Fabozzi, *Fixed Income Mathematics*][FabozziFIM], Ch 5
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 4
* [Redington (1952)][Redington1952]

## Tags

bond immunization, duration matching, asset–liability management, zero-coupon bond portfolio,
interest rate risk, Redington, MSC 91G30, JEL G11, JEL G12
-/

@[expose] public section

namespace MathFin

open Real

/-- Bond portfolio value at rate `r`. -/
noncomputable def bondPortfolioValue
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) : ℝ :=
  ∑ i ∈ s, w i * Real.exp (-(r * (T i - t)))

/-- Duration-times-value `D_P · P` of the bond portfolio. -/
noncomputable def bondPortfolioDur
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (T i - t) * Real.exp (-(r * (T i - t)))

/-- **First-order rate sensitivity**: `∂P/∂r = −D_P · P` (here equivalently
`−bondPortfolioDur`). -/
lemma hasDerivAt_bondPortfolioValue_r
    {ι : Type*} (s : Finset ι) (w T : ι → ℝ) (t r : ℝ) :
    HasDerivAt (fun r' ↦ bondPortfolioValue s w T t r')
      (-bondPortfolioDur s w T t r) r := by
  unfold bondPortfolioValue bondPortfolioDur
  have h_each : ∀ i ∈ s, HasDerivAt
      (fun r' ↦ w i * Real.exp (-(r' * (T i - t))))
      (-(w i * (T i - t) * Real.exp (-(r * (T i - t))))) r := by
    intro i _
    -- each summand's rate-derivative *is* the ZCB duration atom
    -- `ZCB.hasDerivAt_zcb_r` (face value `w i`, maturity `T i`), not a fresh chase.
    have h := (hasDerivAt_zcb_r t (T i) r).const_mul (w i)
    simp only [zcb] at h
    convert h using 1; ring
  have h_raw := HasDerivAt.fun_sum h_each
  rw [Finset.sum_neg_distrib] at h_raw
  exact h_raw

/-- **Single-bond portfolio duration**: matches the ZCB duration `(T − t)`. -/
lemma bondPortfolio_single_bond_dur
    {ι : Type*} (i : ι) (w T : ι → ℝ) (t r : ℝ) :
    bondPortfolioDur {i} w T t r =
      w i * (T i - t) * Real.exp (-(r * (T i - t))) := by
  unfold bondPortfolioDur
  simp

/-- Single-bond portfolio value matches the ZCB price `w · exp(−r(T − t))`. -/
lemma bondPortfolio_single_bond_value
    {ι : Type*} (i : ι) (w T : ι → ℝ) (t r : ℝ) :
    bondPortfolioValue {i} w T t r = w i * Real.exp (-(r * (T i - t))) := by
  unfold bondPortfolioValue
  simp

/-- **First-order immunization**: if the duration-weighted asset value equals
the duration-weighted liability value, then the net portfolio's first-order
rate sensitivity is zero. -/
lemma bondPortfolio_immunization_first_order
    {ι κ : Type*}
    (sA : Finset ι) (wA TA : ι → ℝ)
    (sL : Finset κ) (wL TL : κ → ℝ)
    (t r : ℝ)
    (h_match : bondPortfolioDur sA wA TA t r =
               bondPortfolioDur sL wL TL t r) :
    HasDerivAt (fun r' ↦
        bondPortfolioValue sA wA TA t r' -
        bondPortfolioValue sL wL TL t r')
      0 r := by
  have hA := hasDerivAt_bondPortfolioValue_r sA wA TA t r
  have hL := hasDerivAt_bondPortfolioValue_r sL wL TL t r
  have h := hA.sub hL
  rw [show (0 : ℝ) = -bondPortfolioDur sA wA TA t r - -bondPortfolioDur sL wL TL t r from by
    rw [h_match]; ring]
  exact h

end MathFin

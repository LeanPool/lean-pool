/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PutGreeks
public import LeanPool.MathFin.Models.BlackScholes.StrikeGreeks

/-!
# The put price's second strike-derivative

The put price's second `K`-derivative matches the call's:

  `∂²_K bsP = e^{-rτ} · ϕ(d₂) / (K σ √τ)`,

since `bsP(K) − bsV(K) = K · e^{-rτ} − S` is linear in `K`. A clean expression
of put-call symmetry at the strike-convexity level.

## Main results

* `hasDerivAt_bsP_KK`: the K-derivative of `e^{-rτ} · Φ(−d₂)` is
  `e^{-rτ} · ϕ(d₂) / (K σ √τ)` (PDF evenness `gaussianPDFReal_zero_one_neg` now lives
  in `Probability.Gaussian.StandardNormal`).
* `hasDerivAt_deriv_bsP_K`: `∂²_K bsP = e^{-rτ} · ϕ(d₂) / (K σ √τ)`, for the price
  itself.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 12.8

## Tags

strike convexity, Breeden–Litzenberger, put price second derivative, implied density, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open Real ProbabilityTheory

/-- **The put's second strike-derivative formula**: the K-derivative of
`∂_K bsP = e^{-rτ} · Φ(−d₂)` (from `Models.BlackScholes.StrikeGreeks`) is
`e^{-rτ} · ϕ(d₂) / (K σ √τ)`,
the call's value (`hasDerivAt_deriv_bsV_K`). The second derivative of the put price itself is
`hasDerivAt_deriv_bsP_K`. -/
private lemma hasDerivAt_bsP_KK {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k ↦ Real.exp (-(r * τ)) * Phi (-bsd2 S k r σ τ))
      (Real.exp (-(r * τ)) *
        gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
        (K * σ * Real.sqrt τ)) K := by
  have h_d2_K := hasDerivAt_bsd2_K S r σ τ hS hσ hτ hK
  have h_neg_d2 := h_d2_K.neg
  have h_Phi_neg_d2 := (hasDerivAt_Phi (-bsd2 S K r σ τ)).comp K h_neg_d2
  have h := h_Phi_neg_d2.const_mul (Real.exp (-(r * τ)))
  have h_pdf_sym : gaussianPDFReal 0 1 (-bsd2 S K r σ τ) =
      gaussianPDFReal 0 1 (bsd2 S K r σ τ) := gaussianPDFReal_zero_one_neg _
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  have h1 := h.congr_of_eventuallyEq
    (f₁ := fun k ↦ Real.exp (-(r * τ)) * Phi (-bsd2 S k r σ τ))
    (Filter.Eventually.of_forall fun x ↦ by simp only [Function.comp_def, Pi.neg_apply])
  refine h1.congr_deriv ?_
  rw [h_pdf_sym]
  field_simp

/-- **Second strike-derivative of the put**: `∂²P/∂K² = e^{-rτ} · ϕ(d₂) / (K σ √τ)`, for the
price itself: `∂_K bsP = e^{-rτ} Φ(−d₂)` on all of `K > 0` (`hasDerivAt_bsP_K`), and its
derivative is the formula of `hasDerivAt_bsP_KK`. -/
theorem hasDerivAt_deriv_bsP_K {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (deriv fun k ↦ bsP k r σ S τ)
      (Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) / (K * σ * Real.sqrt τ)) K :=
  hasDerivAt_deriv_of_eventually
    ((eventually_gt_nhds hK).mono fun _ hk ↦ hasDerivAt_bsP_K hS hσ hk hτ)
    (hasDerivAt_bsP_KK hS hσ hK hτ)

end MathFin

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call
public import LeanPool.MathFin.Models.BlackScholes.Forward

/-!
# Power options under the BS lognormal hypothesis

The `n`-th moment of `S_T` under `BSCallHyp` is

  `E_Q[S_T^n] = S_0^n · exp(n · r · T + n(n−1)/2 · σ²T)`,

and its discounted form is the *power-forward price*

  `e^{−rT} · E_Q[S_T^n] = S_0^n · exp((n−1) · r · T + n(n−1)/2 · σ²T)`.

Both are direct instances of the **affine-shifted standard-normal MGF**
`∫ exp(α + β · z) · pdf(0, 1, z) dz = exp(α + β²/2)` (proved in
`StandardGaussianMGF.lean`), with `α = n · (r − σ²/2) · T` and `β = n · σ · √T`.
The identity `α + β²/2 = n · r · T + n(n−1)/2 · σ²T` is the algebraic core; the
rest is the standard HasLaw transfer from `Z` to `gaussianReal 0 1`.

The moment itself, `nthMoment_terminal`, lives in `Models/BlackScholes/Forward.lean` (its `n = 1`
case is the forward price); this file discounts it.

## Main results

* `powerForward_price`: discounted power-forward price.

## References

* [Heynen and Kat (1996)][HeynenKat1996]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 26.10

## Tags

power option, power forward, lognormal moment, moment generating function, Gaussian MGF, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Power-forward price**: discounted `n`-th moment equals
`S_0^n · exp((n−1) · r · T + n(n−1)/2 · σ²T)`. Specialises to:
* `n = 0`: `e^{−rT}` (a unit-payoff at maturity is a zero-coupon bond).
* `n = 1`: `S_0` (discounted spot is a martingale: `e^{−rT} · E[S_T] = S_0`).
* `n = 2`: `S_0² · exp(rT + σ²T)` (the variance-relevant moment after
  subtracting the squared forward). -/
theorem powerForward_price
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)
    (h : BSCallHyp Q S_0 K r σ T Z) :
    Real.exp (-(r * T)) *
        (∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q) =
      S_0^n *
        Real.exp (((n : ℝ) - 1) * r * T +
                  (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T) := by
  rw [nthMoment_terminal n h, ← mul_assoc, mul_comm (Real.exp _) (S_0^n),
      mul_assoc, ← Real.exp_add]
  congr 2
  ring

end MathFin

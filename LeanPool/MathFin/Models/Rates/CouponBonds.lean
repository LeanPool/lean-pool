/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.ZCB

/-!
# Coupon bonds, annuities, and rate-curve identities

Extensions of the deterministic-short-rate framework in `ZCB.lean`:

* **Annuity closed form**: `A_n(c, r, Δt) = c · e^{-rΔt} · (1 − x^n) / (1 − x)`,
  with `x = e^{-rΔt}`. Standard geometric-series identity.
* **Forward / spot rate consistency under a flat curve**:
  `f(t, T) = -∂_T log B(t, T) = r` when `B(t, T) = e^{-r(T - t)}`. Under a flat
  curve the instantaneous forward rate equals the spot rate at every horizon.
* **Coupon bond strict-monotonicity in `r`**: for positive coupons paid at
  future times, the bond price is a strictly decreasing function of the yield,
  giving the standard YTM-uniqueness property at the parameter-monotonicity
  level.

## Main definitions

* `annuityValue`: the value of an annuity over `n` periods of length `Δt` with coupon `c` at rate
  `r`.

## Main results

* `annuityValue`, `annuityValue_closed_form`: definition and geometric-series
  closed form.
* `annuityValue_succ_mul_exp_sub`: one period of an annuity's value,
  `A_{m+1}·e^{rΔt} - A = A_m`.
* `hasDerivAt_neg_log_zcb_T`: `-∂_T log B(t, T) = r` (forward = spot under flat
  curve).
* `couponBondPrice_strictAnti`: bond price strictly decreasing in `r`, for
  positive coupons at future times.

## References

* [Fabozzi, *Fixed Income Mathematics*][FabozziFIM], Ch 2; Ch 3
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 4; Ch 4.5; Ch 4.7

## Tags

annuity, coupon bond, yield to maturity, flat curve, forward rate, geometric series, present value,
MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

open Real

/-- Annuity value over `n` periods of length `Δt`, coupon `c`, rate `r`. -/
noncomputable def annuityValue (n : ℕ) (c r Δt : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, c * Real.exp (-(r * ((↑i + 1) * Δt)))

/-- **Annuity closed form** via the geometric-series identity:
`A_n(c, r, Δt) = c · e^{-rΔt} · (1 − x^n) / (1 − x)`, with `x = e^{-rΔt}`. -/
lemma annuityValue_closed_form (n : ℕ) (c r Δt : ℝ)
    (h : Real.exp (-(r * Δt)) ≠ 1) :
    annuityValue n c r Δt =
      c * Real.exp (-(r * Δt)) *
        (1 - Real.exp (-(r * Δt)) ^ n) / (1 - Real.exp (-(r * Δt))) := by
  unfold annuityValue
  -- Rewrite each term: c · exp(-r(i+1)Δt) = c · exp(-rΔt) · exp(-rΔt)^i.
  have h_term : ∀ i ∈ Finset.range n,
      c * Real.exp (-(r * ((↑i + 1) * Δt))) =
        c * Real.exp (-(r * Δt)) * Real.exp (-(r * Δt)) ^ i := by
    intro i _
    rw [show -(r * ((↑i + 1) * Δt)) = -(r * Δt) + ↑i * (-(r * Δt)) from by ring]
    rw [Real.exp_add, Real.exp_nat_mul]
    ring
  rw [Finset.sum_congr rfl h_term]
  rw [← Finset.mul_sum]
  rw [geom_sum_eq h n]
  have h_one_minus_ne : 1 - Real.exp (-(r * Δt)) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm h)
  have h_x_minus_one_ne : Real.exp (-(r * Δt)) - 1 ≠ 0 := sub_ne_zero.mpr h
  field_simp
  ring

/-- One period of an annuity: carrying the value of `m + 1` payments forward one
period and paying the first leaves the value of the other `m`,
`A_{m+1}·e^{rΔt} - A = A_m`. -/
theorem annuityValue_succ_mul_exp_sub (m : ℕ) (A r Δt : ℝ) :
    annuityValue (m + 1) A r Δt * Real.exp (r * Δt) - A = annuityValue m A r Δt := by
  rw [annuityValue, annuityValue, Finset.sum_range_succ', add_mul, Finset.sum_mul,
    mul_assoc A, ← Real.exp_add]
  simp only [Nat.cast_zero, zero_add, one_mul, neg_add_cancel, Real.exp_zero, mul_one,
    add_sub_cancel_right]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- **Forward = spot under a flat curve**: under a constant short rate `r`, the
instantaneous forward rate `-∂_T log B(t, T)` equals `r` at every horizon. -/
lemma hasDerivAt_neg_log_zcb_T (r t T : ℝ) :
    HasDerivAt (fun T' ↦ -Real.log (zcb r t T')) r T := by
  have h_eq : ∀ T' : ℝ, -Real.log (zcb r t T') = r * (T' - t) := by
    intro T'
    change -Real.log (Real.exp (-(r * (T' - t)))) = r * (T' - t)
    rw [Real.log_exp]
    ring
  have h_lin : HasDerivAt (fun T' : ℝ ↦ r * (T' - t)) r T := by
    have h := ((hasDerivAt_id T).sub_const t).const_mul r
    simpa using h
  exact h_lin.congr_of_eventuallyEq (Filter.Eventually.of_forall h_eq)

/-- **Coupon bond strict-monotonicity in `r`** at a fixed cash-flow schedule:
if all coupons are positive and all payment times are strictly in the future,
the bond price is strictly decreasing in the yield. This is the parameter
form of the YTM-uniqueness property — any positive price corresponds to at
most one yield. -/
lemma couponBondPrice_strictAnti
    {ι : Type*} (s : Finset ι) (c T : ι → ℝ) (t : ℝ)
    (h_pos : ∀ i ∈ s, 0 < c i)
    (h_future : ∀ i ∈ s, t < T i)
    (h_nonempty : s.Nonempty) :
    StrictAnti (fun r ↦ ∑ i ∈ s, c i * Real.exp (-(r * (T i - t)))) := by
  intro r₁ r₂ hr
  apply Finset.sum_lt_sum_of_nonempty h_nonempty
  intro i hi
  have h_diff : 0 < T i - t := sub_pos.mpr (h_future i hi)
  have h_arg : -(r₂ * (T i - t)) < -(r₁ * (T i - t)) := by
    have : r₁ * (T i - t) < r₂ * (T i - t) := by
      exact mul_lt_mul_of_pos_right hr h_diff
    linarith
  have h_exp_lt : Real.exp (-(r₂ * (T i - t))) < Real.exp (-(r₁ * (T i - t))) :=
    Real.exp_lt_exp.mpr h_arg
  exact mul_lt_mul_of_pos_left h_exp_lt (h_pos i hi)

end MathFin

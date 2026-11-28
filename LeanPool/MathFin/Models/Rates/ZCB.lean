/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Analysis.DerivOfDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Fixed-income basics under a deterministic short rate

Closed-form identities for a zero-coupon bond with continuous compounding under
a constant short rate `r`:

  `B(t, T) = exp(-(r · (T - t)))`.

## Main definitions

* `zcb`: the continuous-compounding zero-coupon bond price `zcb r t T = exp (-(r * (T - t)))`
  under a constant short rate `r`.

## Main results

* `zcb_at_maturity`: `B(T, T) = 1`.
* `zcb_pos`: `B(t, T) > 0`; `positivity` proves it (`evalZcb`).
* `zcb_yield_eq_rate`: under a constant `r`, the yield-to-maturity equals `r`.
* `hasDerivAt_zcb_r`: `∂_r B(t, T) = -(T - t) · B(t, T)` — the bond duration is
  the time-to-maturity.
* `zcb_duration_eq_time_to_maturity`: `-∂_r B / B = T - t`.
* `hasDerivAt_deriv_zcb_r`: `∂²_r B(t, T) = (T - t)² · B(t, T)`.
* `zcb_convexity_eq_time_to_maturity_sq`: convexity `∂²_r B / B = (T - t)²`.

The model is purely deterministic; the Vasicek / CIR / HJM stochastic versions
would need Itô calculus.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 4.2; 4.8; 4.9

## Tags

zero-coupon bond, bond duration, bond convexity, constant short rate, yield to maturity, JEL G12,
MSC 91G30
-/

@[expose] public section

namespace MathFin

open Real

/-- Continuous-compounding zero-coupon bond price under a constant short rate. -/
noncomputable def zcb (r : ℝ) (t T : ℝ) : ℝ := Real.exp (-(r * (T - t)))

/-- The bond pays `1` at maturity. -/
lemma zcb_at_maturity (r T : ℝ) : zcb r T T = 1 := by
  unfold zcb
  rw [sub_self, mul_zero, neg_zero, Real.exp_zero]

/-- The bond is positive. `positivity` proves it (`evalZcb`). -/
lemma zcb_pos (r t T : ℝ) : 0 < zcb r t T := Real.exp_pos _

/-- Yield-to-maturity for a ZCB under a constant rate equals the rate. -/
lemma zcb_yield_eq_rate {r t T : ℝ} (htT : t < T) :
    -Real.log (zcb r t T) / (T - t) = r := by
  unfold zcb
  rw [Real.log_exp, neg_neg]
  have h_ne : T - t ≠ 0 := sub_ne_zero.mpr htT.ne'
  field_simp

/-- `∂_r B(t, T) = -(T - t) · B(t, T)`. Duration of a ZCB equals time-to-maturity. -/
lemma hasDerivAt_zcb_r (t T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' ↦ zcb r' t T) (-(T - t) * zcb r t T) r := by
  unfold zcb
  have h_lin : HasDerivAt (fun r' : ℝ ↦ -(r' * (T - t))) (-(T - t)) r := by
    have h := (hasDerivAt_id r).mul_const (T - t)
    rw [one_mul] at h
    exact h.neg
  have h := h_lin.exp
  convert h using 1
  ring

/-- ZCB Macaulay duration equals time-to-maturity: `-∂_r B / B = T - t`. -/
lemma zcb_duration_eq_time_to_maturity (t T r : ℝ) :
    -deriv (fun r' ↦ zcb r' t T) r / zcb r t T = T - t := by
  have h_ne : zcb r t T ≠ 0 := (zcb_pos r t T).ne'
  rw [(hasDerivAt_zcb_r t T r).deriv]
  field_simp

/-- The r-derivative of the duration formula `-(T - t) · B` is `(T - t)² · B`. The second
derivative of the price itself is `hasDerivAt_deriv_zcb_r`. -/
private lemma hasDerivAt_zcb_r_r (t T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' ↦ -(T - t) * zcb r' t T) ((T - t)^2 * zcb r t T) r := by
  have h := (hasDerivAt_zcb_r t T r).const_mul (-(T - t))
  rw [show (T - t) ^ 2 * zcb r t T = -(T - t) * (-(T - t) * zcb r t T) from by ring]
  exact h

/-- `∂²_r B(t, T) = (T - t)² · B(t, T)`, for the price itself: `∂_r B = -(T - t) · B` at every
rate (`hasDerivAt_zcb_r`). -/
theorem hasDerivAt_deriv_zcb_r (t T r : ℝ) :
    HasDerivAt (deriv fun r' ↦ zcb r' t T) ((T - t) ^ 2 * zcb r t T) r :=
  hasDerivAt_deriv_of_eventually (.of_forall (hasDerivAt_zcb_r t T)) (hasDerivAt_zcb_r_r t T r)

/-- ZCB convexity = squared time-to-maturity: `∂²_r B / B = (T - t)²`. -/
lemma zcb_convexity_eq_time_to_maturity_sq (t T r : ℝ) :
    deriv (deriv fun r' ↦ zcb r' t T) r / zcb r t T = (T - t)^2 := by
  have h_ne : zcb r t T ≠ 0 := (zcb_pos r t T).ne'
  rw [(hasDerivAt_deriv_zcb_r t T r).deriv]
  field_simp

end MathFin

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: a zero-coupon bond price `zcb r t T` is positive. -/
@[positivity MathFin.zcb _ _ _]
meta def evalZcb : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(MathFin.zcb $r $t $T) =>
    assertInstancesCommute
    pure (.positive q(MathFin.zcb_pos $r $t $T))
  | _, _, _ => throwError "not zcb"

end Mathlib.Meta.Positivity

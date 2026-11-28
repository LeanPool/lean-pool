/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reduced-form credit risk under constant hazard rate

The simplest credit-risk model assumes a constant hazard (default-intensity)
rate `h ≥ 0`. The survival probability between `t` and `T` is

  `S(t, T) = exp(-(h · (T - t)))`,

and the resulting credit spread (additional yield over the risk-free rate)
equals the hazard rate itself:

  `c(t, T) = -log(S(t, T)) / (T - t) = h`.

This is structurally identical to the ZCB-yield identity in `ZCB.lean`
(`zcb_yield_eq_rate`), with the hazard `h` playing the role of the risk-free
rate. The continuous-time stochastic-intensity model (Cox process / doubly
stochastic Poisson) is gated on the Itô integral and is not formalized here.

## Main definitions

* `survivalProbability`: the survival probability `exp(-(h · (T - t)))` under a constant hazard
  rate `h`.
* `cdsFairSpread`: the fair CDS spread `c = h · (1 − R)` under constant hazard with recovery `R`.

## Main results

* `survival_at_zero`: `S(T, T) = 1`.
* `survival_pos`: survival probability is positive.
* `creditSpread_eq_hazard`: under constant hazard, spread equals hazard.
* `survival_strictAnti_of_pos_hazard`: positive hazard → strictly decreasing
  survival in horizon `T`.

## References

* [Duffie and Singleton (1999)][DuffieSingleton1999]
* [Jarrow and Turnbull][JarrowTurnbull]
* [D. Lando, *Credit Risk Modeling*][Lando2004], Ch 5

## Tags

reduced-form credit risk, hazard rate, default intensity, credit spread, survival probability,
constant intensity, MSC 91G40, JEL G12
-/

@[expose] public section

namespace MathFin

open Real

/-- Survival probability under a constant hazard rate `h`. -/
noncomputable def survivalProbability (h t T : ℝ) : ℝ :=
  Real.exp (-(h * (T - t)))

/-- At `T = t`, survival is 1 (no time elapsed). -/
lemma survival_at_zero (h T : ℝ) : survivalProbability h T T = 1 := by
  unfold survivalProbability
  rw [sub_self, mul_zero, neg_zero, Real.exp_zero]

/-- Survival probability is strictly positive. -/
lemma survival_pos (h t T : ℝ) : 0 < survivalProbability h t T := Real.exp_pos _

/-- **Credit spread equals hazard rate** under constant hazard:
`-log(S(t, T)) / (T − t) = h`. -/
lemma creditSpread_eq_hazard {h t T : ℝ} (htT : t < T) :
    -Real.log (survivalProbability h t T) / (T - t) = h := by
  unfold survivalProbability
  rw [Real.log_exp, neg_neg]
  have h_ne : T - t ≠ 0 := sub_ne_zero.mpr htT.ne'
  field_simp

/-- **Positive hazard ⇒ strictly decreasing survival in horizon `T`**. -/
lemma survival_strictAnti_of_pos_hazard {h t : ℝ} (hh : 0 < h) :
    StrictAntiOn (fun T ↦ survivalProbability h t T) (Set.Ici t) := by
  intro T₁ _ T₂ _ hT
  unfold survivalProbability
  have h_arg : -(h * (T₂ - t)) < -(h * (T₁ - t)) := by
    have : h * (T₁ - t) < h * (T₂ - t) := by
      have : T₁ - t < T₂ - t := by linarith
      exact mul_lt_mul_of_pos_left this hh
    linarith
  exact Real.exp_lt_exp.mpr h_arg

/-! ## CDS fair spread with recovery (folded from `CDS.lean`)

A CDS exchanges a periodic premium `c` for `(1 − R)` at default. Under
constant hazard `h` and risk-free rate `r`, both legs share the annuity
factor `(1 − e^{−(r+h) T}) / (r + h)`. Equating PVs gives the fair spread
`c = h · (1 − R)`. Specialises to `c = h` (the bare `creditSpread_eq_hazard`)
at zero recovery. -/

/-- **Fair CDS spread under constant hazard with recovery**: `c = h · (1 − R)`. -/
noncomputable def cdsFairSpread (hh R : ℝ) : ℝ := hh * (1 - R)

/-- **Zero recovery specialisation**: the fair spread equals the hazard rate. -/
lemma cdsFairSpread_zero_recovery (hh : ℝ) : cdsFairSpread hh 0 = hh := by
  unfold cdsFairSpread; ring

/-- **Leg-equality characterisation**: with `factor` the common annuity factor,
the fair spread is the unique value equating premium and protection legs. -/
theorem cds_leg_equality (hh R factor c : ℝ) (h_factor_ne : factor ≠ 0) :
    c * factor = (1 - R) * hh * factor ↔ c = cdsFairSpread hh R := by
  unfold cdsFairSpread
  constructor
  · intro heq
    have := mul_right_cancel₀ h_factor_ne heq
    linarith
  · intro hc
    rw [hc]; ring

end MathFin

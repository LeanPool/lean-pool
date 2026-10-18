/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.ConsumptionFloor
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationLipschitz


/-!
# A natural asset bound for log utility

`exists_decline_of_consumption_lower_bound` turns a LINEAR lower bound on consumption into the
statement that assets above an explicit threshold decline — the natural asset bound, which is
what `assetCap` has been standing in for, and what
`not_concaveOn_consumptionFn_of_cap_binds` says has to hold before the Carroll–Kimball
hypothesis is even true. Its input, the linear bound, has been missing. This file supplies it
for log utility.

## The argument is the crudest possible deviation

Saving nothing is always feasible. Comparing the optimum with it,

  `u (resources) + β · cont 0 ≤ u (consumption) + β · cont (policy)`,

so `u resources - u consumption ≤ β (cont (policy) - cont 0) ≤ 2 β ‖V‖`. For LOG utility that
reads `log (resources / consumption) ≤ 2 β ‖V‖`, which is a linear bound outright:

  `consumption ≥ exp (-2 β ‖V‖) · resources`.

## Why this works for log and for nothing else

The deviation is informative only because log is UNBOUNDED ABOVE, so `u resources` grows without
limit and drags `u consumption` up with it. With CRRA `γ > 1` utility is bounded above, the same
comparison gives only `c^(1-γ)` bounded, hence a constant floor and no linear bound at all — the
crude deviation says nothing about rich households. That is another face of the same split
`crra_pinch` found, and it is the case the structure leaves us with anyway.

## What is honest about the constant

`exp (-2 β ‖V‖)` is very lossy. The sharp constant is Ma and Toda's asymptotic MPC
`c_bar = 1 - (β R^(1-γ))^(1/γ)`, at which the decline condition becomes exactly `β R < 1`
(`one_sub_mpc_mul_of_asymptotic`). Getting it needs the Euler equation, hence the envelope
condition, hence the machinery that `IncomeFluctuationEnvelope` supplies only under side
conditions. So the bound proved here is qualitatively right and quantitatively weak: it
establishes a natural asset bound, but only for interest rates small relative to `exp (-2 β ‖V‖)`,
where the sharp argument would ask only for impatience.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-- The slack in the "save nothing" comparison: twice the size of the value function, discounted. -/
noncomputable def deviationGap : ℝ := 2 * P.discount * ‖P.toExtended.valueFunction‖

theorem deviationGap_nonneg : 0 ≤ P.deviationGap := by
  have : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have := norm_nonneg P.toExtended.valueFunction
  simp only [deviationGap]
  positivity

/-- **The optimum beats saving nothing, so utility cannot fall far short of the utility of
eating everything.** This holds for any utility function; it is the log case that turns it into
a linear bound. -/
theorem utility_resources_sub_le {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.u (P.resources (a, z) - assetFloor) - P.u (P.consumptionFn z a) ≤ P.deviationGap := by
  have hmem0 : assetFloor ∈ P.toExtended.feasible (a, z) := ⟨le_rfl, le_max_left _ _⟩
  have hc0 : 0 < P.consumption (a, z) assetFloor := by
    have h1 := P.minConsumption_le_consumption_floor (a, z)
    have h2 := P.minConsumption_pos
    simp only [consumption]; linarith
  have hopt := P.objR_le_of_mem ha hmem0 (P.mem_dom_of_pos hc0)
  simp only [objR, consumption] at hopt
  have hb1 := abs_le.mp (P.abs_cont_le z (P.policy (a, z)))
  have hb2 := abs_le.mp (P.abs_cont_le z assetFloor)
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hgap : (P.discount : ℝ) * (P.cont z (P.policy (a, z)) - P.cont z assetFloor)
      ≤ P.deviationGap := by
    simp only [deviationGap]
    nlinarith [hb1.2, hb2.1, hβ]
  simp only [consumptionFn, consumption]
  nlinarith [hopt, hgap]

/-- **A linear lower bound on consumption, for log utility.** The one place the development gets
a bound that scales with resources rather than being a constant. -/
theorem log_consumption_linear_lower_bound (hpc : P.PositiveConsumption) (hu : P.u = Real.log)
    {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    Real.exp (-P.deviationGap) * (P.resources (a, z) - assetFloor) ≤ P.consumptionFn z a := by
  have hm : 0 < P.resources (a, z) - assetFloor := by
    have h1 := P.minConsumption_le_consumption_floor (a, z)
    have h2 := P.minConsumption_pos
    linarith
  have hc : 0 < P.consumptionFn z a := P.consumptionFn_pos hpc ha z
  have hkey := P.utility_resources_sub_le ha z
  rw [hu] at hkey
  have hdiv : Real.log ((P.resources (a, z) - assetFloor) / P.consumptionFn z a)
      ≤ P.deviationGap := by
    rw [Real.log_div hm.ne' hc.ne']
    exact hkey
  have hle : (P.resources (a, z) - assetFloor) / P.consumptionFn z a ≤ Real.exp P.deviationGap :=
    (Real.log_le_iff_le_exp (by positivity)).mp hdiv
  rw [div_le_iff₀ hc] at hle
  rw [Real.exp_neg]
  rw [inv_mul_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **The natural asset bound for log utility.** Assets above an explicit threshold decline, so
the household never accumulates without limit and the asset cap can be justified rather than
imposed.

The hypothesis on the interest rate is the price of the crude constant: the sharp argument would
ask only for `β (1 + r) < 1`. -/
theorem exists_natural_asset_bound_log (hpc : P.PositiveConsumption) (hu : P.u = Real.log)
    (z : Z)
    (hr : (1 - Real.exp (-P.deviationGap)) * (1 + P.interest) < 1) :
    ∃ ā : ℝ, ∀ a ∈ Icc assetFloor assetCap, ā < a → P.policy (a, z) < a :=
  P.exists_decline_of_consumption_lower_bound hr
    fun _ ha => P.log_consumption_linear_lower_bound hpc hu ha z

/-! ### A better constant, from a smaller deviation

`log_consumption_linear_lower_bound` compares the optimum with saving NOTHING, which is a huge
deviation and costs an exponential: `ε = exp (-2 β ‖V‖)`. Comparing instead with saving a
FRACTION `θ` of the optimum costs only a ratio, and letting `θ` approach one turns the bound
polynomial:

  `consumption ≥ resources / (1 + 2 · 2 β ‖V‖)`.

No derivative is taken. The reason a near-zero deviation is affordable is that BOTH sides shrink
with `1 - θ`: the utility gain is `log (1 + (1-θ) b / c)`, and the continuation loss is bounded by
`2‖V‖ (1-θ) / θ` because concavity makes the slope of `cont` on `[θb, b]` no larger than its slope
on `[0, θb]`. The factor `(1-θ)` cancels, and what survives is the comparison of the two
constants.

`θ = (G + 1/2) / (1 + G)` is chosen so that `θ (1 + G) - G = 1/2` exactly, which is what makes the
final inequality `b ≤ 2 G c`.

The gain is small when `‖V‖` is small and large when it is not: at `G = 1.3` the two constants are
`0.27` and `0.28`, at `G = 5` they are `0.007` and `0.09`. Since `‖V‖` grows like `|log minIncome|`,
it is the dispersed calibrations — the ones the precautionary motive needs — where this matters.
-/

/-- `log (c + d) - log c ≥ d / (c + d)`, the elementary inequality behind the bound. -/
theorem log_sub_log_ge {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    d / (c + d) ≤ Real.log (c + d) - Real.log c := by
  have hcd : 0 < c + d := by linarith
  have h := Real.log_le_sub_one_of_pos (x := c / (c + d)) (by positivity)
  rw [Real.log_div hc.ne' hcd.ne'] at h
  have he : c / (c + d) - 1 = -(d / (c + d)) := by field_simp; ring
  rw [he] at h
  linarith

/-- The arithmetic behind `b ≤ 2 G c`, isolated so the search stays small. -/
private theorem two_gap_cancel {B G c θ : ℝ} (hθkey : θ * (1 + G) - G = 1 / 2)
    (hcancel : θ * B ≤ G * (c + (1 - θ) * B)) : B ≤ 2 * G * c := by
  have h : B * (θ * (1 + G) - G) = B * (1 / 2) := by rw [hθkey]
  linarith [hcancel, h]

/-- **A polynomial linear lower bound on consumption.** Sharper than
`log_consumption_linear_lower_bound` whenever the value function is large, and proved from a
deviation to `θ` times the optimal saving rather than to zero. -/
theorem log_consumption_linear_lower_bound' (hpc : P.PositiveConsumption) (hu : P.u = Real.log)
    {a : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    (P.resources (a, z) - assetFloor) / (1 + 2 * P.deviationGap) ≤ P.consumptionFn z a := by
  have hres0 : P.resources (a, z) = P.consumptionFn z a + P.policy (a, z) := by
    simp only [consumptionFn, consumption]; ring
  have hc0 : 0 < P.consumptionFn z a := P.consumptionFn_pos hpc ha z
  set G : ℝ := P.deviationGap with hGdef
  have hG : 0 ≤ G := P.deviationGap_nonneg
  set b : ℝ := P.policy (a, z) with hbdef
  set c : ℝ := P.consumptionFn z a with hcdef
  have hc : 0 < c := hc0
  have hres : P.resources (a, z) = c + b := hres0
  have hb2 : b - assetFloor ≤ 2 * G * c := by
    rcases eq_or_lt_of_le (P.policy_mem_region (a, z)).1 with hzero | hbpos
    · rw [← hbdef] at hzero
      rw [← hzero, sub_self]
      exact mul_nonneg (by linarith) hc.le
    rw [← hbdef] at hbpos
    have hbf : (0 : ℝ) < b - assetFloor := by linarith
    set θ : ℝ := (G + 1 / 2) / (1 + G) with hθdef
    have hden : (0 : ℝ) < 1 + G := by linarith
    have hθ0 : 0 < θ := by rw [hθdef]; positivity
    have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hden]; linarith
    have h1θ : (0 : ℝ) < 1 - θ := by linarith
    have hθkey : θ * (1 + G) - G = 1 / 2 := by rw [hθdef]; field_simp; ring
    have hbreg : b ∈ Icc assetFloor assetCap := P.policy_mem_region _
    have hmem0 : assetFloor ∈ Icc assetFloor assetCap := ⟨le_rfl, P.assetFloor_le_assetCap⟩
    -- deviate from `b` a fraction `1-θ` of the way back to the borrowing limit
    set d : ℝ := assetFloor + θ * (b - assetFloor) with hddef
    have hθb0 : assetFloor < d := by rw [hddef]; nlinarith
    have hθbb : d < b := by rw [hddef]; nlinarith
    have hfeas : d ∈ P.toExtended.feasible (a, z) := by
      rw [P.feasible_eq]
      exact ⟨by linarith, by linarith [(P.policy_mem (a, z)).2]⟩
    have hcons : P.consumption (a, z) d = c + (1 - θ) * (b - assetFloor) := by
      simp only [consumption, hddef]
      rw [hres]
      ring
    have hdpos : (0 : ℝ) ≤ (1 - θ) * (b - assetFloor) := mul_nonneg h1θ.le hbf.le
    have hcpos : 0 < P.consumption (a, z) d := by rw [hcons]; linarith
    have hopt := P.objR_le_of_mem ha hfeas (P.mem_dom_of_pos hcpos)
    simp only [objR, hcons, hu] at hopt
    rw [show P.consumption (a, z) (P.policy (a, z)) = c from rfl,
      show P.policy (a, z) = b from rfl] at hopt
    -- concavity bounds the continuation loss
    have hslope := (P.concaveOn_cont z).slope_anti_adjacent hmem0 hbreg hθb0 hθbb
    have hb1 := abs_le.mp (P.abs_cont_le z d)
    have hb0 := abs_le.mp (P.abs_cont_le z assetFloor)
    have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
    have hd1 : d - assetFloor = θ * (b - assetFloor) := by rw [hddef]; ring
    have hd2 : b - d = (1 - θ) * (b - assetFloor) := by rw [hddef]; ring
    have hloss : P.cont z b - P.cont z d
        ≤ 2 * ‖P.toExtended.valueFunction‖ * (1 - θ) / θ := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)] at hslope
      rw [hd1, hd2] at hslope
      rw [le_div_iff₀ hθ0]
      have hkey : (P.cont z b - P.cont z d) * θ * (b - assetFloor)
          ≤ 2 * ‖P.toExtended.valueFunction‖ * (1 - θ) * (b - assetFloor) := by
        nlinarith [hslope, hb1.2, hb0.1, hbf, h1θ]
      exact le_of_mul_le_mul_right hkey hbf
    have heq : (P.discount : ℝ) * (2 * ‖P.toExtended.valueFunction‖ * (1 - θ) / θ)
        = G * (1 - θ) / θ := by
      rw [hGdef, IncomeFluctuation.deviationGap]; ring
    have hβloss : (P.discount : ℝ) * (P.cont z b - P.cont z d) ≤ G * (1 - θ) / θ := by
      have hmul := mul_le_mul_of_nonneg_left hloss hβ
      linarith [hmul, heq.le, heq.ge]
    -- the utility gain
    have hgain := log_sub_log_ge hc hdpos
    have hdist : (P.discount : ℝ) * (P.cont z b - P.cont z d)
        = (P.discount : ℝ) * P.cont z b - (P.discount : ℝ) * P.cont z d := by ring
    have hchain : (1 - θ) * (b - assetFloor) / (c + (1 - θ) * (b - assetFloor))
        ≤ G * (1 - θ) / θ := by
      linarith [hopt, hβloss, hgain, hdist.le, hdist.ge]
    rw [div_le_div_iff₀ (by linarith) hθ0] at hchain
    have hcancel : θ * (b - assetFloor) ≤ G * (c + (1 - θ) * (b - assetFloor)) := by
      refine le_of_mul_le_mul_left ?_ h1θ
      nlinarith [hchain]
    exact two_gap_cancel hθkey hcancel
  rw [hres, div_le_iff₀ (by linarith)]
  linarith [hb2]

/-! ### The other half of exhaustion: the corner, for log

`exists_decline_of_consumption_lower_bound` gives assets falling above a threshold. The ergodic
argument also needs the constraint to BIND below one — `policy = 0` on `[0, a₀]` at the bad income
state — and `policy_eq_zero_of_corner_at` supplies that from two explicit constants: a Lipschitz
bound `L` on the value function and a lower bound `m` on the secant slope of `u`, with `β L < m`.

Both are computable for log. The secant slope of `log` on `(0, R]` is at least `1/R`, from
`log x ≤ x - 1`. The Lipschitz constant is the fixed point of the operator's own estimate,
`L = K (1+r) / (1 - β(1+r))` with `K = slopeBound log minIncome = 2 log 2 / minIncome`, so `β L < m`
reads

  `resources · β · 2 log 2 (1+r) / (minIncome (1 - β(1+r)))  <  1`,

a condition on the state's resources alone. Since resources at the bad state are
`minIncome + (1+r) a`, it cuts out an interval of low assets — exactly what the ergodic argument
wants, and exactly why the condition has to be state-dependent rather than global. -/

/-- The secant slope of `log` on `(0, R]` is at least `1 / R`. -/
theorem log_marginal_bound {R : ℝ} (hR : 0 < R) {c d : ℝ} (hd : 0 < d) (hdc : d ≤ c)
    (hcR : c ≤ R) : 1 / R * (c - d) ≤ Real.log c - Real.log d := by
  have hc : 0 < c := lt_of_lt_of_le hd hdc
  have hkey : Real.log (d / c) ≤ d / c - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hd hc)
  rw [Real.log_div hd.ne' hc.ne'] at hkey
  have hstep : (c - d) / c ≤ Real.log c - Real.log d := by
    rw [sub_div, div_self hc.ne']
    linarith
  refine le_trans ?_ hstep
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hR hc]
  nlinarith [sub_nonneg.mpr hdc]

/-- The slope bound of `log` at the income floor, in closed form. -/
theorem log_slopeBoundU (hu : P.u = Real.log) :
    P.slopeBoundU = 2 * Real.log 2 / P.minConsumption := by
  have hm := P.minConsumption_pos
  simp only [slopeBoundU, slopeBound, hu]
  rw [← Real.log_div hm.ne' (by positivity), show P.minConsumption / (P.minConsumption / 2) = 2 by
    field_simp]
  field_simp

/-- The Lipschitz constant the operator's own estimate is a fixed point of. -/
noncomputable def logLipschitz : ℝ :=
  2 * Real.log 2 / P.minConsumption * (1 + P.interest) / (1 - P.discount * (1 + P.interest))

theorem logLipschitz_nonneg (hβR : P.discount * (1 + P.interest) < 1) :
    0 ≤ P.logLipschitz := by
  have hm := P.minConsumption_pos
  have hr := P.interest_gt_neg_one
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine div_nonneg (by positivity) (by linarith)

/-- **The value function is Lipschitz with the explicit log constant.** -/
theorem log_valueFunction_lipschitz (hu : P.u = Real.log)
    (hβR : P.discount * (1 + P.interest) < 1) :
    ∀ z : Z, ∀ x ∈ Icc assetFloor assetCap, ∀ y ∈ Icc assetFloor assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)|
        ≤ P.logLipschitz * |x - y| := by
  refine P.valueFunction_lipschitz (P.logLipschitz_nonneg hβR) (le_of_eq ?_)
  have hne : (1 : ℝ) - P.discount * (1 + P.interest) ≠ 0 := by linarith
  simp only [logLipschitz, P.log_slopeBoundU hu]
  field_simp
  ring

/-- **The borrowing constraint binds where resources are small**, with an explicit threshold in
the primitives. -/
theorem log_policy_eq_zero_of_resources (hdom : P.Unbounded) (hu : P.u = Real.log)
    (hβR : P.discount * (1 + P.interest) < 1) {s : ℝ × Z} (hs : s.1 ∈ Icc assetFloor assetCap)
    (hlt : P.discount * P.logLipschitz < 1 / (P.resources s - assetFloor)) :
    P.policy s = assetFloor :=
  P.policy_eq_zero_of_corner_at (P.log_valueFunction_lipschitz hu hβR) hs
    (fun c d hd hdc hc => by
      rw [hu]
      refine log_marginal_bound ?_ (by rw [hdom] at hd; exact hd) hdc hc
      have h1 := P.minConsumption_le_consumption_floor s
      have h2 := P.minConsumption_pos
      linarith)
    hlt



end IncomeFluctuation

/-- **The bound is not vacuous.** At `r = 0` the interest-rate hypothesis holds automatically,
since `exp` is positive, so the log witness has a natural asset bound outright. -/
theorem logImpatient_natural_asset_bound (z : Fin 2) :
    ∃ ā : ℝ, ∀ a ∈ Icc (0 : ℝ) 1, ā < a → logImpatient.policy (a, z) < a := by
  refine logImpatient.exists_natural_asset_bound_log
    (logImpatient.positiveConsumption_of_unbounded rfl) logImpatient_u z ?_
  have hpos := Real.exp_pos (-logImpatient.deviationGap)
  have hint : logImpatient.interest = 0 := rfl
  rw [hint]
  linarith


end LeanEconomics

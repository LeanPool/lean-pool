/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Analysis.Bisection
public import LeanPool.MathFin.Models.Rates.FRA
public import LeanPool.MathFin.Models.Rates.InterestRateSwap
public import LeanPool.MathFin.Models.Rates.YieldCurve
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Curve bootstrapping by bracketing search

Every curve starts as instrument quotes and ends as discount factors; the
algorithm between is **bootstrapping** — solve one instrument at a time for
its new discount factor, with the already-solved factors held fixed. This
module connects the curve instruments (`fraValue`, `payerSwapValue` — both
carry `zero_iff` root conditions in `MathFin`) to a proved bisection
root-finder: each step reprices its instrument to tolerance, and the induction
`boot` carries that to every step under per-step hypotheses stated at the
prefix the recursion feeds in.

The module layers:

* **A bisection engine** — imported from `MathFin.Probability.Analysis.Bisection` (not
  duplicated here): the iteration `bisectStep` / `bisect` / `bisectMid` with
  its three facts — the bracket is invariant around the threshold, the error
  is at most half the interval per step, and the estimates converge.
* **A threshold bridge** (private) — the engine's hypothesis
  (`∀ x ∈ [lo, hi], f x < C ↔ x < σ`) is produced from an affine function with
  positive slope (`mul_sub_lt_neg_iff`).
* **The affine bootstrap step** — `affineStep_err` / `affineStep_tendsto` /
  `affineStep_value_err` / `affineStep_stepBudget`: bisection, from a bracket
  containing the root `(a − c)/b`, of an increasing rearrangement `x ↦ b·x − a`
  at level `−c` converges to that root; the instrument reprices to within
  `b·(hi − lo)/2^{n+1}` of the quote, and some `n ≤ ⌈log₂ (b·(hi−lo)/ε)⌉` steps
  achieve accuracy `ε`.
* **The FRA as an instrument** — with the earlier discount factor `p` fixed
  and the later one `x ≠ 0` bootstrapped, the FRA value is `p − (1 + δ·K)·x` —
  affine, covered when `1 + δ·K > 0`; strictly antitone, so the negated value is
  an increasing solving function (`fraThreshold`), and
  `fraValue_newUnknown_eq_quote_iff` is the root condition in the new unknown
  (with `fraRoot_agrees_with_pin`, it recovers `fraValue_zcb_eq_zero_iff` on the
  flat curve).
* **The payer swap as an instrument** — with the fixed schedule already
  bootstrapped (annuity `A` constant in the new factor `x`), the value is
  `(P0 − K·A) − x`: affine with slope `−1`, strictly antitone with **no**
  positivity condition; at zero quote the fixed rate is par at the root
  (`swapRoot_is_par`, consuming `payerSwapValue_eq_zero_iff`).
  With one payment at the new maturity (annuity `A₀ + δ·x`), the value is
  `(P0 − K·A₀) − (1 + K·δ)·x` — covered under `1 + K·δ > 0`
  (`swapLastCouponThreshold`).
* **The swap is a par coupon bond** — the zero-value last-coupon swap at fixed rate `K`
  is the coupon-bond pricing equation `couponBondPricingEq` of
  `Models/Rates/YieldCurve.lean` with coupon `K·δ` and face `1`
  (`payerSwapValue_lastCoupon_eq_zero_iff_couponBond`), so the closed-form bootstrap
  `bootstrap_solve` names the swap's root, and bisection on the swap recovers the
  discount factor of the coupon bond (`swapBootstrap_recovers_couponBondFactor`).
* **The induction** — `boot` builds the curve by structural recursion over
  the instrument index: step `i` bisects instrument `i`'s solving function on
  the prefix bootstrapped so far, so each step literally inherits the previous
  factors. `boot_step_err` bounds every step, `boot_length` (proved by
  induction) tracks the curve, and `boot_reprices_all` is the repricing
  theorem over all instruments — with hypotheses stated at the fed-in prefix
  (see the scope note). `fraChain` with `boot_reprices_fraChain` runs the
  FRA strip through the induction (fixed rate `K i` per FRA; step `0` is the
  spot deposit, anchored at the valuation-date factor `1`), and `swapChain`
  with `boot_reprices_swapChain` does the same for the spot-starting swap
  strip (fixed rate `K i` per maturity, last-coupon annuity over the prefix)
  — both discharging every hypothesis of `boot_reprices_all` except the
  per-step bracket condition, under the instrument layer's standing
  conditions.
* **Flat-curve capstone** — `fraBootstrap_flatCurve`: if the fixed rate
  equals the flat-curve forward rate, bisection at zero quote from any positive bracket
  around the true later discount factor recovers it to within
  `(hi − lo)/2^{n+1}`.

Scope of the induction: the hypotheses of `boot_step_err` and
`boot_reprices_all` are stated at the prefix the recursion actually feeds the
step — `boot V c lo hi n i`, the factors the earlier steps produced — and, on
that prefix, on the step's own bracket `[lo i, hi i]` (bisection evaluates the
instrument nowhere else). Each step assumes only what it consumes: the
instrument's threshold shape and affine identity at the run's actual earlier
factors, and a bracket containing the root computed from them. The first two are
exactly the facts the instrument layers provide at any prefix — the FRA by
`fraValue_affine_of_newUnknown` + `fraThreshold` (under `δ ≠ 0`, `1 + δ·K > 0`,
on a positive bracket), the known-schedule swap by
`payerSwapValue_affine_of_newUnknown` + `swapThreshold` (no slope condition),
the last-coupon swap by `payerSwapValue_affine_lastCoupon` +
`swapLastCouponThreshold` (under `1 + K·δ > 0`) — and `boot_reprices_fraChain` /
`boot_reprices_swapChain` discharge every hypothesis of `boot_reprices_all`
except the bracket condition for `fraChain` / `swapChain`, the FRA and swap
strips as `boot` instruments, under those standing conditions. The bracket
condition stays a hypothesis: the root moves with the prefix, so which bracket
is adequate depends on the factors the run produced, and the theorems ask for
exactly that, at the step that uses it. The pointwise per-`n` error bound is the
curve-level statement (convergence of the factors as `n → ∞` would follow by
induction on `i` when the hypotheses hold for every `n` and each threshold is
continuous in the prefix — as for `fraChain` / `swapChain`, whose roots are
affine in it — but is not formalized). Excluded: instruments whose
*already-fixed* legs contain the new factor (forward-starting fixed/floating
exchanges — the value is still affine in the bracket but with a slope of unknown
sign, possibly zero, so no bracketing sign change is guaranteed), and joint
solves for several new factors at once.

Boundary: `MathFin/Models/Rates/YieldCurve.lean` owns the closed-form
`bootstrap_solve*` names; this module owns the search-based bootstrap, and the swap layer
proves that bisection on the swap lands within `(hi − lo)/2^{n+1}` of the closed-form root, for a
bracket containing it (`swapBootstrap_recovers_couponBondFactor`).

## Main definitions

* `boot`: the bootstrapped curve, a list of discount factors after the first `i` instruments, the
  head being the newest.
* `fraChain`: the FRA strip as a `boot` instrument, instrument `i` being the FRA with fixed rate
  `K i` that reads the new discount factor `x`.
* `swapChain`: the swap strip as a `boot` instrument, instrument `i` being the spot-starting
  payer swap maturing at the new discount factor.

## Main results

* `affineStep_err`: for `b > 0` and a root `(a − c)/b` in `[lo, hi]`, bisection on `b·x − a`
  at target `−c` is within `(hi − lo)/2^{n+1}` of that root after `n` steps.
* `fraValue_affine_of_newUnknown`, `fraValue_newUnknown_eq_quote_iff`: for `δ ≠ 0`, the FRA value
  at the bootstrapped forward rate is `p − (1 + δK)·x` (for `x ≠ 0`); for `x > 0` and
  `1 + δK > 0` it equals the quote `c` if and only if `x = (p − c)/(1 + δK)`.
* `strictAntiOn_fraValue`, `fraStep_err`: for `δ ≠ 0` and `1 + δK > 0`, the FRA value is
  strictly decreasing on `x > 0`, and bisection from a bracket `[lo, hi]` with `lo > 0`
  containing `(p − c)/(1 + δK)` lands within `(hi − lo)/2^{n+1}` of it.
* `swapRoot_is_par`, `strictAnti_payerSwapValue`, `swapStep_err`: for `A ≠ 0` the root
  `P0 − K·A` of the payer swap has par rate `K`; the swap value is strictly decreasing in the
  new factor with no positivity condition, and bisection on it lands within `(hi − lo)/2^{n+1}`
  of the root when a bracket contains it.
* `payerSwapValue_lastCoupon_eq_zero_iff_couponBond`: the last-coupon swap has zero value at `x`
  if and only if `x` satisfies the coupon-bond pricing equation with coupon `K·δ` and face `1`.
* `swapBootstrap_recovers_couponBondFactor`: for `1 + K·δ > 0`, if `x` solves that
  coupon-bond equation and lies in `[lo, hi]`, bisection on the last-coupon swap lands within
  `(hi − lo)/2^{n+1}` of `x`.
* `boot_length`, `boot_step_err`: `boot` returns `i` factors after `i` instruments, and at step
  `i` its new factor is within `(hi i − lo i)/2^{n+1}` of the threshold root `σ`, given the
  threshold shape of the solving function on the bracket and `σ` in the bracket.
* `boot_reprices_all`: for `b > 0` and a solving function affine `a − b·x` on the bracket
  with root in the bracket, the repriced instrument `i` is within `b·(hi i − lo i)/2^{n+1}`
  of its quote `c i`.
* `boot_reprices_fraChain`, `boot_reprices_swapChain`: the same repricing bound for the FRA strip
  (`δ ≠ 0`, `1 + δ·K i > 0`, `lo i > 0`) and the swap strip (`1 + K i·δ > 0`), each given that the
  root lies in the step's bracket.
* `fraBootstrap_flatCurve`: for `δ ≠ 0`, a fixed rate equal to the flat-curve forward rate and
  a bracket with `lo > 0` containing the true later discount factor, bisection at zero quote
  recovers it within `(hi − lo)/2^{n+1}`.

## References

* [P. S. Hagan and G. West, *Interpolation methods for curve construction*][HaganWest2006], §2
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 4 and ch. 7

## Tags

curve bootstrapping, bisection, discount factors, FRA, swap rate, yield curve construction,
par swap, MSC 91G30, MSC 91G60, JEL E43
-/


@[expose] public section

namespace MathFin.Bootstrapping

open Filter Topology

/-! ### Threshold bridge: from instrument shape to the engine's hypothesis -/

/-- The threshold property is *global* for an affine function with positive
slope: `b·x − a` crosses the level `−c` exactly at the root `x = (a − c)/b`. -/
theorem mul_sub_lt_neg_iff (a b c x : ℝ) (hb : 0 < b) :
    b * x - a < -c ↔ x < (a - c) / b := by
  rw [lt_div_iff₀ hb, mul_comm x b]
  constructor <;> intro h <;> linarith

/-- The slope-weighted residual: for `b > 0`, `|a − b·m − c| = b · |m − (a − c)/b|`. -/
theorem abs_sub_mul_sub_eq_mul_abs (a b c m : ℝ) (hb : 0 < b) :
    |a - b * m - c| = b * |m - (a - c) / b| := by
  have : a - b * m - c = b * ((a - c) / b - m) := by field_simp; ring
  rw [this, abs_mul, abs_of_pos hb, abs_sub_comm]

/-! ### The affine bootstrap step -/

/-- **Bootstrap step, affine form.** For a value function whose increasing
rearrangement is `x ↦ b·x − a` (`b > 0`) and quote `c`, bisection from a bracket
containing the root `(a − c)/b` lands within `(hi − lo)/2^{n+1}` of it. -/
theorem affineStep_err (a b c lo hi : ℝ) (hb : 0 < b) (hσ : (a - c) / b ∈ Set.Icc lo hi)
    (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - (a - c) / b|
      ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (fun x _ ↦ mul_sub_lt_neg_iff a b c x hb) hσ n

/-- Convergence form of the affine bootstrap step. -/
theorem affineStep_tendsto (a b c lo hi : ℝ) (hb : 0 < b) (hσ : (a - c) / b ∈ Set.Icc lo hi) :
    Tendsto (bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi) atTop (𝓝 ((a - c) / b)) :=
  tendsto_bisectMid (fun x _ ↦ mul_sub_lt_neg_iff a b c x hb) hσ

/-- **Repricing bound.** The instrument value `a − b·x` at the bisection
estimate is within `b·(hi − lo)/2^{n+1}` of the quote `c` — the slope-weighed
half-interval. -/
theorem affineStep_value_err (a b c lo hi : ℝ) (hb : 0 < b)
    (hσ : (a - c) / b ∈ Set.Icc lo hi) (n : ℕ) :
    |a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - c|
      ≤ b * ((hi - lo) / 2 ^ (n + 1)) := by
  rw [abs_sub_mul_sub_eq_mul_abs _ _ _ _ hb]
  exact mul_le_mul_of_nonneg_left (affineStep_err a b c lo hi hb hσ n) hb.le

/-- **Step budget.** Some number `n ≤ ⌈log₂ (b·(hi − lo)/ε)⌉` of bisection steps
achieves repricing accuracy `ε`. `Real.logb 2` is `log₂`; Mathlib states the log ladder over
`Real.logb`. -/
theorem affineStep_stepBudget (a b c lo hi ε : ℝ) (hb : 0 < b)
    (hσ : (a - c) / b ∈ Set.Icc lo hi) (hε : 0 < ε) :
    ∃ n : ℕ,
      |a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi n - c| ≤ ε ∧
        n ≤ Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) := by
  refine ⟨Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)), ?_, le_rfl⟩
  have hlohi : lo ≤ hi := hσ.1.trans hσ.2
  have hT0 : 0 ≤ b * (hi - lo) / ε :=
    div_nonneg (mul_nonneg hb.le (sub_nonneg.mpr hlohi)) hε.le
  have hTle : b * (hi - lo) / ε
      ≤ 2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1) := by
    rcases eq_or_lt_of_le hT0 with h0 | h0
    · rw [← h0]
      exact pow_nonneg (by norm_num) _
    · have h1 : Real.logb 2 (b * (hi - lo) / ε)
          ≤ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) : ℕ) := Nat.le_ceil _
      have h2 : Real.logb 2 (b * (hi - lo) / ε)
          ≤ Real.logb 2 (2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1)) := by
        rw [Real.logb_pow 2 2 _, Real.logb_self_eq_one (by norm_num), mul_one,
          Nat.cast_add]
        linarith
      exact (Real.logb_le_logb (by norm_num) h0 (by positivity)).mp h2
  have hmain := (div_le_iff₀ hε).mp hTle
  calc |a - b * bisectMid (fun x : ℝ ↦ b * x - a) (-c) lo hi
        (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε))) - c|
      ≤ b * ((hi - lo) / 2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1)) :=
        affineStep_value_err a b c lo hi hb hσ _
    _ = (b * (hi - lo)) / 2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1) :=
        mul_div_assoc' b (hi - lo) _
    _ ≤ ε := by
        rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _),
          mul_comm ε (2 ^ (Nat.ceil (Real.logb 2 (b * (hi - lo) / ε)) + 1))]
        exact hmain

/-! ### Instruments I: the FRA (new unknown = the later discount factor) -/

section Fra

/-- **The FRA as an affine function of its new unknown.** With the earlier
discount factor `p` fixed and the later one `x` bootstrapped, the FRA value at
fixed rate `K` is `p − (1 + δ·K)·x` — consuming
`fraValue_forwardRate_eq_discount_difference`. -/
theorem fraValue_affine_of_newUnknown (p δ K x : ℝ) (hδ : δ ≠ 0) (hx : x ≠ 0) :
    fraValue δ x (fraForwardRate p x δ) K = p - (1 + δ * K) * x := by
  have h := fraValue_forwardRate_eq_discount_difference p x δ K hδ hx
  rw [h]
  ring

/-- **The FRA root condition** — the `zero_iff` layer in the new unknown.
For a positive candidate factor, the FRA reprices the quote exactly at
`x = (p − c)/(1 + δ·K)`. With `fraRoot_agrees_with_pin` it recovers
`fraValue_zcb_eq_zero_iff` at `c = 0` on the flat `zcb` curve, for `K` with
`1 + δ·K > 0`. -/
theorem fraValue_newUnknown_eq_quote_iff (p δ K c x : ℝ) (hδ : δ ≠ 0) (hx : 0 < x)
    (hpos : 0 < 1 + δ * K) :
    fraValue δ x (fraForwardRate p x δ) K = c ↔ x = (p - c) / (1 + δ * K) := by
  rw [fraValue_affine_of_newUnknown p δ K x hδ hx.ne', eq_div_iff hpos.ne']
  constructor <;> intro h
  · rw [mul_comm]
    linarith
  · rw [mul_comm x (1 + δ * K)] at h
    linarith

/-- Consistency: on the flat `zcb` curve the affine identity reproduces
`fraValue_zcb_eq_discount_difference` (right side equal by `ring`). -/
theorem fraValue_affine_zcb (r δ K T1 T2 : ℝ) (hδ : δ ≠ 0) :
    fraValue δ (zcb r 0 T2) (fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ) K
      = zcb r 0 T1 - (1 + δ * K) * zcb r 0 T2 :=
  fraValue_affine_of_newUnknown _ δ K _ hδ (zcb_pos r 0 T2).ne'

/-- **FRA monotonicity** (the licensing fact for bracketing): in the new
discount factor, on positive factors, the FRA value is strictly antitone — affine with slope
`−(1 + δ·K)`, covered when `1 + δ·K > 0`. -/
theorem strictAntiOn_fraValue (p δ K : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K) :
    StrictAntiOn (fun x : ℝ ↦ fraValue δ x (fraForwardRate p x δ) K) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change fraValue δ y (fraForwardRate p y δ) K < fraValue δ x (fraForwardRate p x δ) K
  rw [fraValue_affine_of_newUnknown p δ K x hδ (ne_of_gt hx),
    fraValue_affine_of_newUnknown p δ K y hδ (ne_of_gt hy)]
  linarith [mul_lt_mul_of_pos_right hxy hpos]

/-- **FRA threshold**: on a bracket of positive discount factors, the negated
FRA value at level `−c` is an increasing solving function with threshold
`(p − c)/(1 + δ·K)` — the exact hypothesis the engine's error bound
consumes. -/
theorem fraThreshold (p δ K c lo hi : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K)
    (hlo : 0 < lo) (x : ℝ) (hx : x ∈ Set.Icc lo hi) :
    -(fraValue δ x (fraForwardRate p x δ) K) < -c ↔ x < (p - c) / (1 + δ * K) := by
  have hx0 : x ≠ 0 := (lt_of_lt_of_le hlo hx.1).ne'
  rw [fraValue_affine_of_newUnknown p δ K x hδ hx0, neg_sub]
  exact mul_sub_lt_neg_iff p (1 + δ * K) c x hpos

/-- **FRA bootstrap step.** Bisection of the negated FRA value at the negated
quote computes the later discount factor to within `(hi − lo)/2^{n+1}`. -/
theorem fraStep_err (p δ K c lo hi : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K)
    (hlo : 0 < lo) (hσ : (p - c) / (1 + δ * K) ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate p x δ) K)) (-c) lo hi n
      - (p - c) / (1 + δ * K)| ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (fraThreshold p δ K c lo hi hδ hpos hlo) hσ n

/-- Convergence form of the FRA bootstrap step. -/
theorem fraStep_tendsto (p δ K c lo hi : ℝ) (hδ : δ ≠ 0) (hpos : 0 < 1 + δ * K)
    (hlo : 0 < lo) (hσ : (p - c) / (1 + δ * K) ∈ Set.Icc lo hi) :
    Tendsto (bisectMid (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate p x δ) K)) (-c) lo hi)
      atTop (𝓝 ((p - c) / (1 + δ * K))) :=
  tendsto_bisectMid (fraThreshold p δ K c lo hi hδ hpos hlo) hσ

/-- At the zero quote the FRA root makes the forward rate par: at the bootstrapped
factor `p/(1 + δ·K)` the simple forward rate equals the quoted fixed rate (one
direction; the equivalence on the flat curve is `fraRoot_agrees_with_pin`). -/
theorem fraRoot_parForward (p δ K : ℝ) (hδ : δ ≠ 0) (hp : p ≠ 0) :
    fraForwardRate p (p / (1 + δ * K)) δ = K := by
  unfold fraForwardRate
  field_simp
  ring

/-- The bridge to `fraValue_zcb_eq_zero_iff`: on the flat `zcb` curve the
bootstrap root `p/(1 + δ·K)` and the par-forward characterization
(`fraValue_zcb_eq_zero_iff`'s right side, `K = fraForwardRate p x δ`) describe
the same factor. -/
theorem fraRoot_agrees_with_pin (r δ K T1 T2 : ℝ) (hδ : δ ≠ 0) :
    zcb r 0 T2 = zcb r 0 T1 / (1 + δ * K) ↔
      K = fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ := by
  have hp : zcb r 0 T1 ≠ 0 := (zcb_pos r 0 T1).ne'
  have hx : zcb r 0 T2 ≠ 0 := (zcb_pos r 0 T2).ne'
  unfold fraForwardRate
  constructor <;> intro h
  · rw [h]
    field_simp
    ring
  · rw [h]
    have h1 : (1 : ℝ) + δ * ((zcb r 0 T1 / zcb r 0 T2 - 1) / δ)
        = zcb r 0 T1 / zcb r 0 T2 := by
      field_simp
      ring
    rw [h1]
    field_simp

end Fra

/-! ### Instruments II: the payer swap -/

section Swap

/-- **Swap, fixed schedule known.** With the annuity `A` already bootstrapped
(every fixed payment sits at a maturity before the new one), the payer swap
value in the new factor `x` is `(P0 − K·A) − x`: affine with slope `−1`, hence
strictly decreasing with **no** positivity condition (`strictAnti_payerSwapValue`). -/
theorem payerSwapValue_affine_of_newUnknown (P0 K A x : ℝ) :
    payerSwapValue P0 x K A = (P0 - K * A) - 1 * x := by
  change P0 - x - K * A = (P0 - K * A) - 1 * x
  ring

/-- Swap monotonicity, known schedule: strictly antitone on all of `ℝ`. -/
theorem strictAnti_payerSwapValue (P0 K A : ℝ) :
    StrictAnti (fun x : ℝ ↦ payerSwapValue P0 x K A) := by
  intro x y hxy
  change payerSwapValue P0 y K A < payerSwapValue P0 x K A
  change P0 - y - K * A < P0 - x - K * A
  linarith

/-- **Swap threshold**, known schedule: the negated value at level `−c` has
threshold `P0 − K·A − c`. -/
theorem swapThreshold (P0 K A c lo hi : ℝ) (x : ℝ) (_hx : x ∈ Set.Icc lo hi) :
    -(payerSwapValue P0 x K A) < -c ↔ x < P0 - K * A - c := by
  have h : payerSwapValue P0 x K A = P0 - K * A - x := by
    change P0 - x - K * A = P0 - K * A - x
    ring
  rw [h, neg_sub]
  simpa only [one_mul, div_one] using mul_sub_lt_neg_iff (P0 - K * A) 1 c x one_pos

/-- **Swap bootstrap step**, known schedule: bisection of the negated value at
the negated quote computes the new discount factor to within
`(hi − lo)/2^{n+1}`. -/
theorem swapStep_err (P0 K A c lo hi : ℝ) (hσ : P0 - K * A - c ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(payerSwapValue P0 x K A)) (-c) lo hi n - (P0 - K * A - c)|
      ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (swapThreshold P0 K A c lo hi) hσ n

/-- Convergence form of the swap bootstrap step. -/
theorem swapStep_tendsto (P0 K A c lo hi : ℝ) (hσ : P0 - K * A - c ∈ Set.Icc lo hi) :
    Tendsto (bisectMid (fun x : ℝ ↦ -(payerSwapValue P0 x K A)) (-c) lo hi)
      atTop (𝓝 (P0 - K * A - c)) :=
  tendsto_bisectMid (swapThreshold P0 K A c lo hi) hσ

/-- The par-rate interpretation of the swap root: at quote zero the fixed rate is par
at the bootstrapped factor `P0 − K·A` — consuming `payerSwapValue_eq_zero_iff`. -/
theorem swapRoot_is_par (P0 K A : ℝ) (hA : A ≠ 0) : parSwapRate P0 (P0 - K * A) A = K := by
  have h0 : payerSwapValue P0 (P0 - K * A) K A = 0 := by
    change P0 - (P0 - K * A) - K * A = 0
    ring
  exact ((payerSwapValue_eq_zero_iff P0 (P0 - K * A) K hA).mp h0).symm

/-- **Swap with one payment at the new maturity.** The fixed leg's annuity is
`A₀ + δ·x` (`A₀ = annuity δ P s` over the already-bootstrapped schedule, plus
one accrual at the new factor): value `(P0 − K·A₀) − (1 + K·δ)·x` — affine,
covered when `1 + K·δ > 0`. -/
theorem payerSwapValue_affine_lastCoupon (P0 K A₀ δ x : ℝ) :
    payerSwapValue P0 x K (A₀ + δ * x) = (P0 - K * A₀) - (1 + K * δ) * x := by
  change P0 - x - K * (A₀ + δ * x) = (P0 - K * A₀) - (1 + K * δ) * x
  ring

/-- Same, with the annuity in the `annuity δ P s` form. -/
theorem payerSwapValue_affine_lastCoupon_annuity {ι : Type*} (P0 K δ x : ℝ) (P : ι → ℝ)
    (s : Finset ι) :
    payerSwapValue P0 x K (annuity δ P s + δ * x)
      = (P0 - K * annuity δ P s) - (1 + K * δ) * x :=
  payerSwapValue_affine_lastCoupon P0 K (annuity δ P s) δ x

/-- Monotonicity of the last-coupon swap: strictly antitone on all of `ℝ` under
the slope condition `1 + K·δ > 0`. -/
theorem strictAnti_payerSwapValue_lastCoupon (P0 K A₀ δ : ℝ) (hpos : 0 < 1 + K * δ) :
    StrictAnti (fun x : ℝ ↦ payerSwapValue P0 x K (A₀ + δ * x)) := by
  intro x y hxy
  change payerSwapValue P0 y K (A₀ + δ * y) < payerSwapValue P0 x K (A₀ + δ * x)
  rw [payerSwapValue_affine_lastCoupon, payerSwapValue_affine_lastCoupon]
  linarith [mul_lt_mul_of_pos_right hxy hpos]

/-- Threshold of the last-coupon swap. -/
theorem swapLastCouponThreshold (P0 K A₀ δ c lo hi : ℝ) (hpos : 0 < 1 + K * δ) (x : ℝ)
    (_hx : x ∈ Set.Icc lo hi) :
    -(payerSwapValue P0 x K (A₀ + δ * x)) < -c ↔ x < (P0 - K * A₀ - c) / (1 + K * δ) := by
  rw [payerSwapValue_affine_lastCoupon, neg_sub]
  exact mul_sub_lt_neg_iff _ _ _ x hpos

/-- Bootstrap step for the last-coupon swap. -/
theorem swapStep_lastCoupon_err (P0 K A₀ δ c lo hi : ℝ) (hpos : 0 < 1 + K * δ)
    (hσ : (P0 - K * A₀ - c) / (1 + K * δ) ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(payerSwapValue P0 x K (A₀ + δ * x))) (-c) lo hi n
      - (P0 - K * A₀ - c) / (1 + K * δ)| ≤ (hi - lo) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le (swapLastCouponThreshold P0 K A₀ δ c lo hi hpos) hσ n

/-- The coupons `K·δ` paid on the schedule `s`, discounted by `P`, are `K` times the annuity. -/
private theorem sum_const_mul_eq_annuity {ι : Type*} (s : Finset ι) (P : ι → ℝ) (K δ : ℝ) :
    ∑ i ∈ s, K * δ * P i = K * annuity δ P s := by
  simp only [annuity, Finset.mul_sum, mul_assoc]

/-- **A zero-value swap is a par coupon bond.** The last-coupon payer swap (floating leg
`P0 − x`, one fixed payment of `K·δ` at each date of `s` and at the new factor `x`) has
zero value exactly when the coupon bond paying `K·δ` at every date and face `1` at the last
prices at `P0`: the pricing equation `couponBondPricingEq` of `Models/Rates/YieldCurve.lean`
with coupon `K·δ` and face `1`. -/
theorem payerSwapValue_lastCoupon_eq_zero_iff_couponBond {ι : Type*} (s : Finset ι)
    (P : ι → ℝ) (P0 K δ x : ℝ) :
    payerSwapValue P0 x K (annuity δ P s + δ * x) = 0 ↔
      couponBondPricingEq s (fun _ ↦ K * δ) P P0 (K * δ) 1 x := by
  simp only [payerSwapValue, couponBondPricingEq, sum_const_mul_eq_annuity]
  constructor <;> intro h <;> linear_combination h

/-- **Swap bootstrapping recovers the coupon-bond discount factor.** If the new factor `x`
solves the par-coupon-bond pricing equation — coupon `K·δ` at every date of `s` and at the new
one, face `1`, price `P0` — then bisection on the zero-quote last-coupon swap, from any bracket
`[lo, hi]` containing `x`, lands within `(hi − lo)/2^{n+1}` of it (`1 + K·δ > 0`). The
closed-form bootstrap `bootstrap_solve` identifies `x` with the swap's bisection root
`(P0 − K·A₀)/(1 + K·δ)`. -/
theorem swapBootstrap_recovers_couponBondFactor {ι : Type*} (s : Finset ι) (P : ι → ℝ)
    (P0 K δ x lo hi : ℝ) (hpos : 0 < 1 + K * δ)
    (hbond : couponBondPricingEq s (fun _ ↦ K * δ) P P0 (K * δ) 1 x)
    (hx : x ∈ Set.Icc lo hi) (n : ℕ) :
    |bisectMid (fun y : ℝ ↦ -(payerSwapValue P0 y K (annuity δ P s + δ * y))) 0 lo hi n - x|
      ≤ (hi - lo) / 2 ^ (n + 1) := by
  have hroot : x = (P0 - K * annuity δ P s - 0) / (1 + K * δ) := by
    have h := bootstrap_solve s (fun _ ↦ K * δ) P P0 (K * δ) 1 x
      (show (0 : ℝ) < K * δ + 1 by linarith).ne' hbond
    simp only [sum_const_mul_eq_annuity] at h
    rwa [sub_zero, add_comm 1 (K * δ)]
  have h := swapStep_lastCoupon_err P0 K (annuity δ P s) δ 0 lo hi hpos
    (by rw [← hroot]; exact hx) n
  rwa [neg_zero, ← hroot] at h

end Swap

/-! ### The induction: the bootstrapped curve

`boot` builds the discount curve by structural recursion over the instrument
index: step `i` bisects instrument `i`'s increasing rearrangement
`x ↦ −V i (x :: prefix)` at level `−c i` on the prefix bootstrapped so far —
each step literally inherits the previous factors. The step theorems below
state their hypotheses at exactly this fed-in prefix (`boot V c lo hi n i`),
not at every prefix list whatever: each step assumes only what it consumes.
The parameter `n` is the bisection step count used at *every* instrument
(uniform budget; a per-instrument budget `n : ℕ → ℕ` would need `boot` to
use `n i` at step `i` — not formalized). -/

/-- The **bootstrapped curve**: after the first `i` instruments, a list of
discount factors, the head being the newest. -/
noncomputable def boot (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n : ℕ) : ℕ → List ℝ
  | 0 => []
  | i + 1 =>
      bisectMid (fun x : ℝ ↦ -(V i (x :: boot V c lo hi n i))) (-(c i)) (lo i) (hi i) n
        :: boot V c lo hi n i

/-- Length: after `i` instruments the curve holds `i` factors. -/
theorem boot_length (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n i : ℕ) :
    (boot V c lo hi n i).length = i := by
  induction i with
  | zero => simp [boot]
  | succ i ih => simp only [boot, List.length_cons, ih]

/-- Definitional unfolding of the recursive step (the `i + 1` equation). -/
private theorem boot_succ (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n i : ℕ) :
    boot V c lo hi n (i + 1)
      = bisectMid (fun x : ℝ ↦ -(V i (x :: boot V c lo hi n i))) (-(c i)) (lo i) (hi i) n
        :: boot V c lo hi n i := rfl

/-- Every non-initial curve is nonempty, so its head is the newest factor. -/
theorem boot_succ_ne_nil (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (n i : ℕ) :
    boot V c lo hi n (i + 1) ≠ [] := by
  rw [boot_succ]
  exact List.cons_ne_nil _ _

/-- **The bootstrap step theorem, at the fed-in prefix.** For every instrument
`i`, the `i`-th bootstrapped factor (with `n` bisection steps per instrument)
is within `(hi i − lo i)/2^{n+1}` of that instrument's threshold `σ i p`,
where `p` is the prefix the recursion actually feeds step `i` — the factors
the earlier steps produced (`boot V c lo hi n i`), not an arbitrary list. The
threshold hypothesis and the root-in-bracket condition are assumed exactly
there: each step consumes only its own instrument's shape, on its own
bracket, at the factors the run produced. The prefix itself depends on `n`,
so the hypotheses are per-`n`: if they hold for every `n`, the gap to the
prefix-dependent threshold tends to `0` (not stated as a theorem);
convergence of the factors themselves is not stated either (it would follow
by induction on `i` when, in addition, each `σ i` is continuous in the
prefix). -/
theorem boot_step_err (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (σ : ℕ → List ℝ → ℝ)
    (i n : ℕ)
    (hthr : ∀ x ∈ Set.Icc (lo i) (hi i),
      -(V i (x :: boot V c lo hi n i)) < -(c i) ↔ x < σ i (boot V c lo hi n i))
    (hσ : σ i (boot V c lo hi n i) ∈ Set.Icc (lo i) (hi i)) :
    |(boot V c lo hi n (i + 1)).head (boot_succ_ne_nil V c lo hi n i)
      - σ i (boot V c lo hi n i)| ≤ (hi i - lo i) / 2 ^ (n + 1) :=
  abs_bisectMid_sub_le hthr hσ n

/-- **The bootstrap repricing theorem, at the fed-in prefix.** Given
instrument `i`'s affine shape `V i (x :: p) = a i p − b i p · x` on the step's
own bracket (bisection evaluates the instrument only there), slope
`b i p > 0`, and the root `(a i p − c i)/b i p` in the bracket — all at the
prefix `p` the recursion feeds step `i` — the bootstrapped factor reprices
instrument `i`'s quote up to the slope-weighted half-interval
`b i p · (hi i − lo i)/2^{n+1}`. The shape and slope are exactly the facts the
instrument layers of this file provide at whatever prefix is fed in (FRA:
`fraValue_affine_of_newUnknown` + `fraThreshold`; known-schedule swap:
`payerSwapValue_affine_of_newUnknown` + `swapThreshold`; last-coupon swap:
`payerSwapValue_affine_lastCoupon` + `swapLastCouponThreshold`), so the only
run-dependent input left is the per-step bracket choice;
`boot_reprices_fraChain` / `boot_reprices_swapChain` discharge every
hypothesis but it for the FRA and swap strips, under the FRA / swap standing
conditions. -/
theorem boot_reprices_all (V : ℕ → List ℝ → ℝ) (c lo hi : ℕ → ℝ) (a b : ℕ → List ℝ → ℝ)
    (i n : ℕ) (hb : 0 < b i (boot V c lo hi n i))
    (hV : ∀ x ∈ Set.Icc (lo i) (hi i),
      V i (x :: boot V c lo hi n i)
        = a i (boot V c lo hi n i) - b i (boot V c lo hi n i) * x)
    (hσ : (a i (boot V c lo hi n i) - c i) / b i (boot V c lo hi n i)
      ∈ Set.Icc (lo i) (hi i)) :
    |V i ((boot V c lo hi n (i + 1)).head (boot_succ_ne_nil V c lo hi n i)
        :: boot V c lo hi n i) - c i|
      ≤ b i (boot V c lo hi n i) * ((hi i - lo i) / 2 ^ (n + 1)) := by
  simp only [boot_succ, List.head_cons]
  set p := boot V c lo hi n i
  have hthr : ∀ x ∈ Set.Icc (lo i) (hi i),
      -(V i (x :: p)) < -(c i) ↔ x < (a i p - c i) / b i p := by
    intro x hx
    rw [hV x hx, neg_sub]
    exact mul_sub_lt_neg_iff (a i p) (b i p) (c i) x hb
  have hstep : |bisectMid (fun x : ℝ ↦ -(V i (x :: p))) (-(c i)) (lo i) (hi i) n
      - (a i p - c i) / b i p| ≤ (hi i - lo i) / 2 ^ (n + 1) :=
    abs_bisectMid_sub_le hthr hσ n
  rw [hV _ (bisectMid_mem_Icc hthr hσ n), abs_sub_mul_sub_eq_mul_abs _ _ _ _ hb]
  exact mul_le_mul_of_nonneg_left hstep hb.le

/-! #### The file's instruments inside the induction

`fraChain` and `swapChain` are the instrument layers in `boot`'s list form:
the new factor `x` at the head of the fed-in list, the already-bootstrapped
factors behind it. Both are anchored at every step, including the first: the
discount factor at the valuation date is `1`, so step `0` of the FRA strip is
the spot deposit (an FRA whose earlier factor is `1`), and every swap step is a
spot-starting swap (`P0 = 1`). Each instrument `i` carries its own fixed rate
`K i`. They discharge every hypothesis of `boot_reprices_all` except the
bracket condition, which stays a hypothesis; what they add is only the
instrument layer's standing assumptions. -/

/-- The **FRA strip as a `boot` instrument**: instrument `i` is the FRA with
fixed rate `K i`, reading the new factor `x` and the previous factor off the
fed-in list; on the empty prefix (step `0`) the previous factor is the
valuation-date factor `1`, so the first instrument is the spot deposit. (The
`[]` branch is never fed by `boot`, which always passes `x :: prefix`.) -/
noncomputable def fraChain (δ : ℝ) (K : ℕ → ℝ) : ℕ → List ℝ → ℝ :=
  fun i l ↦
    match l with
    | x :: p => fraValue δ x (fraForwardRate (p.head?.getD 1) x δ) (K i)
    | [] => 0

/-- The unfolding equation: on `x :: p` the strip instrument is the FRA value
function of the instrument layer, the earlier factor read off the head of `p`
(defaulting to the valuation-date factor `1` when `p` is empty, so on `[x]` it is
the spot deposit) — matching `swapChain_cons`'s general shape on the fed-in list. -/
@[simp]
theorem fraChain_cons (δ : ℝ) (K : ℕ → ℝ) (x : ℝ) (p : List ℝ) (i : ℕ) :
    fraChain δ K i (x :: p) = fraValue δ x (fraForwardRate (p.head?.getD 1) x δ) (K i) := rfl

/-- **The FRA strip reprices inside the induction.** At every step `i`
(step `0` is the spot deposit, anchored at the valuation-date factor `1`),
under the FRA layer's standing conditions — `δ ≠ 0`, `1 + δ·K i > 0`, a
positive bracket — the only hypothesis left is the bracket condition at the
fed-in prefix: `[lo i, hi i]` must contain the root computed from the *actual*
previous factor `((boot (fraChain δ K) c lo hi n i).head?.getD 1 − c i) /
(1 + δ·K i)`. Then the bootstrapped factor reprices instrument `i`'s quote to
within `(1 + δ·K i)·(hi i − lo i)/2^{n+1}`. -/
theorem boot_reprices_fraChain (δ : ℝ) (K c lo hi : ℕ → ℝ) (n i : ℕ) (hδ : δ ≠ 0)
    (hpos : 0 < 1 + δ * K i) (hlo : 0 < lo i)
    (hσ : ((boot (fraChain δ K) c lo hi n i).head?.getD 1 - c i) / (1 + δ * K i)
      ∈ Set.Icc (lo i) (hi i)) :
    |fraChain δ K i ((boot (fraChain δ K) c lo hi n (i + 1)).head
        (boot_succ_ne_nil (fraChain δ K) c lo hi n i)
        :: boot (fraChain δ K) c lo hi n i) - c i|
      ≤ (1 + δ * K i) * ((hi i - lo i) / 2 ^ (n + 1)) :=
  boot_reprices_all (fraChain δ K) c lo hi (fun _ p ↦ p.head?.getD 1)
    (fun j _ ↦ 1 + δ * K j) i n hpos
    (fun x hx ↦ fraValue_affine_of_newUnknown _ δ (K i) x hδ (lt_of_lt_of_le hlo hx.1).ne') hσ

/-- The **swap strip as a `boot` instrument**: instrument `i` is the
spot-starting payer swap (`P0 = 1`) maturing at the new factor `x`, with fixed
rate `K i` and one fixed payment (accrual `δ`) at each bootstrapped date and at
the new one — annuity `δ·(Σ prefix) + δ·x`, the last-coupon form of the swap
layer. Every step, including the first (empty prefix: the one-period swap), is
a genuine swap; the `[]` branch is never fed by `boot`. -/
noncomputable def swapChain (δ : ℝ) (K : ℕ → ℝ) : ℕ → List ℝ → ℝ :=
  fun i l ↦
    match l with
    | x :: p => payerSwapValue 1 x (K i) (δ * p.sum + δ * x)
    | [] => 0

/-- The unfolding equation of the swap strip instrument. -/
@[simp]
theorem swapChain_cons (δ : ℝ) (K : ℕ → ℝ) (x : ℝ) (p : List ℝ) (i : ℕ) :
    swapChain δ K i (x :: p) = payerSwapValue 1 x (K i) (δ * p.sum + δ * x) := rfl

/-- **The swap strip reprices inside the induction.** At every step `i`, under
the last-coupon slope condition `1 + K i·δ > 0` (no bracket positivity is
needed: the swap value is affine on all of `ℝ`), the only hypothesis left is
the bracket condition at the fed-in prefix: `[lo i, hi i]` must contain the
root `(1 − K i·δ·Σ prefix − c i)/(1 + K i·δ)` computed from the factors the run
actually produced. Then the bootstrapped factor reprices swap `i`'s quote
(`c i = 0` for a par-rate quote `K i`) to within
`(1 + K i·δ)·(hi i − lo i)/2^{n+1}`. -/
theorem boot_reprices_swapChain (δ : ℝ) (K c lo hi : ℕ → ℝ) (n i : ℕ)
    (hpos : 0 < 1 + K i * δ)
    (hσ : (1 - K i * (δ * (boot (swapChain δ K) c lo hi n i).sum) - c i) / (1 + K i * δ)
      ∈ Set.Icc (lo i) (hi i)) :
    |swapChain δ K i ((boot (swapChain δ K) c lo hi n (i + 1)).head
        (boot_succ_ne_nil (swapChain δ K) c lo hi n i)
        :: boot (swapChain δ K) c lo hi n i) - c i|
      ≤ (1 + K i * δ) * ((hi i - lo i) / 2 ^ (n + 1)) :=
  boot_reprices_all (swapChain δ K) c lo hi (fun j p ↦ 1 - K j * (δ * p.sum))
    (fun j _ ↦ 1 + K j * δ) i n hpos
    (fun x _ ↦ payerSwapValue_affine_lastCoupon 1 (K i) _ δ x) hσ

/-! ### Flat-curve capstone: the bootstrap recovers the flat-curve factor -/

/-- **Flat-curve capstone.** If the fixed rate equals the flat-curve forward
rate, the FRA's true later discount factor on the `zcb` curve *is* the root of
the solving function at zero quote (an algebraic identity), and bisection at zero quote
from any positive bracket around it recovers the factor to within `(hi − lo)/2^{n+1}`. -/
theorem fraBootstrap_flatCurve (r δ K T1 T2 lo hi : ℝ) (hδ : δ ≠ 0)
    (hK : K = fraForwardRate (zcb r 0 T1) (zcb r 0 T2) δ)
    (hx : zcb r 0 T2 ∈ Set.Icc lo hi) (hlo : 0 < lo) (n : ℕ) :
    |bisectMid (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate (zcb r 0 T1) x δ) K)) 0 lo hi n
      - zcb r 0 T2| ≤ (hi - lo) / 2 ^ (n + 1) := by
  have h1 : δ * ((zcb r 0 T1 / zcb r 0 T2 - 1) / δ)
      = zcb r 0 T1 / zcb r 0 T2 - 1 := by field_simp
  have hpos : 0 < 1 + δ * K := by
    simp only [hK, fraForwardRate, h1]
    linarith [div_pos (zcb_pos r 0 T1) (zcb_pos r 0 T2)]
  have hσeq : (zcb r 0 T1 - 0) / (1 + δ * K) = zcb r 0 T2 := by
    rw [hK, sub_zero]
    have hp : zcb r 0 T1 ≠ 0 := (zcb_pos r 0 T1).ne'
    have hx : zcb r 0 T2 ≠ 0 := (zcb_pos r 0 T2).ne'
    unfold fraForwardRate
    rw [show (1 : ℝ) + δ * ((zcb r 0 T1 / zcb r 0 T2 - 1) / δ)
        = zcb r 0 T1 / zcb r 0 T2 from by rw [h1]; ring,
      div_eq_iff (div_ne_zero hp hx)]
    field_simp
  have hthr : ∀ x ∈ Set.Icc lo hi,
      (fun x : ℝ ↦ -(fraValue δ x (fraForwardRate (zcb r 0 T1) x δ) K)) x < 0
        ↔ x < zcb r 0 T2 := by
    intro x hx
    have hthr' := fraThreshold (zcb r 0 T1) δ K 0 lo hi hδ hpos hlo x hx
    simpa only [sub_zero, div_eq_div_iff, neg_zero, one_mul] using
      hthr'.trans (by rw [hσeq])
  exact abs_bisectMid_sub_le hthr hx n

end MathFin.Bootstrapping

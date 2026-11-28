/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PDE
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Local-volatility skew of a tilted smile: Dupire's ratio and the rule of two (eq 10.8)

Equation numbers are those of S. Bagaria, *Notes on Fixed Income Derivative Pricing*
(lecture notes), ch. 10. Dupire's ratio is B. Dupire, "Pricing with a smile",
*Risk* 7(1) (1994); its form in implied total variance is J. Gatheral, *The Volatility
Surface: A Practitioner's Guide*, Wiley (2006), ch. 1. No forward-start option, forward
smile or forward skew is modelled in this module.

Setting: zero rates, one maturity axis `T`, log-moneyness `k = log(K/F)`, a fixed
forward `F > 0`. The smile surface of eq 10.7 is tilted by a parameter `ε` so that
first-order-in-ε readings extract the skew slope:

  `σ_BS(ε, k, T) = σ + ε·ψ₁·k/√(T+T₀)`   (`smileSurface`; `σ > 0`, `T+T₀ > 0`)

and the call prices on it are the `bsV` composites (`bsCallSmile`). Dupire's
zero-rates ratio

  `R(ε, k, T) = 2·∂_T C / (K²·∂²_K C)`  (in `k`-form: `K²·∂²_K C = C_kk − C_k`)

enters **as a definition** (`dupireRatio`) — the derivation of the ratio itself
from a local-vol model is not developed here. The headline results:

* `dupireRatio_k_slope` — eq 10.8: for `F, σ, T, T₀ > 0`, the ATM k-slope of `R` has
  ε-slope `2σψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}` (with `(T+T₀)^{3/2}` rendered as
  `(T+T₀)·√(T+T₀)`). The numerator `(3/2)T + 2T₀` is the one consistent with the
  rule of two (`localSkew_zero`).
* `dupireRatio_sqrt_slope` — the σ_loc reading: the same slope for `√R` is
  `localSkew ψ₁ T₀ T = ψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}` — a first-order-in-ε reading of
  the local-vol ATM skew implied by the surface (for `F, σ, T, T₀ > 0`), not the actual
  skew of the `ε = 1` surface, which carries `O(ψ₁³)` corrections (not proved here).
* `localSkew_zero`, `tendsto_localSkew_nhds_zero`, `tendsto_localSkew_mul_sqrt_atTop` —
  for `T₀ > 0` the closed form `localSkew` equals `2ψ₁/√T₀` at `T = 0`, twice the implied
  ATM skew `ψ₁/√T₀` (the rule of two), tends to that value as `T → 0`, and behaves like
  `(3/2)ψ₁/√T` as `T → ∞`. These are statements about the closed form;
  `dupireRatio_sqrt_slope` identifies it with the skew of the surface only for `T > 0`.
* `smileSurface_skew_slope`, `dupireRatio_sqrt_slope_eq_mul_skew`,
  `tendsto_dupireRatio_sqrt_slope_nhdsGT_zero` — the rule of two on the surface itself: the
  first-order implied ATM skew is `ψ₁/√(T+T₀)`, the first-order local ATM skew is that times
  `((3/2)T + 2T₀)/(T + T₀)` for every `T > 0`, and as `T → 0⁺` it tends to twice the implied
  ATM skew at `T = 0`. All first order in ε, for this one-parameter family of surfaces.

The notes' eq 10.9 reads a forward skew off `localSkew` as one half of it (the rule of two
run in reverse). That reading is a heuristic and is not formalized here.

Method (no probability, no integration, no ODEs): everything is a one-variable
`HasDerivAt` chain rule through the Black form `Φ(d₊) − e^k·Φ(d₋)` in the
coordinates `(k, w)` with total variance `w = σ_tilde²T`. The key exact identity is
`dupireRatio_eq`: in these coordinates Dupire's ratio is the rational function
`w_T/(1 + δ)` with `δ = −k·w_k/w + w_k²·(k²−w−w²/4)/(4w²) + w_kk/2` — the
Gatheral form of the ratio specialized to this surface — after which the
ε/k-extraction is elementary calculus on explicit functions. The price is the
`bsV` of `MathFin.Models.BlackScholes.PDE`, with `bsd1`/`bsd2` unfolded to the `(k,w)` form
(`bsCallSmile_eq`).

## Main definitions

* `smileSurface`: the ε-tilted smile `σ_BS(ε, k, T) = σ + ε ψ₁ k / √(T + T₀)` in
  log-moneyness `k = log(K/F)` at zero rates.
* `totalVar`: the total variance `smileSurface² · T` along the surface.
* `dpl`, `dmi`: `d₊ = (−k + w/2)/√w` and `d₋ = (−k − w/2)/√w` in `(k, w)` coordinates.
* `blackForm`: the forward-normalised zero-rate call `Φ(d₊) − e^k Φ(d₋)`.
* `bsCallSmile`: the call price `bsV` at strike `F e^k`, spot `F`, volatility `smileSurface` and
  maturity `T`.
* `dupireRatio`: Dupire's zero-rate ratio `R = 2 C_T / (C_kk − C_k)` of `bsCallSmile`, taken as
  a definition (it is not derived from a local-volatility model here).
* `wSlope`, `smileN`, `smileDelta`: the total-variance slope `∂_k w`, the numerator `w_T` and
  the denominator deformation `δ` of the Gatheral form `R = w_T / (1 + δ)`.
* `localSkew`: the closed form `ψ₁ ((3/2) T + 2 T₀) / (T + T₀)^{3/2}`.

## Main results

* `bsCallSmile_eq`: for `F, T > 0` and a positive surface value, `bsCallSmile` equals
  `F · blackForm k (totalVar …)`.
* `exp_mul_pdf_dmi`: for `w > 0`, `e^k ϕ(d₋) = ϕ(d₊)`.
* `dupireRatio_eq`: for `F, T, T + T₀ > 0` and a positive surface value, in `(k, w)` coordinates
  `dupireRatio = smileN / (1 + smileDelta)`.
* `dupireRatio_k_slope`: for `F, σ, T, T₀ > 0`, the ε-derivative at `0` of the ATM `k`-slope of
  `dupireRatio` is `2σψ₁ ((3/2)T + 2T₀) / ((T + T₀) √(T + T₀))`.
* `dupireRatio_sqrt_slope`: for `F, σ, T, T₀ > 0`, the same derivative for `√(dupireRatio)` is
  `localSkew ψ₁ T₀ T`.
* `smileSurface_skew_slope`: the ε-derivative at `0` of the ATM `k`-slope of `smileSurface` is
  `ψ₁ / √(T + T₀)`.
* `dupireRatio_sqrt_slope_eq_mul_skew`: the first-order local ATM skew is
  `((3/2)T + 2T₀)/(T + T₀)` times the first-order implied ATM skew.
* `localSkew_zero`, `tendsto_localSkew_nhds_zero`: for `T₀ > 0`, `localSkew` at `T = 0`, and its
  limit as `T → 0`, is `2 ψ₁ / √T₀`.
* `tendsto_dupireRatio_sqrt_slope_nhdsGT_zero`: as `T → 0⁺` the first-order local ATM skew tends
  to twice the first-order implied ATM skew at `T = 0`.
* `tendsto_localSkew_mul_sqrt_atTop`: `localSkew ψ₁ T₀ T · √T → (3/2) ψ₁` as `T → ∞`.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 10
* [B. Dupire, *Pricing with a smile*][Dupire1994]
* [J. Gatheral, *The Volatility Surface: A Practitioner's Guide*][Gatheral2006], ch. 1

## Tags

local volatility skew, rule of two, Dupire ratio, volatility smile, total variance, skew, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin.ForwardSmile

open ProbabilityTheory Real

/-! ## The surface, the price, the ratio -/

/-- **Eq 10.7, ε-tilted**: the smile surface `σ_BS(ε,k,T) = σ + ε·ψ₁·k/√(T+T₀)`
in log-moneyness `k = log(K/F)` at zero rates, with the tilt parameter `ε`
inserted so first-order-in-ε readings extract the skew slope. At `ε = 0` (and at
`k = 0` for every `ε`) it is the ATM vol `σ`. -/
noncomputable def smileSurface (σ ψ₁ T₀ ε k T : ℝ) : ℝ := σ + ε * ψ₁ * k / Real.sqrt (T + T₀)

/-- The smile surface is positive whenever `T + T₀ > 0` and the tilt is smaller than the base:
`|ε·ψ₁·k| < σ·√(T+T₀)` (positivity cannot hold for arbitrary tilts — the surface
is negative once `ε·ψ₁·k < −σ·√(T+T₀)`). -/
theorem smileSurface_pos {σ ψ₁ T₀ ε k T : ℝ} (hS : 0 < T + T₀)
    (hb : |ε * ψ₁ * k| < σ * Real.sqrt (T + T₀)) :
    0 < smileSurface σ ψ₁ T₀ ε k T := by
  have hs : 0 < Real.sqrt (T + T₀) := Real.sqrt_pos.mpr hS
  rw [abs_lt] at hb
  have hdiv : -σ < ε * ψ₁ * k / Real.sqrt (T + T₀) := by
    rw [lt_div_iff₀ hs]
    linarith [hb.1]
  unfold smileSurface
  linarith [hdiv]

/-- At the money the tilt vanishes: the surface sits at the base vol `σ` for
every `ε`. -/
theorem smileSurface_atm (σ ψ₁ T₀ ε T : ℝ) : smileSurface σ ψ₁ T₀ ε 0 T = σ := by
  unfold smileSurface; norm_num

/-- Total implied variance along the surface: `w = σ_BS²·T`. -/
noncomputable def totalVar (σ ψ₁ T₀ ε k T : ℝ) : ℝ := smileSurface σ ψ₁ T₀ ε k T ^ 2 * T

/-- The upper standardized normal argument in `(k, w)` coordinates:
`d₊ = (−k + w/2)/√w` (this is `bsd1 F (F·e^k) 0 σ_tilde T` at `w = σ_tilde²T`). -/
noncomputable def dpl (k w : ℝ) : ℝ := (-k + w / 2) / Real.sqrt w

/-- The lower standardized normal argument: `d₋ = (−k − w/2)/√w`. -/
noncomputable def dmi (k w : ℝ) : ℝ := (-k - w / 2) / Real.sqrt w

/-- `d₊ = −k/√w + √w/2`: the form in which `d₊` is written when `w` is a squared root variance
(for `w ≤ 0` both sides are `0`, as `√w = 0`). -/
theorem dpl_eq (k w : ℝ) : dpl k w = -k / Real.sqrt w + Real.sqrt w / 2 := by
  rw [dpl, add_div, div_right_comm, Real.div_sqrt]

/-- `d₋ = −k/√w − √w/2`, as `dpl_eq`. -/
theorem dmi_eq (k w : ℝ) : dmi k w = -k / Real.sqrt w - Real.sqrt w / 2 := by
  rw [dmi, sub_div, div_right_comm, Real.div_sqrt]

/-- The Black-76 call normalized by the forward: `c(k,w) = Φ(d₊) − e^k·Φ(d₋)`,
the zero-rates `bsV` in `(k, w)` coordinates. -/
noncomputable def blackForm (k w : ℝ) : ℝ := Phi (dpl k w) - Real.exp k * Phi (dmi k w)

/-- **The call price on the tilted surface**: the zero-rates
`bsV` at strike `K = F·e^k`, spot `S = F`, vol `σ_BS(ε,k,T)`, maturity `T`. -/
noncomputable def bsCallSmile (F σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  bsV (F * Real.exp k) 0 (smileSurface σ ψ₁ T₀ ε k T) F T

/-- **Dupire's zero-rates ratio in k-form** (the ratio as a
definition — its derivation from a local-vol model is not developed here):
`R = 2·C_T/(C_kk − C_k)`, using `K²·∂²_K C = C_kk − C_k` for
`K = F·e^k`. -/
noncomputable def dupireRatio (F σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  2 * deriv (fun t ↦ bsCallSmile F σ ψ₁ T₀ ε k t) T
    / (deriv (fun x ↦ deriv (fun x ↦ bsCallSmile F σ ψ₁ T₀ ε x T) x) k
        - deriv (fun x ↦ bsCallSmile F σ ψ₁ T₀ ε x T) k)

/-! ## The `(k, w)` unfolding and the variance chains -/

/-- **The r=0, K=F·e^k magic identity**: `e^k·ϕ(d₋) = ϕ(d₊)` in `(k,w)`
coordinates — the k-form of the `bs_identity` at zero rates. It is
what makes every density term in the Dupire ratio collapse. -/
theorem exp_mul_pdf_dmi {k w : ℝ} (hw : 0 < w) :
    Real.exp k * gaussianPDFReal 0 1 (dmi k w) = gaussianPDFReal 0 1 (dpl k w) := by
  have hsq : dpl k w ^ 2 - dmi k w ^ 2 = -(2 * k) := by
    have hnum : (-k + w / 2) ^ 2 - (-k - w / 2) ^ 2 = -(2 * k) * w := by ring
    have h1 : dpl k w ^ 2 = (-k + w / 2) ^ 2 / w := by
      unfold dpl
      rw [show ((-k + w / 2) / Real.sqrt w) ^ 2 = (-k + w / 2) ^ 2 / Real.sqrt w ^ 2 from by
          ring, Real.sq_sqrt hw.le]
    have h2 : dmi k w ^ 2 = (-k - w / 2) ^ 2 / w := by
      unfold dmi
      rw [show ((-k - w / 2) / Real.sqrt w) ^ 2 = (-k - w / 2) ^ 2 / Real.sqrt w ^ 2 from by
          ring, Real.sq_sqrt hw.le]
    rw [h1, h2, ← sub_div, hnum]
    field_simp [hw.ne']
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [← mul_assoc, mul_comm (Real.exp k) (Real.sqrt (2 * π))⁻¹, mul_assoc,
    ← Real.exp_add,
    show k + -(dmi k w) ^ 2 / 2 = -(dpl k w) ^ 2 / 2 from by linarith [hsq]]

/-- **The `(k, w)` unfolding**: at zero rates with `K = F·e^k`, the `bsV`
composite on the tilted surface is the forward-normalized Black form at the
total variance `w = σ_BS²·T`. -/
theorem bsCallSmile_eq {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    bsCallSmile F σ ψ₁ T₀ ε k T = F * blackForm k (totalVar σ ψ₁ T₀ ε k T) := by
  have hlog : Real.log (F / (F * Real.exp k)) = -k := by
    rw [show F / (F * Real.exp k) = (Real.exp k)⁻¹ by field_simp, Real.log_inv, Real.log_exp]
  have hne : smileSurface σ ψ₁ T₀ ε k T * Real.sqrt T ≠ 0 :=
    mul_ne_zero hst.ne' (Real.sqrt_pos.mpr hT).ne'
  have hsplit : Real.sqrt (smileSurface σ ψ₁ T₀ ε k T ^ 2 * T)
      = smileSurface σ ψ₁ T₀ ε k T * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg _) T, Real.sqrt_sq hst.le]
  have hbsd1 : bsd1 F (F * Real.exp k) 0 (smileSurface σ ψ₁ T₀ ε k T) T
      = dpl k (totalVar σ ψ₁ T₀ ε k T) := by
    unfold bsd1 dpl totalVar
    rw [hlog, hsplit]
    field_simp [hne]
    ring
  have hbsd2 : bsd2 F (F * Real.exp k) 0 (smileSurface σ ψ₁ T₀ ε k T) T
      = dmi k (totalVar σ ψ₁ T₀ ε k T) := by
    unfold bsd2
    rw [hbsd1]
    unfold dmi dpl totalVar
    rw [hsplit]
    field_simp [hne]
    rw [Real.sq_sqrt hT.le]
    ring
  unfold bsCallSmile bsV blackForm
  rw [hbsd1, hbsd2]
  norm_num [Real.exp_neg, Real.exp_zero]
  ring

/-- `∂_k σ_BS = ε·ψ₁/√(T+T₀)` — the surface is affine in `k`. -/
private theorem hasDerivAt_smileSurface_k {σ ψ₁ T₀ ε T x : ℝ} :
    HasDerivAt (fun y ↦ smileSurface σ ψ₁ T₀ ε y T) (ε * ψ₁ / Real.sqrt (T + T₀)) x := by
  have h0 : HasDerivAt (fun y : ℝ ↦ σ + (ε * ψ₁ / Real.sqrt (T + T₀)) * y)
      (ε * ψ₁ / Real.sqrt (T + T₀)) x := by
    simpa using ((hasDerivAt_id x).const_mul (ε * ψ₁ / Real.sqrt (T + T₀))).add_const σ
  refine h0.congr_of_eventuallyEq ?_
  filter_upwards with y
  unfold smileSurface
  field_simp

/-- `∂_k w = 2·σ_tilde·(ε·ψ₁/√(T+T₀))·T` — the `k`-chain of the total variance. -/
private theorem hasDerivAt_totalVar_k {σ ψ₁ T₀ ε T x : ℝ} :
    HasDerivAt (fun y ↦ totalVar σ ψ₁ T₀ ε y T)
      (2 * smileSurface σ ψ₁ T₀ ε x T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T) x :=
  ((hasDerivAt_smileSurface_k.fun_pow 2).mul_const T).congr_deriv (by ring)

/-- `∂_T w = σ_tilde² − σ_tilde·(ε·ψ₁·k)·T/(T+T₀)^{3/2}` — the `T`-chain of the total
variance (both `T`-channels of `w = σ_tilde²T` move: `σ_tilde` carries `√(T+T₀)` in the
denominator). `(T+T₀)^{3/2}` is rendered `(T+T₀)·√(T+T₀)`. -/
private theorem hasDerivAt_totalVar_t {σ ψ₁ T₀ ε k T : ℝ} (hS : 0 < T + T₀) :
    HasDerivAt (fun t ↦ totalVar σ ψ₁ T₀ ε k t)
      (smileSurface σ ψ₁ T₀ ε k T ^ 2
        - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T / ((T + T₀) * Real.sqrt (T + T₀))) T := by
  have hs : Real.sqrt (T + T₀) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hT₀ne : T + T₀ ≠ 0 := by linarith
  have hssq : Real.sqrt (T + T₀) ^ 2 = T + T₀ := Real.sq_sqrt hS.le
  have h1 : HasDerivAt (fun t : ℝ ↦ t + T₀) 1 T := (hasDerivAt_id' T).add_const T₀
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.sqrt (t + T₀)) (1 / (2 * Real.sqrt (T + T₀))) T :=
    h1.sqrt hT₀ne
  have hinv : HasDerivAt (fun t : ℝ ↦ (Real.sqrt (t + T₀))⁻¹)
      (-(Real.sqrt (T + T₀))⁻¹ ^ 2 * (1 / (2 * Real.sqrt (T + T₀)))) T := by
    have h0 := h2.inv hs
    refine h0.congr_deriv ?_
    field_simp [hssq]
  have hsigt : HasDerivAt (fun t : ℝ ↦ σ + ε * ψ₁ * k * (Real.sqrt (t + T₀))⁻¹)
      (ε * ψ₁ * k * (-(Real.sqrt (T + T₀))⁻¹ ^ 2 * (1 / (2 * Real.sqrt (T + T₀))))) T := by
    have h0 := (hinv.const_mul (ε * ψ₁ * k)).add_const σ
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards with t
    ring
  have hsq : HasDerivAt (fun t : ℝ ↦ (σ + ε * ψ₁ * k * (Real.sqrt (t + T₀))⁻¹) ^ 2)
      (2 * (σ + ε * ψ₁ * k * (Real.sqrt (T + T₀))⁻¹)
        * (ε * ψ₁ * k * (-(Real.sqrt (T + T₀))⁻¹ ^ 2 * (1 / (2 * Real.sqrt (T + T₀)))))) T :=
    (hsigt.fun_pow 2).congr_deriv (by ring)
  have hid : HasDerivAt (fun t : ℝ ↦ t) 1 T := hasDerivAt_id T
  have hmul := hsq.mul hid
  have hfun : (fun t : ℝ ↦ (σ + ε * ψ₁ * k * (Real.sqrt (t + T₀))⁻¹) ^ 2 * t)
      = fun t ↦ totalVar σ ψ₁ T₀ ε k t := by
    funext t
    unfold totalVar smileSurface
    field_simp
  have hfin := hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun hfun))
  refine hfin.congr_deriv ?_
  have hne : (T + T₀) * Real.sqrt (T + T₀) ≠ 0 := mul_ne_zero hT₀ne hs
  unfold smileSurface
  field_simp [hne, hs]
  simp only [hssq]
  ring

/-! ## The composite chains in `(k, w)`: an abstract inner function `u` -/

/-- The `k`-chain of `d₊` through a moving inner function `u` (the total
variance composite): `∂_k d₊(k, u(k)) = ∂_k d₊ + ∂_w d₊·u'` at `x`, with
`∂_k d₊ = −1/√w` and `∂_w d₊ = (k + w/2)/(2w^{3/2})`. -/
private theorem hasDerivAt_dpl_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y ↦ dpl y (u y))
      (-(1 / Real.sqrt (u x)) + (x + u x / 2) / (2 * u x * Real.sqrt (u x)) * ub) x := by
  have hne : Real.sqrt (u x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (u x) ^ 2 = u x := Real.sq_sqrt hpos.le
  have hnum : HasDerivAt (fun y : ℝ ↦ -y + u y / 2) (-1 + ub / 2) x :=
    (hasDerivAt_id x).neg.add (hu.div_const 2)
  have hden : HasDerivAt (fun y : ℝ ↦ Real.sqrt (u y)) (ub / (2 * Real.sqrt (u x))) x :=
    hu.sqrt hpos.ne'
  have hq := hnum.div hden hne
  unfold dpl
  refine hq.congr_deriv ?_
  field_simp [hsq]
  simp only [hsq]
  ring

/-- The `k`-chain of `d₋` through a moving `u` (mirror of `hasDerivAt_dpl_comp`:
`∂_w d₋ = (k − w/2)/(2w^{3/2})`). -/
private theorem hasDerivAt_dmi_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y ↦ dmi y (u y))
      (-(1 / Real.sqrt (u x)) + (x - u x / 2) / (2 * u x * Real.sqrt (u x)) * ub) x := by
  have hne : Real.sqrt (u x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (u x) ^ 2 = u x := Real.sq_sqrt hpos.le
  have hnum : HasDerivAt (fun y : ℝ ↦ -y - u y / 2) (-1 - ub / 2) x :=
    (hasDerivAt_id x).neg.sub (hu.div_const 2)
  have hden : HasDerivAt (fun y : ℝ ↦ Real.sqrt (u y)) (ub / (2 * Real.sqrt (u x))) x :=
    hu.sqrt hpos.ne'
  have hq := hnum.div hden hne
  unfold dmi
  refine hq.congr_deriv ?_
  field_simp [hsq]
  simp only [hsq]
  ring

/-- The `k`-chain of `e^k·Φ(d₋(k, u(k)))` through a moving `u` — the strike
side of the Black form. -/
private theorem hasDerivAt_exp_Phi_dmi_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y ↦ Real.exp y * Phi (dmi y (u y)))
      (Real.exp x * Phi (dmi x (u x))
        + Real.exp x * (gaussianPDFReal 0 1 (dmi x (u x))
          * (-(1 / Real.sqrt (u x)) + (x - u x / 2) / (2 * u x * Real.sqrt (u x)) * ub))) x := by
  have hdmi := hasDerivAt_dmi_comp hu hpos
  have hPhi := (hasDerivAt_Phi (dmi x (u x))).comp x hdmi
  rw [Function.comp_def] at hPhi
  exact ((hasDerivAt_exp x).mul hPhi).congr_deriv (by ring)

/-- The `k`-chain of the whole Black form through a moving `u`:
`C_k/F = ϕ(d₊)·∂_k d₊^{comp} − [e^k Φ(d₋) + e^k ϕ(d₋)·∂_k d₋^{comp}]`. -/
private theorem hasDerivAt_blackForm_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y ↦ blackForm y (u y))
      (gaussianPDFReal 0 1 (dpl x (u x))
          * (-(1 / Real.sqrt (u x)) + (x + u x / 2) / (2 * u x * Real.sqrt (u x)) * ub)
        - (Real.exp x * Phi (dmi x (u x))
          + Real.exp x * (gaussianPDFReal 0 1 (dmi x (u x))
            * (-(1 / Real.sqrt (u x)) + (x - u x / 2) / (2 * u x * Real.sqrt (u x)) * ub)))) x := by
  have hdpl := hasDerivAt_dpl_comp hu hpos
  have hPhiP := (hasDerivAt_Phi (dpl x (u x))).comp x hdpl
  rw [Function.comp_def] at hPhiP
  have hex := hasDerivAt_exp_Phi_dmi_comp hu hpos
  unfold blackForm
  exact hPhiP.sub hex

/-- The `w`-chain of the Black form at fixed `k` (single slot): `∂_w c = ϕ(d₊)/(2√w)`. -/
private theorem hasDerivAt_blackForm_w {k w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun z ↦ blackForm k z)
      (gaussianPDFReal 0 1 (dpl k w) / (2 * Real.sqrt w)) w := by
  have hne : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  have hsq : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  have hden : HasDerivAt (fun z : ℝ ↦ Real.sqrt z) (1 / (2 * Real.sqrt w)) w :=
    Real.hasDerivAt_sqrt hw.ne'
  have hnP : HasDerivAt (fun z : ℝ ↦ -k + z / 2) (1 / 2) w :=
    ((hasDerivAt_id' w).div_const 2).const_add (-k)
  have hnM : HasDerivAt (fun z : ℝ ↦ -k - z / 2) (-(1 / 2)) w := by
    have h1 : HasDerivAt (fun z : ℝ ↦ z / 2) (1 / 2) w := (hasDerivAt_id w).div_const 2
    exact h1.const_sub (-k)
  have hdP := hnP.div hden hne
  have hdM := hnM.div hden hne
  have hPhiP := (hasDerivAt_Phi (dpl k w)).comp w hdP
  rw [Function.comp_def] at hPhiP
  have hPhiM := (hasDerivAt_Phi (dmi k w)).comp w hdM
  rw [Function.comp_def] at hPhiM
  have hexp := (hasDerivAt_const w (Real.exp k)).mul hPhiM
  have hfull := hPhiP.sub hexp
  refine (hfull.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with z
    unfold blackForm dpl dmi
    simp only [Pi.sub_apply, Pi.mul_apply]
  · rw [← exp_mul_pdf_dmi hw]
    field_simp [hsq]
    simp only [hsq]
    ring

/-- The `k`-chain of the vega-density quotient `ϕ(d₊(k,u(k)))/(2√(u(k)))` — the
B_w-value composite: its `k`-derivative is `B_wk + B_ww·u'` with
`B_wk = d₊ϕ(d₊)/(2w)` and `B_ww = ϕ(d₊)(k²−w−w²/4)/(4w^{5/2})`. -/
private theorem hasDerivAt_Bw_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y ↦ gaussianPDFReal 0 1 (dpl y (u y)) / (2 * Real.sqrt (u y)))
      (dpl x (u x) * gaussianPDFReal 0 1 (dpl x (u x)) / (2 * u x)
        + gaussianPDFReal 0 1 (dpl x (u x)) * (x ^ 2 - u x - u x ^ 2 / 4)
            / (4 * u x ^ 2 * Real.sqrt (u x)) * ub) x := by
  have hsq : Real.sqrt (u x) ^ 2 = u x := Real.sq_sqrt hpos.le
  have hdpl := hasDerivAt_dpl_comp hu hpos
  have hphi := (hasDerivAt_gaussianPDFReal_zero_one (dpl x (u x))).comp x hdpl
  rw [Function.comp_def] at hphi
  have hden : HasDerivAt (fun y : ℝ ↦ 2 * Real.sqrt (u y)) (ub / Real.sqrt (u x)) x := by
    have hc := (Real.hasDerivAt_sqrt hpos.ne').comp x hu
    rw [Function.comp_def] at hc
    refine (hc.const_mul 2).congr_deriv ?_
    field_simp
  have hdenne : 2 * Real.sqrt (u x) ≠ 0 :=
    (mul_pos two_pos (Real.sqrt_pos.mpr hpos)).ne'
  refine (hphi.div hden hdenne).congr_deriv ?_
  unfold dpl
  field_simp [hsq]
  simp only [hsq]
  ring

/-! ## The call's own chains: `C_k`, `C_T`, `C_kk` -/

/-- The value of the `d₋` slope composite, `∂_k d₋ + ∂_w d₋·m` at total variance `w`
and variance slope `m`. -/
private noncomputable def dminus (k w m : ℝ) : ℝ :=
  -(1 / Real.sqrt w) + (k - w / 2) / (2 * w * Real.sqrt w) * m

/-- The smile surface is affine in `k`, so positivity at one point spreads to a
neighborhood. -/
private theorem smileSurface_eventually_pos_k {σ ψ₁ T₀ ε T k : ℝ}
    (hk : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    ∀ᶠ y in nhds k, 0 < smileSurface σ ψ₁ T₀ ε y T := by
  have hcont : Continuous (fun y : ℝ ↦ smileSurface σ ψ₁ T₀ ε y T) := by
    unfold smileSurface; fun_prop
  exact hcont.continuousAt.eventually_const_lt hk

/-- Same along the maturity axis: `σ_tilde(t) = σ + εψ₁k/√(t+T₀)` is continuous at
`T`, and `t > 0` holds eventually at `T > 0`. -/
private theorem smileSurface_eventually_pos_t {σ ψ₁ T₀ ε k T : ℝ} (hT : 0 < T)
    (hS : 0 < T + T₀) (hk : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    ∀ᶠ t in nhds T, 0 < smileSurface σ ψ₁ T₀ ε k t ∧ 0 < t := by
  have hadd : ContinuousAt (fun t : ℝ ↦ t + T₀) T :=
    (continuous_id.add continuous_const).continuousAt
  have hsca : ContinuousAt (fun t : ℝ ↦ Real.sqrt (t + T₀)) T :=
    (Real.continuous_sqrt.continuousAt).comp hadd
  have hcst : ContinuousAt (fun _ : ℝ ↦ ε * ψ₁ * k) T := continuousAt_const
  have hca : ContinuousAt (fun t : ℝ ↦ smileSurface σ ψ₁ T₀ ε k t) T := by
    unfold smileSurface
    exact continuousAt_const.add (hcst.div hsca (Real.sqrt_pos.mpr hS).ne')
  filter_upwards [hca.eventually_const_lt hk, eventually_gt_nhds hT] with t h1t h2t
  exact ⟨h1t, h2t⟩

/-- **The `k`-chain of the call price** (both `k`-channels: strike `F·e^k` and
surface tilt), from `hasDerivAt_blackForm_comp` at the variance composite. -/
private theorem hasDerivAt_bsCallSmile_k {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    HasDerivAt (fun y ↦ bsCallSmile F σ ψ₁ T₀ ε y T)
      (F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
            * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                + (k + totalVar σ ψ₁ T₀ ε k T / 2)
                  / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                  * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T))
          - (Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))
              + Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
                * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                    + (k - totalVar σ ψ₁ T₀ ε k T / 2)
                      / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                      * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀))
                        * T)))))) k := by
  have hwpos : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have huc := hasDerivAt_totalVar_k (σ := σ) (ψ₁ := ψ₁) (T₀ := T₀) (ε := ε) (T := T) (x := k)
  have hcore := hasDerivAt_blackForm_comp huc hwpos
  refine (hcore.const_mul F).congr_of_eventuallyEq ?_
  filter_upwards [smileSurface_eventually_pos_k hst] with y hy
  exact bsCallSmile_eq hF hT hy

/-- **The `T`-chain of the call price** (single `(k,w)` slot: the maturity moves
only through `w`), from `hasDerivAt_blackForm_w` composed with the variance
`T`-chain. -/
private theorem hasDerivAt_bsCallSmile_t {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hS : 0 < T + T₀) (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    HasDerivAt (fun t ↦ bsCallSmile F σ ψ₁ T₀ ε k t)
      (F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)))
        * (smileSurface σ ψ₁ T₀ ε k T ^ 2
          - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T
            / ((T + T₀) * Real.sqrt (T + T₀)))) T := by
  have hwpos : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have hwt := hasDerivAt_totalVar_t (σ := σ) (ψ₁ := ψ₁) (T₀ := T₀) (ε := ε) (k := k) hS
  have hcomp := (hasDerivAt_blackForm_w (k := k) hwpos).comp T hwt
  rw [Function.comp_def] at hcomp
  refine ((hcomp.const_mul F).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [smileSurface_eventually_pos_t hT hS hst] with t ht
  exact bsCallSmile_eq hF ht.2 ht.1

/-- The variance slope `w_k(y) = 2σ_tilde(y)·(εψ₁/√(T+T₀))·T` of the total variance
`w = σ_tilde²T` along log-moneyness: `∂_k w` at `k = y` (affine in `y`). -/
noncomputable def wSlope (σ ψ₁ T₀ ε T y : ℝ) : ℝ :=
  2 * smileSurface σ ψ₁ T₀ ε y T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T

/-- Its chain: `w'' = 2·(εψ₁/√(T+T₀))²·T`, constant in `y`. -/
private theorem hasDerivAt_wSlope {σ ψ₁ T₀ ε T k : ℝ} :
    HasDerivAt (fun y ↦ wSlope σ ψ₁ T₀ ε T y)
      (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) k :=
  (((hasDerivAt_smileSurface_k.const_mul 2).mul_const _).mul_const T).congr_deriv (by ring)

/-! ## The second `k`-chain: `C_kk` and the Gatheral form of the ratio -/

/-- **The `k`-derivative of the call price, collapsed**: the spelled chain value of
`hasDerivAt_bsCallSmile_k` simplifies (via the magic identity `e^k·ϕ(d₋) = ϕ(d₊)`) to
`C_k = F·(B_w·m − e^k·Φ(d₋))` with `B_w = ϕ(d₊)/(2√w)` and `m = w'` — the vega-density
composite times the variance slope, minus the exercise side. -/
private theorem deriv_bsCallSmile_k_value {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hS : 0 < T + T₀) (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    deriv (fun x ↦ bsCallSmile F σ ψ₁ T₀ ε x T) k
      = F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
            / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)) * wSlope σ ψ₁ T₀ ε T k
          - Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))) := by
  have hw : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  rw [(hasDerivAt_bsCallSmile_k hF hT hst).deriv]
  rw [show Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
        * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
          + (k - totalVar σ ψ₁ T₀ ε k T / 2)
            / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
            * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T)))
      = (Real.exp k * gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T)))
        * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
          + (k - totalVar σ ψ₁ T₀ ε k T / 2)
            / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
            * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T)) from
    (mul_assoc _ _ _).symm,
    exp_mul_pdf_dmi hw]
  simp only [wSlope]
  field_simp [hw.ne', (Real.sqrt_pos.mpr hw).ne', (Real.sqrt_pos.mpr hS).ne']
  ring

/-- **The second `k`-chain `C_kk`** (the second `k`-derivative of the call
price, the remaining ingredient Dupire's ratio needs beyond `C_k`), assembled from the
`B_w` composite chain (`hasDerivAt_Bw_comp`), the variance-slope chain
(`hasDerivAt_wSlope`) and the exercise-side chain
(`hasDerivAt_exp_Phi_dmi_comp`) — each factor evaluated on the *collapsed*
first-derivative function of `deriv_bsCallSmile_k_value`, which closes the eventual
congruence directly. -/
private theorem hasDerivAt_deriv_bsCallSmile_k {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hS : 0 < T + T₀) (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    HasDerivAt (fun y ↦ deriv (fun x ↦ bsCallSmile F σ ψ₁ T₀ ε x T) y)
      (F * ((dpl k (totalVar σ ψ₁ T₀ ε k T)
              * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              / (2 * totalVar σ ψ₁ T₀ ε k T)
            + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              * (k ^ 2 - totalVar σ ψ₁ T₀ ε k T - totalVar σ ψ₁ T₀ ε k T ^ 2 / 4)
              / (4 * totalVar σ ψ₁ T₀ ε k T ^ 2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
              * wSlope σ ψ₁ T₀ ε T k) * wSlope σ ψ₁ T₀ ε T k
          + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
            * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)
          - (Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))
            + Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
              * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k))))) k := by
  have hwpos : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have hu : HasDerivAt (fun y ↦ totalVar σ ψ₁ T₀ ε y T) (wSlope σ ψ₁ T₀ ε T k) k :=
    hasDerivAt_totalVar_k
  have hBw := hasDerivAt_Bw_comp hu hwpos
  have hm : HasDerivAt (fun y ↦ wSlope σ ψ₁ T₀ ε T y)
      (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) k := hasDerivAt_wSlope
  have hprod := hBw.mul hm
  have hexp := hasDerivAt_exp_Phi_dmi_comp hu hwpos
  refine ((hprod.sub hexp).const_mul F).congr_of_eventuallyEq ?_
  filter_upwards [smileSurface_eventually_pos_k hst] with y hy
  exact deriv_bsCallSmile_k_value hF hT hS hy

/-! ## The Gatheral form of the ratio -/

/-- **The numerator of Dupire's ratio** in `(k, w)` coordinates: the maturity slope of
the total variance, `w_T = σ_tilde² − σ_tilde·εψ₁k·T/(T+T₀)^{3/2}` (both `T`-channels of
`w = σ_tilde²T` move). -/
noncomputable def smileN (σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  smileSurface σ ψ₁ T₀ ε k T ^ 2
    - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T / ((T + T₀) * Real.sqrt (T + T₀))

/-- **The Gatheral denominator deformation** of Dupire's ratio,
`δ = −k·w_k/w + w_k²·(k²−w−w²/4)/(4w²) + w_kk/2`, specialized to this surface (so
`w_kk/2 = (εψ₁/√(T+T₀))²·T` is spelled out); Dupire's ratio is `w_T/(1 + δ)`
(`dupireRatio_eq`). `1 + smileDelta` has the algebraic form of Durrleman's function `g`, which
`MathFin.SVI.durrleman` (`SVI/Reduction.lean`) defines for the SVI variance: where the two have the
same total variance, slope and curvature they are equal (`SVI.durrleman_eq_one_add_smileDelta`).
The SVI development (`SVI/BlackSmile.lean`) uses `dpl`, `dmi`, `blackForm` and `exp_mul_pdf_dmi`
directly, at `w = SVI.variance p k`. -/
noncomputable def smileDelta (σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  -k * wSlope σ ψ₁ T₀ ε T k / totalVar σ ψ₁ T₀ ε k T
    + wSlope σ ψ₁ T₀ ε T k ^ 2 * (k ^ 2 - totalVar σ ψ₁ T₀ ε k T
        - totalVar σ ψ₁ T₀ ε k T ^ 2 / 4) / (4 * totalVar σ ψ₁ T₀ ε k T ^ 2)
    + (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T

/-- **`dupireRatio_eq`** — the exact identity behind the module: in `(k, w)`
coordinates, Dupire's zero-rates ratio on the tilted surface is the rational function
`R = w_T/(1 + δ)` (the Gatheral form). Everything downstream is calculus on the
explicit right-hand side. -/
theorem dupireRatio_eq {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T) (hS : 0 < T + T₀)
    (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    dupireRatio F σ ψ₁ T₀ ε k T
      = smileN σ ψ₁ T₀ ε k T / (1 + smileDelta σ ψ₁ T₀ ε k T) := by
  have hw : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have hsne : Real.sqrt (totalVar σ ψ₁ T₀ ε k T) ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  have hI :
      (F * ((dpl k (totalVar σ ψ₁ T₀ ε k T)
                * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
                / (2 * totalVar σ ψ₁ T₀ ε k T)
              + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
                * (k ^ 2 - totalVar σ ψ₁ T₀ ε k T - totalVar σ ψ₁ T₀ ε k T ^ 2 / 4)
                / (4 * totalVar σ ψ₁ T₀ ε k T ^ 2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                * wSlope σ ψ₁ T₀ ε T k) * wSlope σ ψ₁ T₀ ε T k
            + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
                / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
              * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)
            - (Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))
              + Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
                * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k))))
        - F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)) * wSlope σ ψ₁ T₀ ε T k
            - Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))))
      = F * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          / Real.sqrt (totalVar σ ψ₁ T₀ ε k T) * (1 + smileDelta σ ψ₁ T₀ ε k T) := by
    have hexp : Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
        * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k))
        = gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k) := by
      rw [← mul_assoc, exp_mul_pdf_dmi hw]
    rw [hexp]
    simp only [dminus, dpl]
    unfold smileDelta
    field_simp [hw.ne', hsne]
    ring
  unfold dupireRatio
  rw [(hasDerivAt_bsCallSmile_t hF hT hS hst).deriv, deriv_bsCallSmile_k_value hF hT hS hst,
    (hasDerivAt_deriv_bsCallSmile_k hF hT hS hst).deriv, hI]
  have hA : F * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
      / Real.sqrt (totalVar σ ψ₁ T₀ ε k T) ≠ 0 :=
    div_ne_zero (mul_ne_zero hF.ne' (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne') hsne
  have htwo : 2 * (F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
        / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)))
        * (smileSurface σ ψ₁ T₀ ε k T ^ 2
          - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T / ((T + T₀) * Real.sqrt (T + T₀))))
      = F * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          / Real.sqrt (totalVar σ ψ₁ T₀ ε k T) * smileN σ ψ₁ T₀ ε k T := by
    unfold smileN
    field_simp
  rw [htwo]
  field_simp [hA, (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne']

/-! ## The `k = 0` extraction -/

/-- At the money the total variance is `σ²T`, independent of the tilt. -/
private theorem totalVar_zero (σ ψ₁ T₀ ε T : ℝ) : totalVar σ ψ₁ T₀ ε 0 T = σ ^ 2 * T := by
  unfold totalVar
  rw [smileSurface_atm]

/-- At the money the variance slope is `m₀ = 2σ·(εψ₁/√(T+T₀))·T` — linear in `ε`. -/
private theorem wSlope_zero (σ ψ₁ T₀ ε T : ℝ) :
    wSlope σ ψ₁ T₀ ε T 0 = 2 * σ * (ε * ψ₁ / Real.sqrt (T + T₀)) * T := by
  unfold wSlope
  rw [smileSurface_atm]

/-- The `T`-chain numerator at the money: `w_T(ε, 0) = σ²`, tilt-free. -/
private theorem smileN_zero (σ ψ₁ T₀ ε T : ℝ) : smileN σ ψ₁ T₀ ε 0 T = σ ^ 2 := by
  unfold smileN
  rw [smileSurface_atm]
  ring

/-- The `k`-slope of the numerator at the money (the value of `hasDerivAt_smileN_k`). -/
private noncomputable def smileNk (σ ψ₁ T₀ ε T : ℝ) : ℝ :=
  2 * σ * (ε * ψ₁ / Real.sqrt (T + T₀))
    - σ * (ε * ψ₁) * T / ((T + T₀) * Real.sqrt (T + T₀))

private theorem smileNk_zero (σ ψ₁ T₀ T : ℝ) : smileNk σ ψ₁ T₀ 0 T = 0 := by
  unfold smileNk
  simp

/-- The `k`-slope of the Gatheral deformation at the money (the value of
`hasDerivAt_smileDelta_k`). -/
private noncomputable def smileDk (σ ψ₁ T₀ ε T : ℝ) : ℝ :=
  -(wSlope σ ψ₁ T₀ ε T 0 / totalVar σ ψ₁ T₀ ε 0 T)
    + ((((-wSlope σ ψ₁ T₀ ε T 0 - totalVar σ ψ₁ T₀ ε 0 T * wSlope σ ψ₁ T₀ ε T 0 / 2)
            * wSlope σ ψ₁ T₀ ε T 0 ^ 2
        + (-totalVar σ ψ₁ T₀ ε 0 T - totalVar σ ψ₁ T₀ ε 0 T ^ 2 / 4)
            * (2 * wSlope σ ψ₁ T₀ ε T 0 * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)))
        * (4 * totalVar σ ψ₁ T₀ ε 0 T ^ 2)
      - (-totalVar σ ψ₁ T₀ ε 0 T - totalVar σ ψ₁ T₀ ε 0 T ^ 2 / 4)
          * wSlope σ ψ₁ T₀ ε T 0 ^ 2 * (4 * (2 * totalVar σ ψ₁ T₀ ε 0 T * wSlope σ ψ₁ T₀ ε T 0)))
      / (4 * totalVar σ ψ₁ T₀ ε 0 T ^ 2) ^ 2)

private theorem smileDelta_zero (σ ψ₁ T₀ T : ℝ) : smileDelta σ ψ₁ T₀ 0 0 T = 0 := by
  unfold smileDelta
  rw [totalVar_zero, wSlope_zero]
  simp

private theorem smileDk_zero (σ ψ₁ T₀ T : ℝ) : smileDk σ ψ₁ T₀ 0 T = 0 := by
  unfold smileDk
  rw [totalVar_zero, wSlope_zero]
  simp

/-- The numerator of the ATM `k`-slope of the ratio: quotient-rule value
`N'(0)·D(0) − N(0)·D'(0)` in the `(k = 0)` slice. -/
private noncomputable def slopeNum (σ ψ₁ T₀ ε T : ℝ) : ℝ :=
  smileNk σ ψ₁ T₀ ε T * (1 + smileDelta σ ψ₁ T₀ ε 0 T)
    - smileN σ ψ₁ T₀ ε 0 T * smileDk σ ψ₁ T₀ ε T

private theorem slopeNum_zero (σ ψ₁ T₀ T : ℝ) : slopeNum σ ψ₁ T₀ 0 T = 0 := by
  unfold slopeNum
  rw [smileNk_zero, smileDelta_zero, smileN_zero, smileDk_zero]
  simp

/-- The `k`-chain of the numerator `w_T` at the money. -/
private theorem hasDerivAt_smileN_k {σ ψ₁ T₀ ε T : ℝ} :
    HasDerivAt (fun k ↦ smileN σ ψ₁ T₀ ε k T) (smileNk σ ψ₁ T₀ ε T) 0 := by
  have hs : HasDerivAt (fun k ↦ smileSurface σ ψ₁ T₀ ε k T) (ε * ψ₁ / Real.sqrt (T + T₀)) 0 :=
    hasDerivAt_smileSurface_k
  have hs2 : HasDerivAt (fun k ↦ smileSurface σ ψ₁ T₀ ε k T ^ 2)
      (2 * smileSurface σ ψ₁ T₀ ε 0 T ^ (2 - 1) * (ε * ψ₁ / Real.sqrt (T + T₀))) 0 :=
    hs.fun_pow 2
  have hkm : HasDerivAt (fun k ↦ smileSurface σ ψ₁ T₀ ε k T * k)
      ((ε * ψ₁ / Real.sqrt (T + T₀)) * 0 + smileSurface σ ψ₁ T₀ ε 0 T * 1) 0 :=
    hs.mul (hasDerivAt_id 0)
  have hsub := hs2.sub (hkm.const_mul (ε * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀))))
  refine (hsub.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with k
    simp only [Pi.sub_apply]
    unfold smileN
    ring
  · rw [smileSurface_atm]
    unfold smileNk
    ring

/-- The `k`-chain of the Gatheral deformation `δ` at the money. -/
private theorem hasDerivAt_smileDelta_k {σ ψ₁ T₀ ε T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun k ↦ smileDelta σ ψ₁ T₀ ε k T) (smileDk σ ψ₁ T₀ ε T) 0 := by
  have hw0 : 0 < totalVar σ ψ₁ T₀ ε 0 T := by rw [totalVar_zero]; positivity
  have hw0ne := hw0.ne'
  have hm : HasDerivAt (fun k ↦ wSlope σ ψ₁ T₀ ε T k)
      (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) 0 := hasDerivAt_wSlope
  have hw : HasDerivAt (fun k ↦ totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T 0) 0 :=
    hasDerivAt_totalVar_k
  have hkm : HasDerivAt (fun k ↦ k * wSlope σ ψ₁ T₀ ε T k)
      (1 * wSlope σ ψ₁ T₀ ε T 0 + 0 * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)) 0 :=
    (hasDerivAt_id 0).mul hm
  have ht1 := (hkm.div hw hw0ne).neg
  have hk2 : HasDerivAt (fun k ↦ k ^ 2) ((2:ℝ) * 0 ^ (2 - 1)) 0 := hasDerivAt_pow 2 0
  have hc2 : HasDerivAt (fun k ↦ totalVar σ ψ₁ T₀ ε k T ^ 2)
      (2 * totalVar σ ψ₁ T₀ ε 0 T ^ (2 - 1) * wSlope σ ψ₁ T₀ ε T 0) 0 :=
    hw.fun_pow 2
  have hA := (hk2.sub hw).sub (hc2.div_const 4)
  have hm2 : HasDerivAt (fun k ↦ wSlope σ ψ₁ T₀ ε T k ^ 2)
      (2 * wSlope σ ψ₁ T₀ ε T 0 ^ (2 - 1) * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)) 0 :=
    hm.fun_pow 2
  have hAm := hA.mul hm2
  have h4 : HasDerivAt (fun k ↦ 4 * totalVar σ ψ₁ T₀ ε k T ^ 2)
      (4 * (2 * totalVar σ ψ₁ T₀ ε 0 T ^ (2 - 1) * wSlope σ ψ₁ T₀ ε T 0)) 0 := hc2.const_mul 4
  have h4ne : 4 * totalVar σ ψ₁ T₀ ε 0 T ^ 2 ≠ 0 := by rw [totalVar_zero]; positivity
  have ht2 := hAm.div h4 h4ne
  have ht3 : HasDerivAt (fun k : ℝ ↦ (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) 0 0 :=
    hasDerivAt_const 0 ((ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)
  have hsum := ht1.add (ht2.add ht3)
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with k
    unfold smileDelta
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply]
    ring
  · unfold smileDk
    simp only [Pi.sub_apply, Pi.mul_apply]
    field_simp [hw0ne, h4ne]
    ring

/-- **The ATM `k`-chain of Dupire's ratio itself**: at every tilt `ε` with nondegenerate
denominator, `∂_k R(ε, ·, T)|₀ = slopeNum/(1 + δ₀)²` — the quotient rule on
`dupireRatio_eq`. -/
private theorem hasDerivAt_dupireRatio_k_zero {F σ ψ₁ T₀ ε T : ℝ} (hF : 0 < F) (hσ : 0 < σ)
    (hT : 0 < T) (hS : 0 < T + T₀) (hD0ne : 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0) :
    HasDerivAt (fun k ↦ dupireRatio F σ ψ₁ T₀ ε k T)
      (slopeNum σ ψ₁ T₀ ε T / (1 + smileDelta σ ψ₁ T₀ ε 0 T) ^ 2) 0 := by
  have hst : 0 < smileSurface σ ψ₁ T₀ ε 0 T := by rwa [smileSurface_atm]
  have hN : HasDerivAt (fun k ↦ smileN σ ψ₁ T₀ ε k T) (smileNk σ ψ₁ T₀ ε T) 0 :=
    hasDerivAt_smileN_k
  have hD : HasDerivAt (fun k ↦ smileDelta σ ψ₁ T₀ ε k T) (smileDk σ ψ₁ T₀ ε T) 0 :=
    hasDerivAt_smileDelta_k hσ hT
  have hD1 := hD.const_add 1
  have hQ := hN.div hD1 hD0ne
  refine hQ.congr_of_eventuallyEq ?_
  filter_upwards [smileSurface_eventually_pos_k hst] with k hk
  exact dupireRatio_eq hF hT hS hk

/-! ## The `ε`-extraction at zero tilt -/

/-- The ATM Gatheral deformation is exactly quadratic in the tilt:
`δ(ε, 0) = ε²·d₂` with `d₂` tilt-free. -/
private noncomputable def smileD2 (σ ψ₁ T₀ T : ℝ) : ℝ :=
  (2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T) ^ 2
    * (-(σ ^ 2 * T) - (σ ^ 2 * T) ^ 2 / 4) / (4 * (σ ^ 2 * T) ^ 2)
  + (ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T

private theorem smileDelta_zero_fac {σ ψ₁ T₀ T : ℝ} (ε : ℝ) :
    smileDelta σ ψ₁ T₀ ε 0 T = ε ^ 2 * smileD2 σ ψ₁ T₀ T := by
  unfold smileDelta smileD2
  rw [totalVar_zero, wSlope_zero]
  ring

/-- Near zero tilt the deformed denominator stays nondegenerate. -/
private theorem eventually_one_add_smileDelta_ne_zero {σ ψ₁ T₀ T : ℝ} :
    ∀ᶠ ε in nhds 0, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 := by
  have hc : Continuous fun ε : ℝ ↦ 1 + ε ^ 2 * smileD2 σ ψ₁ T₀ T := by fun_prop
  have ht : Filter.Tendsto (fun ε : ℝ ↦ 1 + ε ^ 2 * smileD2 σ ψ₁ T₀ T) (nhds 0) (nhds 1) := by
    simpa using hc.tendsto 0
  simpa only [smileDelta_zero_fac] using ht.eventually_ne one_ne_zero

/-- The `ε`-chain of `N'(0; ε)` — linear in the tilt. -/
private theorem hasDerivAt_smileNk_eps {σ ψ₁ T₀ T : ℝ} :
    HasDerivAt (fun ε ↦ smileNk σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ / Real.sqrt (T + T₀) - σ * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀))) 0 := by
  have hcore := (hasDerivAt_id 0).const_mul
    (2 * σ * ψ₁ / Real.sqrt (T + T₀) - σ * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀)))
  refine (hcore.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with ε
  unfold smileNk
  simp only [id_eq]
  ring

/-- The `ε`-chain of the ATM numerator `N(ε, 0) = σ²` — constant in the tilt. -/
private theorem hasDerivAt_smileN_zero_eps {σ ψ₁ T₀ T : ℝ} :
    HasDerivAt (fun ε ↦ smileN σ ψ₁ T₀ ε 0 T) 0 0 := by
  refine (hasDerivAt_const 0 (σ ^ 2)).congr_of_eventuallyEq ?_
  filter_upwards with ε
  exact smileN_zero σ ψ₁ T₀ ε T

/-- The `ε`-chain of the deformed denominator `1 + δ(ε, 0) = 1 + ε²d₂`. -/
private theorem hasDerivAt_one_add_smileDelta_eps {σ ψ₁ T₀ T : ℝ} :
    HasDerivAt (fun ε ↦ 1 + smileDelta σ ψ₁ T₀ ε 0 T) 0 0 := by
  have hcore := (hasDerivAt_const 0 (1 : ℝ)).add
    ((hasDerivAt_pow 2 0).const_mul (smileD2 σ ψ₁ T₀ T))
  refine (hcore.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with ε
  simp only [Pi.add_apply]
  rw [smileDelta_zero_fac]
  ring

/-- The `ε`-chain of the ATM deformation slope `δ'(0; ε)`: tilt-linear part from the
`−k·w_k/w` term; every other term is `O(ε²)` at the money. -/
private theorem hasDerivAt_smileDk_eps {σ ψ₁ T₀ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun ε ↦ smileDk σ ψ₁ T₀ ε T)
      (-(2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T / (σ ^ 2 * T))) 0 := by
  have hWne : σ ^ 2 * T ≠ 0 := mul_ne_zero (pow_ne_zero 2 hσ.ne') hT.ne'
  have hDENne : (4 * (σ ^ 2 * T) ^ 2) ^ 2 ≠ 0 := by positivity
  have hid : HasDerivAt (fun ε ↦ ε * ψ₁ / Real.sqrt (T + T₀))
      (ψ₁ / Real.sqrt (T + T₀)) 0 :=
    (((hasDerivAt_id' 0).mul_const ψ₁).div_const _).congr_deriv (by ring)
  have hM := (hid.const_mul (2 * σ)).mul_const T
  have hM2 := hM.fun_pow 2
  have hq := hid.fun_pow 2
  have hq2 := (hq.const_mul 2).const_mul T
  have hW : HasDerivAt (fun _ : ℝ ↦ σ ^ 2 * T) 0 0 := hasDerivAt_const 0 (σ ^ 2 * T)
  have hAp := ((hasDerivAt_const 0 (0 : ℝ)).sub hM).sub ((hW.mul hM).div_const 2)
  have hA0 : HasDerivAt (fun _ : ℝ ↦ 0 ^ 2 - σ ^ 2 * T - (σ ^ 2 * T) ^ 2 / 4) 0 0 :=
    hasDerivAt_const 0 (0 ^ 2 - σ ^ 2 * T - (σ ^ 2 * T) ^ 2 / 4)
  have hmid := (hAp.mul hM2).add (hA0.mul ((hM.mul hq2).const_mul 2))
  have hNUM := (hmid.mul (hasDerivAt_const 0 (4 * (σ ^ 2 * T) ^ 2))).sub
    (hA0.mul (hM2.mul (((hW.mul hM).const_mul 4).const_mul 2)))
  have hDENc : HasDerivAt (fun _ : ℝ ↦ (4 * (σ ^ 2 * T) ^ 2) ^ 2) 0 0 :=
    hasDerivAt_const 0 ((4 * (σ ^ 2 * T) ^ 2) ^ 2)
  have hBIG := hNUM.div hDENc hDENne
  have htot := (hM.div hW hWne).neg.add hBIG
  refine (htot.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with ε
    unfold smileDk
    rw [totalVar_zero, wSlope_zero]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply]
    ring
  · field_simp [hWne, hDENne]
    ring

/-- **The `ε`-chain of the ATM slope numerator**: `∂_ε[slopeNum]|₀ =
2σψ₁((3/2)T + 2T₀)/(T+T₀)^{3/2}`, the eq-10.8 coefficient. -/
private theorem hasDerivAt_slopeNum {σ ψ₁ T₀ T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hS : 0 < T + T₀) :
    HasDerivAt (fun ε ↦ slopeNum σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀))) 0 := by
  have h1 : HasDerivAt (fun ε ↦ smileNk σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ / Real.sqrt (T + T₀) - σ * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀))) 0 :=
    hasDerivAt_smileNk_eps
  have h2 : HasDerivAt (fun ε ↦ 1 + smileDelta σ ψ₁ T₀ ε 0 T) 0 0 :=
    hasDerivAt_one_add_smileDelta_eps
  have h3 : HasDerivAt (fun ε ↦ smileN σ ψ₁ T₀ ε 0 T) 0 0 :=
    hasDerivAt_smileN_zero_eps
  have h4 : HasDerivAt (fun ε ↦ smileDk σ ψ₁ T₀ ε T)
      (-(2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T / (σ ^ 2 * T))) 0 :=
    hasDerivAt_smileDk_eps hσ hT
  have hcomb := (h1.mul h2).sub (h3.mul h4)
  refine (hcomb.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with ε
    simp only [Pi.sub_apply, Pi.mul_apply]
    unfold slopeNum
    rfl
  · rw [smileDelta_zero, smileNk_zero, smileN_zero]
    field_simp [hσ.ne', hT.ne', (Real.sqrt_pos.mpr hS).ne']
    ring

/-- **Eq 10.8**: for `F, σ, T, T₀ > 0`, the ATM `k`-slope of Dupire's ratio has ε-slope
`2σψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}` — the first-order-in-ε coefficient of the local-variance
ATM skew implied by the tilted surface, reading `R` as `σ_loc²` (Dupire's ratio enters as a
definition). -/
theorem dupireRatio_k_slope {F σ ψ₁ T₀ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T)
    (h₀ : 0 < T₀) :
    deriv (fun ε ↦ deriv (fun k ↦ dupireRatio F σ ψ₁ T₀ ε k T) 0) 0
      = 2 * σ * ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀)) := by
  have hS : 0 < T + T₀ := by linarith
  have hD2ε :=
    (hasDerivAt_one_add_smileDelta_eps (σ := σ) (ψ₁ := ψ₁) (T₀ := T₀) (T := T)).fun_pow 2
  have hD2ne : (1 + smileDelta σ ψ₁ T₀ 0 0 T) ^ 2 ≠ 0 := by
    rw [smileDelta_zero]; norm_num
  have hQ := (hasDerivAt_slopeNum (ψ₁ := ψ₁) hσ hT hS).div hD2ε hD2ne
  rw [smileDelta_zero, slopeNum_zero] at hQ
  refine (hasDerivAt_deriv_param_of_eventually
    (eventually_one_add_smileDelta_ne_zero.mono fun ε hε ↦
      hasDerivAt_dupireRatio_k_zero hF hσ hT hS hε) (hQ.congr_deriv ?_)).deriv
  norm_num

/-! ## The `σ_loc` reading -/

/-- The closed form of the first-order-in-ε local-vol ATM skew of the tilted surface,
`ψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}` (with `(T+T₀)^{3/2}` rendered as `(T+T₀)·√(T+T₀)`);
`dupireRatio_sqrt_slope` identifies it with the ε-slope of the ATM `k`-slope of `√R` for
`F, σ, T, T₀ > 0`. -/
noncomputable def localSkew (ψ₁ T₀ T : ℝ) : ℝ :=
  ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀))

/-- **The local-vol ATM skew** (eq 10.8's square-root reading): the ε-slope of the
ATM `k`-slope of `√R` — a first-order-in-ε reading of the local vol implied by the
surface, not the actual skew of the `ε = 1` surface (which carries `O(ψ₁³)`
corrections, not proved here) — is `localSkew ψ₁ T₀ T` for every `T > 0`, given
`F, σ, T₀ > 0`. The closed form at `T = 0` is twice the implied ATM skew (`localSkew_zero`);
as `T → ∞` it behaves like `(3/2)ψ₁/√T` (`tendsto_localSkew_mul_sqrt_atTop`). -/
theorem dupireRatio_sqrt_slope {F σ ψ₁ T₀ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T)
    (h₀ : 0 < T₀) :
    deriv (fun ε ↦ deriv (fun k ↦ Real.sqrt (dupireRatio F σ ψ₁ T₀ ε k T)) 0) 0
      = localSkew ψ₁ T₀ T := by
  unfold localSkew
  have hS : 0 < T + T₀ := by linarith
  have hev : ∀ᶠ ε in nhds 0, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 :=
    eventually_one_add_smileDelta_ne_zero
  have hR0ne (ε : ℝ) (hε : 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0) :
      dupireRatio F σ ψ₁ T₀ ε 0 T ≠ 0 := by
    have hst : 0 < smileSurface σ ψ₁ T₀ ε 0 T := by rwa [smileSurface_atm]
    rw [dupireRatio_eq hF hT hS hst, smileN_zero]
    exact div_ne_zero (pow_ne_zero 2 hσ.ne') hε
  have hR0sq (ε : ℝ) : Real.sqrt (dupireRatio F σ ψ₁ T₀ ε 0 T)
      = σ / Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T) := by
    have hst : 0 < smileSurface σ ψ₁ T₀ ε 0 T := by rwa [smileSurface_atm]
    rw [dupireRatio_eq hF hT hS hst, smileN_zero, Real.sqrt_div (sq_nonneg σ),
      Real.sqrt_sq hσ.le]
  have hchain (ε : ℝ) (hε : 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0) :
      deriv (fun k ↦ Real.sqrt (dupireRatio F σ ψ₁ T₀ ε k T)) 0
        = (1 / (2 * (σ / Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T))))
          * (slopeNum σ ψ₁ T₀ ε T / (1 + smileDelta σ ψ₁ T₀ ε 0 T) ^ 2) := by
    have hBigk := hasDerivAt_dupireRatio_k_zero hF hσ hT hS hε
    have hsq := (Real.hasDerivAt_sqrt (hR0ne ε hε)).comp 0 hBigk
    rw [Function.comp_def] at hsq
    rw [hsq.deriv, hR0sq ε]
  have hSn : HasDerivAt (fun ε ↦ slopeNum σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀))) 0 :=
    hasDerivAt_slopeNum hσ hT hS
  have hD0ε : HasDerivAt (fun ε ↦ 1 + smileDelta σ ψ₁ T₀ ε 0 T) 0 0 :=
    hasDerivAt_one_add_smileDelta_eps
  have hD0ne : (1 : ℝ) + smileDelta σ ψ₁ T₀ 0 0 T ≠ 0 := by rw [smileDelta_zero]; norm_num
  have hsD0 := (Real.hasDerivAt_sqrt hD0ne).comp 0 hD0ε
  rw [Function.comp_def] at hsD0
  have hD2ε := hD0ε.fun_pow 2
  have hD2ne : (1 + smileDelta σ ψ₁ T₀ 0 0 T) ^ 2 ≠ 0 := by
    rw [smileDelta_zero]; norm_num
  have hV := hSn.div hD2ε hD2ne
  have hprod := hV.mul hsD0
  have h2σ : HasDerivAt (fun _ : ℝ ↦ 2 * σ) 0 0 := hasDerivAt_const 0 (2 * σ)
  have hfin := hprod.div h2σ (mul_ne_zero two_pos.ne' hσ.ne')
  refine (hfin.congr_deriv ?_).congr_of_eventuallyEq ?_ |>.deriv
  · rw [show (1 : ℝ) + smileDelta σ ψ₁ T₀ 0 0 T = 1 from by rw [smileDelta_zero]; norm_num,
      Real.sqrt_one, slopeNum_zero]
    field_simp [hσ.ne', hT.ne', hS.ne', (Real.sqrt_pos.mpr hS).ne']
    ring
  · filter_upwards [hev] with ε hε
    rw [hchain ε hε]
    simp only [Pi.mul_apply, Pi.div_apply]
    by_cases hD : 0 < 1 + smileDelta σ ψ₁ T₀ ε 0 T
    · have hs0 : Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hD)
      have hD0 : 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 := ne_of_gt hD
      field_simp [hσ.ne', hs0, hD0]
    · have hsq0 : Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T) = 0 :=
        (Real.sqrt_eq_zero' (x := 1 + smileDelta σ ψ₁ T₀ ε 0 T)).mpr (not_lt.mp hD)
      rw [hsq0]
      simp

/-! ## Corollaries -/

/-- **The rule of two, on the closed form**: for `T₀ > 0`, `localSkew` at `T = 0` is `2·(ψ₁/√T₀)`,
twice the implied ATM skew `ψ₁/√T₀`. An algebraic identity on the closed form;
`dupireRatio_sqrt_slope` identifies the closed form with the skew only for `T > 0`. -/
theorem localSkew_zero (ψ₁ T₀ : ℝ) (h₀ : 0 < T₀) :
    localSkew ψ₁ T₀ 0 = 2 * (ψ₁ / Real.sqrt T₀) := by
  unfold localSkew
  norm_num
  field_simp [(Real.sqrt_pos.mpr h₀).ne']

/-- **The rule of two as a limit**: `localSkew` tends, as `T → 0`, to `2·(ψ₁/√T₀)`, the
value of `localSkew_zero` (continuity of the closed form at `0`). -/
theorem tendsto_localSkew_nhds_zero (ψ₁ T₀ : ℝ) (h₀ : 0 < T₀) :
    Filter.Tendsto (fun T ↦ localSkew ψ₁ T₀ T) (nhds 0) (nhds (2 * (ψ₁ / Real.sqrt T₀))) := by
  have h : ContinuousAt (fun T ↦ localSkew ψ₁ T₀ T) 0 := by
    change ContinuousAt (fun T : ℝ ↦ ψ₁ * ((3 / 2) * T + 2 * T₀)
      / ((T + T₀) * Real.sqrt (T + T₀))) 0
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp only [zero_add]; positivity)
  rw [← localSkew_zero ψ₁ T₀ h₀]
  exact h.tendsto

/-- **The calendar-time asymptotic** of the closed form: `localSkew ψ₁ T₀ T · √T` tends to
`(3/2)ψ₁` as `T → ∞`. -/
theorem tendsto_localSkew_mul_sqrt_atTop (ψ₁ T₀ : ℝ) :
    Filter.Tendsto (fun T ↦ localSkew ψ₁ T₀ T * Real.sqrt T) Filter.atTop
      (nhds ((3 / 2) * ψ₁)) := by
  unfold localSkew
  have hinv : Filter.Tendsto (fun T : ℝ ↦ (T + T₀)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ T₀ Filter.tendsto_id)
  have hA : Filter.Tendsto (fun T : ℝ ↦ (3 / 2 : ℝ) + (T₀ / 2) * (T + T₀)⁻¹)
      Filter.atTop (nhds ((3 / 2 : ℝ) + (T₀ / 2) * 0)) :=
    (tendsto_const_nhds (x := (3 / 2 : ℝ))).add ((tendsto_const_nhds (x := T₀ / 2)).mul hinv)
  rw [show ((3 : ℝ) / 2 + (T₀ / 2) * 0) = 3 / 2 from by norm_num] at hA
  have hM0 : Filter.Tendsto (fun T : ℝ ↦ 1 - T₀ * (T + T₀)⁻¹) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := T₀)).mul hinv))
  have hM : Filter.Tendsto (fun T : ℝ ↦ Real.sqrt (1 - T₀ * (T + T₀)⁻¹)) Filter.atTop
      (nhds (1 : ℝ)) := by
    simpa using hM0.sqrt
  have hfin := (tendsto_const_nhds (x := ψ₁)).mul (hA.mul hM)
  rw [mul_one] at hfin
  rw [show ψ₁ * ((3 : ℝ) / 2) = (3 / 2) * ψ₁ from by ring] at hfin
  refine hfin.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (-T₀), Filter.eventually_ge_atTop 0] with T hT hT0
  have hne : T + T₀ ≠ 0 := by linarith
  have hpos : 0 < T + T₀ := by linarith
  have hinner : 1 - T₀ * (T + T₀)⁻¹ = T / (T + T₀) := by
    field_simp [hne]
    ring
  rw [hinner, Real.sqrt_div hT0]
  field_simp [hne, (Real.sqrt_pos.mpr hpos).ne']
  ring

/-! ## The rule of two on the surface itself -/

/-- **The implied ATM skew, first order in ε**: the ε-slope at `ε = 0` of the ATM `k`-slope of
the implied-volatility surface is `ψ₁/√(T+T₀)` (the surface is affine in `k`). -/
theorem smileSurface_skew_slope (σ ψ₁ T₀ T : ℝ) :
    deriv (fun ε ↦ deriv (fun k ↦ smileSurface σ ψ₁ T₀ ε k T) 0) 0
      = ψ₁ / Real.sqrt (T + T₀) := by
  have h : (fun ε ↦ deriv (fun k ↦ smileSurface σ ψ₁ T₀ ε k T) 0)
      = fun ε ↦ ε * (ψ₁ / Real.sqrt (T + T₀)) :=
    funext fun ε ↦ (hasDerivAt_smileSurface_k (σ := σ) (ψ₁ := ψ₁) (T₀ := T₀) (ε := ε)
      (T := T) (x := 0)).deriv.trans (mul_div_assoc ε ψ₁ _)
  rw [h, (hasDerivAt_mul_const _).deriv]

/-- **Local versus implied ATM skew, first order in ε.** For `F, σ, T₀ > 0` and every `T > 0`,
the ε-slope of the ATM `k`-slope of `√R` (Dupire's local volatility, `R` taken as its
definition) is the ε-slope of the implied ATM skew times `((3/2)T + 2T₀)/(T + T₀)`, a factor
that decreases from `2` (as `T → 0⁺`) to `3/2` (as `T → ∞`). -/
theorem dupireRatio_sqrt_slope_eq_mul_skew {F σ ψ₁ T₀ T : ℝ} (hF : 0 < F) (hσ : 0 < σ)
    (hT : 0 < T) (h₀ : 0 < T₀) :
    deriv (fun ε ↦ deriv (fun k ↦ Real.sqrt (dupireRatio F σ ψ₁ T₀ ε k T)) 0) 0
      = ((3 / 2) * T + 2 * T₀) / (T + T₀)
        * deriv (fun ε ↦ deriv (fun k ↦ smileSurface σ ψ₁ T₀ ε k T) 0) 0 := by
  rw [dupireRatio_sqrt_slope hF hσ hT h₀, smileSurface_skew_slope, localSkew,
    div_mul_div_comm, mul_comm ψ₁]

/-- **The rule of two on the tilted surface.** For `F, σ, T₀ > 0`, as `T → 0⁺` the
first-order-in-ε local-volatility ATM skew (the ε-slope of the ATM `k`-slope of `√R`) tends to
twice the first-order implied ATM skew at `T = 0`, `2·ψ₁/√T₀`. The statement is about the Dupire
ratio of the surface for `T > 0` (`dupireRatio_sqrt_slope`), not only about the closed form
`localSkew`. -/
theorem tendsto_dupireRatio_sqrt_slope_nhdsGT_zero {F σ ψ₁ T₀ : ℝ} (hF : 0 < F)
    (hσ : 0 < σ) (h₀ : 0 < T₀) :
    Filter.Tendsto
      (fun T ↦ deriv (fun ε ↦ deriv (fun k ↦ Real.sqrt (dupireRatio F σ ψ₁ T₀ ε k T)) 0) 0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * deriv (fun ε ↦ deriv (fun k ↦ smileSurface σ ψ₁ T₀ ε k 0) 0) 0)) := by
  rw [smileSurface_skew_slope, zero_add]
  exact ((tendsto_localSkew_nhds_zero ψ₁ T₀ h₀).mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun T hT ↦ (dupireRatio_sqrt_slope hF hσ hT h₀).symm)

end MathFin.ForwardSmile

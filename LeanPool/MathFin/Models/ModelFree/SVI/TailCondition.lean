/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.ExtendedFormula
public import LeanPool.MathFin.Models.ModelFree.PriceBounds
public import LeanPool.MathFin.Models.ModelFree.CallPriceFunction
public import LeanPool.MathFin.Probability.Gaussian.NormalTail

/-! # The tail condition for raw SVI, and butterfly-freeness

The strike-convexity certificate of `ExtendedFormula` leaves out the large-strike behaviour. A
smile is free of butterfly arbitrage when its call prices, as a function of the strike, are convex,
lie between `(1 − K)⁺` and `1`, and tend to `0` at large strikes (`IsNormalizedCallPrice`, after
Roper's Theorem 2.1). The smiled call always satisfies the bounds, so for raw SVI with `b ≥ 0`
and positive variance what convexity leaves open is the large-strike limit. The right wing of the
variance has slope `b(1 + ρ)`, and

* `tendsto_dpl_atBot_iff` — `d₊(k) → −∞` as `k → ∞`, the tail condition of
  Gatheral–Jacquier, *Arbitrage-free SVI volatility surfaces*, Lemma 2.2, holds exactly when
  `b(1 + ρ) < 2`;
* `tendsto_bsSmile_zero_iff` — the SVI-smiled call tends to `0` at large strikes exactly when
  `b(1 + ρ) < 2`;
* `butterflyFreeFormula_iff_isNormalizedCallPrice` — the strike-convexity formula with one more
  sign atom, `2 − b(1 + ρ) > 0`, holds exactly when `σ ≥ 0`, `b ≥ 0`, `ρ² ≤ 1`, the variance is
  positive, and the SVI-smiled Black–Scholes call is a normalised call price function.

The left wing gets no atom of its own: the bounds and the limit at strike `0` hold for any
positive variance, and whatever convexity asks of the left wing is already in the strike-convexity
formula. What is not here is the last step of Roper's theorem, the construction of the random
variable from such a function.

## Main definitions

* `butterflyFreeFormula`: the strike-convexity formula with the sign atom `2 - b(1 + ρ) > 0` of
  the tail condition.

## Main results

* `asymptote_le_variance`: for `b ≥ 0`, `variance p k ≥ a + b(1 + ρ)(k - m)`.
* `tendsto_dpl_atBot_iff`: for `b ≥ 0` and positive variance, `d₊(k) → -∞` as `k → ∞` iff
  `b(1 + ρ) < 2`.
* `blackCall_le_Phi_dpl`, `bsSmile_nonneg`, `one_sub_le_bsSmile`, `bsSmile_le_one`: for `K > 0` and
  positive variance at `log K`, the smiled call is at most `Φ(d₊)`, nonnegative, at least
  `1 - K` and at most `1`.
* `tendsto_bsSmile_zero_iff`: for `b ≥ 0` and positive variance, `bsSmile p` tends to `0` at
  `∞` iff `b(1 + ρ) < 2`.
* `isNormalizedCallPrice_bsSmile_iff`: for `b ≥ 0` and positive variance, `bsSmile p` is a
  normalised call price function iff it is convex on `(0, ∞)` and `b(1 + ρ) < 2`.
* `butterflyFreeFormula_iff_isNormalizedCallPrice`: `butterflyFreeFormula` holds iff `σ ≥ 0`,
  `b ≥ 0`, `1 - ρ² ≥ 0`, the variance is positive, and `bsSmile p` is a normalised call price
  function.

## References

* [Gatheral and Jacquier, *Arbitrage-free SVI volatility surfaces*][GatheralJacquier2014], Lemma 2.2
* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1

## Tags

SVI tail condition, butterfly arbitrage, Gatheral–Jacquier, Roper theorem, large-strike behaviour,
arbitrage-free SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

open Filter Topology Set ProbabilityTheory MeasureTheory
open scoped NNReal
open ForwardSmile (dpl dmi blackForm)

/-! ### The right wing of the variance -/

/-- The variance lies above its right asymptote, of slope `b(1 + ρ)`. -/
theorem asymptote_le_variance (p : Params) (hb : 0 ≤ p.b) (k : ℝ) :
    p.a + p.b * (1 + p.rho) * (k - p.m) ≤ variance p k := by
  have hu : k - p.m ≤ Real.sqrt ((k - p.m) ^ 2 + p.sigma ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  unfold variance
  linarith [mul_le_mul_of_nonneg_left hu hb]

/-- Right of `m`, the variance is within `b|σ|` of its asymptote. -/
theorem variance_le_asymptote_add (p : Params) (hb : 0 ≤ p.b) {k : ℝ} (hk : p.m ≤ k) :
    variance p k ≤ p.a + p.b * (1 + p.rho) * (k - p.m) + p.b * |p.sigma| := by
  have hu : Real.sqrt ((k - p.m) ^ 2 + p.sigma ^ 2) ≤ (k - p.m) + |p.sigma| :=
    Real.sqrt_le_iff.2 ⟨by linarith [sub_nonneg.2 hk, abs_nonneg p.sigma],
      by nlinarith [mul_nonneg (sub_nonneg.2 hk) (abs_nonneg p.sigma), sq_abs p.sigma]⟩
  unfold variance
  linarith [mul_le_mul_of_nonneg_left hu hb]

/-- `d₊ = (w − 2k)/(2√w)` where the variance is positive. -/
theorem dpl_eq_div (p : Params) (k : ℝ) (hw : 0 < variance p k) :
    dpl k (variance p k) = (variance p k - 2 * k) / (2 * rootVariance p k) := by
  have hr := rootVariance_pos p k hw
  rw [dpl_eq_rootVariance, ← rootVariance_sq p k hw.le]
  field_simp
  ring

/-! ### The tail condition -/

/-- **A wing slope below `2` sends `d₊` to `−∞`.** With `r = √w`, `d₊ ≤ −M` is
`w + 2Mr ≤ 2k`. Young's inequality `2Mr ≤ qw + M²/q` reduces it to a linear bound on `w`, which
the asymptote supplies once `q` is small enough for `(1 + q)·slope < 2`. -/
theorem tendsto_dpl_atBot (p : Params) (hb : 0 ≤ p.b)
    (hw : ∀ k : ℝ, 0 < variance p k) (hc : p.b * (1 + p.rho) < 2) :
    Tendsto (fun k ↦ dpl k (variance p k)) atTop atBot := by
  refine tendsto_atBot.2 fun y ↦ ?_
  set c := p.b * (1 + p.rho)
  set M := max (-y) 1
  set q := (2 - c) / 4
  have hq : 0 < q := div_pos (sub_pos.2 hc) four_pos
  filter_upwards [eventually_ge_atTop (max p.m (max 0
    (2 * ((1 + q) * (p.a - c * p.m + p.b * |p.sigma|) + M ^ 2 / q) / (2 - c))))] with k hk
  have hkm : p.m ≤ k := (le_max_left _ _).trans hk
  have hk0 : 0 ≤ k := ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hkL : 2 * ((1 + q) * (p.a - c * p.m + p.b * |p.sigma|) + M ^ 2 / q) ≤ k * (2 - c) :=
    (div_le_iff₀ (sub_pos.2 hc)).1 (((le_max_right _ _).trans (le_max_right _ _)).trans hk)
  have hr := rootVariance_pos p k (hw k)
  have hr2 := rootVariance_sq p k (hw k).le
  have hwle : (1 + q) * variance p k
      ≤ (1 + q) * c * k + (1 + q) * (p.a - c * p.m + p.b * |p.sigma|) := by
    have := mul_le_mul_of_nonneg_left (variance_le_asymptote_add p hb hkm)
      (by linarith : 0 ≤ 1 + q)
    simp only [c]
    linarith
  have hslope : (1 + q) * c * k ≤ (2 + c) / 2 * k :=
    mul_le_mul_of_nonneg_right (by simp only [q]; nlinarith [sq_nonneg (2 - c)]) hk0
  -- Young's inequality, from `(q r − M)² ≥ 0`
  have hyoung : 2 * M * rootVariance p k - q * variance p k ≤ M ^ 2 / q := by
    rw [← hr2, le_div_iff₀ hq]
    nlinarith [sq_nonneg (q * rootVariance p k - M)]
  rw [dpl_eq_div p k (hw k)]
  exact ((div_le_iff₀ (by positivity)).2
    (by linarith : _ ≤ -M * (2 * rootVariance p k))).trans (neg_le.1 (le_max_left _ _))

/-- **A wing slope of at least `2` keeps `d₊` bounded below**, and sends the variance above any
level: eventually `d₊ ≥ −|a − 2m|/2` and `√w ≥ R`. -/
theorem eventually_le_dpl (p : Params) (hb : 0 ≤ p.b)
    (hw : ∀ k : ℝ, 0 < variance p k) (hc : 2 ≤ p.b * (1 + p.rho)) (R : ℝ) :
    ∀ᶠ k in atTop,
      -(|p.a - 2 * p.m| / 2) ≤ dpl k (variance p k) ∧ R ≤ rootVariance p k := by
  filter_upwards [eventually_ge_atTop (max p.m (p.m + ((max R 1) ^ 2 - p.a) / 2))] with k hk
  have hkm : p.m ≤ k := (le_max_left _ _).trans hk
  have hk1 : p.m + ((max R 1) ^ 2 - p.a) / 2 ≤ k := (le_max_right _ _).trans hk
  have hw2 : p.a + 2 * (k - p.m) ≤ variance p k :=
    le_trans (by nlinarith [sub_nonneg.2 hkm]) (asymptote_le_variance p hb k)
  have hr := rootVariance_pos p k (hw k)
  have hr2 := rootVariance_sq p k (hw k).le
  have hRr : max R 1 ≤ rootVariance p k := Real.le_sqrt_of_sq_le (by linarith)
  have hr1 : 1 ≤ rootVariance p k := (le_max_right _ _).trans hRr
  refine ⟨?_, (le_max_left _ _).trans hRr⟩
  rw [dpl_eq_div p k (hw k), le_div_iff₀ (by positivity)]
  nlinarith [abs_nonneg (p.a - 2 * p.m), neg_abs_le (p.a - 2 * p.m),
    mul_nonneg (abs_nonneg (p.a - 2 * p.m)) (sub_nonneg.2 hr1)]

/-- **The tail condition for raw SVI**: `d₊(k) → −∞` as `k → ∞` exactly when the right wing
slope `b(1 + ρ)` is below `2`. -/
theorem tendsto_dpl_atBot_iff (p : Params) (hb : 0 ≤ p.b)
    (hw : ∀ k : ℝ, 0 < variance p k) :
    Tendsto (fun k ↦ dpl k (variance p k)) atTop atBot ↔ p.b * (1 + p.rho) < 2 := by
  refine ⟨fun h ↦ not_le.1 fun hc ↦ ?_, tendsto_dpl_atBot p hb hw⟩
  obtain ⟨k, hlow, hk⟩ := ((tendsto_atBot.1 h (-(|p.a - 2 * p.m| / 2) - 1)).and
    (eventually_le_dpl p hb hw hc 0)).exists
  linarith [hk.1]

/-! ### The call price at large and small strikes -/

/-- The SVI-smiled call is at most `Φ(d₊)`. -/
theorem blackCall_le_Phi_dpl (p : Params) (K : ℝ) :
    blackCall p K ≤ MathFin.Phi (dpl (Real.log K) (variance p (Real.log K))) := by
  simp only [blackCall, ForwardSmile.blackForm]
  linarith [mul_nonneg (Real.exp_pos (Real.log K)).le
    (MathFin.Phi_nonneg (dmi (Real.log K) (variance p (Real.log K))))]

/-- The Black–Scholes hypothesis at the smile's volatility, on the standard normal space. -/
theorem bsCallHyp_smile (p : Params) {K : ℝ} (hK : 0 < K) (hw : 0 < variance p (Real.log K)) :
    BSCallHyp (gaussianReal 0 1) 1 K 0 (rootVariance p (Real.log K)) 1 id :=
  ⟨one_pos, hK, rootVariance_pos p _ hw, one_pos, ⟨aemeasurable_id, Measure.map_id⟩⟩

/-- The SVI-smiled call is nonnegative: it is a Black–Scholes price at the smile's volatility. -/
theorem bsSmile_nonneg (p : Params) {K : ℝ} (hK : 0 < K) (hw : 0 < variance p (Real.log K)) :
    0 ≤ bsSmile p K :=
  MathFin.bsV_nonneg (bsCallHyp_smile p hK hw)

/-- The SVI-smiled call is at least the forward payoff `1 − K`. -/
theorem one_sub_le_bsSmile (p : Params) {K : ℝ} (hK : 0 < K)
    (hw : 0 < variance p (Real.log K)) : 1 - K ≤ bsSmile p K := by
  simpa [bsSmile] using MathFin.bsV_ge_forward_lower_bound (bsCallHyp_smile p hK hw)

/-- The SVI-smiled call is at most `1`. -/
theorem bsSmile_le_one (p : Params) {K : ℝ} (hK : 0 < K) (hw : 0 < variance p (Real.log K)) :
    bsSmile p K ≤ 1 :=
  (blackCall_eq_bsSmile p K hK hw).symm.trans_le
    ((blackCall_le_Phi_dpl p K).trans (MathFin.Phi_le_one _))

/-- **Under the tail condition the call vanishes at large strikes**: it lies between `0` and
`Φ(d₊)`. -/
theorem tendsto_bsSmile_zero (p : Params) (hb : 0 ≤ p.b)
    (hw : ∀ k : ℝ, 0 < variance p k) (hc : p.b * (1 + p.rho) < 2) :
    Tendsto (bsSmile p) atTop (𝓝 0) := by
  have hΦ : Tendsto (fun K ↦ MathFin.Phi (dpl (Real.log K) (variance p (Real.log K)))) atTop
      (𝓝 0) :=
    tendsto_Phi_atBot.comp ((tendsto_dpl_atBot p hb hw hc).comp Real.tendsto_log_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hΦ ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with K hK using bsSmile_nonneg p hK (hw _)
  · filter_upwards [eventually_gt_atTop 0] with K hK
    exact (blackCall_eq_bsSmile p K hK (hw _)).symm.trans_le (blackCall_le_Phi_dpl p K)

/-- **With a wing slope of at least `2` the call does not vanish at large strikes.** Eventually
`Φ(d₊) ≥ δ := Φ(−|a − 2m|/2) > 0`, while by the Mills bound
`eᵏΦ(d₋) ≤ φ(d₊)/|d₋| ≤ 1/|d₋| ≤ 2/√w`, which is at most `δ/2` once `√w ≥ 4/δ`. -/
theorem not_tendsto_bsSmile_zero (p : Params) (hb : 0 ≤ p.b)
    (hw : ∀ k : ℝ, 0 < variance p k) (hc : 2 ≤ p.b * (1 + p.rho)) :
    ¬ Tendsto (bsSmile p) atTop (𝓝 0) := by
  intro h
  set δ := MathFin.Phi (-(|p.a - 2 * p.m| / 2))
  have hδ : 0 < δ := (MathFin.Phi_mem_Ioo _).1
  obtain ⟨k, hsmall, ⟨hlow, hR⟩, hk0⟩ :=
    ((Real.tendsto_exp_atTop.eventually ((tendsto_order.1 h).2 (δ / 2) (half_pos hδ))).and
      ((eventually_le_dpl p hb hw hc (4 / δ)).and (eventually_ge_atTop 0))).exists
  have hr := rootVariance_pos p k (hw k)
  rw [← blackCall_eq_bsSmile p _ (Real.exp_pos k)
    (by rw [Real.log_exp]; exact hw k)] at hsmall
  simp only [blackCall, ForwardSmile.blackForm, Real.log_exp] at hsmall
  have hE : 0 ≤ Real.exp k * MathFin.Phi (dmi k (variance p k)) :=
    mul_nonneg (Real.exp_pos k).le (MathFin.Phi_nonneg _)
  -- the Mills bound, transported by `eᵏφ(d₋) = φ(d₊)`
  have hmills :
      -dmi k (variance p k) * (Real.exp k * MathFin.Phi (dmi k (variance p k))) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (neg_mul_Phi_le_gaussianPDFReal (dmi k (variance p k)))
      (Real.exp_pos k).le
    rw [ForwardSmile.exp_mul_pdf_dmi (hw k)] at this
    linarith [gaussianPDFReal_zero_one_le_one (dpl k (variance p k))]
  have hd : 2 / δ ≤ -dmi k (variance p k) := by
    have h1 : 0 ≤ k / rootVariance p k := div_nonneg hk0 hr.le
    have h2 : 4 / δ / 2 = 2 / δ := by ring
    simp only [dmi_eq_rootVariance, neg_div]
    linarith
  have h3 := (mul_le_mul_of_nonneg_right hd hE).trans hmills
  rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at h3
  linarith [MathFin.strictMono_Phi.monotone hlow]

/-- **The call price at large strikes**: the SVI-smiled call tends to `0` exactly when the right
wing slope `b(1 + ρ)` is below `2`. -/
theorem tendsto_bsSmile_zero_iff (p : Params) (hb : 0 ≤ p.b)
    (hw : ∀ k : ℝ, 0 < variance p k) :
    Tendsto (bsSmile p) atTop (𝓝 0) ↔ p.b * (1 + p.rho) < 2 :=
  ⟨fun h ↦ not_le.1 fun hc ↦ not_tendsto_bsSmile_zero p hb hw hc h, tendsto_bsSmile_zero p hb hw⟩

/-! ### The call price function -/

/-- For a raw SVI smile with positive variance and `b ≥ 0`, the smiled call is a normalised call
price function exactly when it is convex in the strike and the right wing slope is below `2`. -/
theorem isNormalizedCallPrice_bsSmile_iff (p : Params) (hb : 0 ≤ p.b)
    (hw : ∀ k : ℝ, 0 < variance p k) :
    IsNormalizedCallPrice (bsSmile p) ↔
      ConvexOn ℝ (Ioi 0) (bsSmile p) ∧ p.b * (1 + p.rho) < 2 :=
  ⟨fun h ↦ ⟨h.convexOn, (tendsto_bsSmile_zero_iff p hb hw).1 h.tendsto_zero⟩, fun h ↦
    .of_convexOn h.1
      (fun _ hK ↦ max_le (one_sub_le_bsSmile p hK (hw _)) (bsSmile_nonneg p hK (hw _)))
      (fun _ hK ↦ bsSmile_le_one p hK (hw _)) (tendsto_bsSmile_zero p hb hw h.2)⟩

/-! ### The sign formula -/

/-- The strike-convexity formula together with the sign atom `2 − b(1 + ρ) > 0` of the tail
condition. -/
noncomputable def butterflyFreeFormula : SignFormula :=
  .and extendedCertificateFormula
    (positiveAtom (2 - MvPolynomial.X (1 : Fin 5) * (1 + MvPolynomial.X (2 : Fin 5))))

/-- `butterflyFreeFormula` holds exactly when the strike-convexity conditions do and the right
wing slope is below `2`. -/
theorem butterflyFreeFormula_eval (p : Params) :
    butterflyFreeFormula.eval p = true ↔
      (0 ≤ p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1 - p.rho ^ 2 ∧ (∀ k : ℝ, 0 < variance p k) ∧
        ConvexOn ℝ (Ioi 0) (bsSmile p)) ∧ p.b * (1 + p.rho) < 2 := by
  have he : parameterEval p (2 - MvPolynomial.X (1 : Fin 5) * (1 + MvPolynomial.X (2 : Fin 5)))
      = 2 - p.b * (1 + p.rho) := by
    simp [parameterEval, parameterValues]
  simp only [butterflyFreeFormula, SignFormula.eval, Bool.and_eq_true, positiveAtom_eval, he,
    extendedCertificateFormula_iff_bsSmile_convex, sub_pos]

/-- **Convexity of the call and the tail condition as a finite sign formula.**
`butterflyFreeFormula` holds exactly when `σ ≥ 0`, `b ≥ 0`, `ρ² ≤ 1`, the variance is positive at
every log-strike, the SVI-smiled Black–Scholes call is convex in strike, and `d₊(k) → −∞` as
`k → ∞`. For `σ > 0` that convexity is Durrleman's condition (`bsSmile_convex_iff`), and these
are the two conditions of Gatheral–Jacquier's Lemma 2.2. -/
theorem butterflyFreeFormula_iff (p : Params) :
    butterflyFreeFormula.eval p = true ↔
      0 ≤ p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1 - p.rho ^ 2 ∧ (∀ k : ℝ, 0 < variance p k) ∧
        ConvexOn ℝ (Ioi 0) (bsSmile p) ∧
          Tendsto (fun k ↦ dpl k (variance p k)) atTop atBot := by
  rw [butterflyFreeFormula_eval]
  constructor
  · rintro ⟨⟨hs, hb, hr, hw, hcv⟩, hc⟩
    exact ⟨hs, hb, hr, hw, hcv, tendsto_dpl_atBot p hb hw hc⟩
  · rintro ⟨hs, hb, hr, hw, hcv, ht⟩
    exact ⟨⟨hs, hb, hr, hw, hcv⟩, (tendsto_dpl_atBot_iff p hb hw).1 ht⟩

/-- **Butterfly-free raw SVI as a finite sign formula.** `butterflyFreeFormula` holds exactly
when `σ ≥ 0`, `b ≥ 0`, `ρ² ≤ 1`, the variance is positive at every log-strike, and the SVI-smiled
Black–Scholes call is a normalised call price function: convex and nonincreasing in the strike,
between `(1 − K)⁺` and `1`, tending to `1` at strike `0` and to `0` at large strikes. -/
theorem butterflyFreeFormula_iff_isNormalizedCallPrice (p : Params) :
    butterflyFreeFormula.eval p = true ↔
      0 ≤ p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1 - p.rho ^ 2 ∧ (∀ k : ℝ, 0 < variance p k) ∧
        IsNormalizedCallPrice (bsSmile p) := by
  rw [butterflyFreeFormula_eval]
  constructor
  · rintro ⟨⟨hs, hb, hr, hw, hcv⟩, hc⟩
    exact ⟨hs, hb, hr, hw, (isNormalizedCallPrice_bsSmile_iff p hb hw).2 ⟨hcv, hc⟩⟩
  · rintro ⟨hs, hb, hr, hw, hC⟩
    exact ⟨⟨hs, hb, hr, hw, hC.convexOn⟩, ((isNormalizedCallPrice_bsSmile_iff p hb hw).1 hC).2⟩

end SVI
end MathFin

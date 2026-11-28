/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ExchangeOption
public import LeanPool.MathFin.Models.BlackScholes.GaussianGirsanov
public import LeanPool.MathFin.Probability.Gaussian.GaussianPairLinearLaw
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Probability.Independence.Integration

/-!
# The Margrabe ratio from a joint two-GBM model

`margrabe_price_via_call` (in `ExchangeOption.lean`) prices the exchange option
by *assuming* `BSCallHyp Q (S¹₀/S²₀) 1 0 σ T Z` — the ratio `R = S¹/S²` is
lognormal at the effective volatility `σ` with a standard-normal driver `Z` under some `Q`.
This file builds that hypothesis from a joint Gaussian model of the two assets' drivers,
and ties it to the actual ratio.

The two terminal prices are Black–Scholes terminals, `Sⁱ_T = bsTerminal Sⁱ₀ r σᵢ T Wᵢ`, with
`(W₁, W₂)` jointly Gaussian, each `N(0, 1)`, with covariance `ρ`. Then:

* the normalized log-spread driver `W := (σ₁·W₁ − σ₂·W₂)/σ_eff`,
  `σ_eff² = σ₁² + σ₂² − 2ρσ₁σ₂`, is `N(0, 1)` (`normalizedSpread_hasLaw_std`): Gaussian as
  a linear image of the pair, with variance `1` by covariance bilinearity
  (`margrabe_effective_variance`);
* pathwise, the ratio is one Black–Scholes terminal at zero rate and volatility `σ_eff`,
  driven by `W` shifted by `c = (ρσ₁σ₂ − σ₂²)√T/σ_eff` (`bsTerminal_div_bsTerminal`):
  `S¹_T/S²_T = bsTerminal (S¹₀/S²₀) 0 σ_eff T (W − c)`;
* under the Esscher tilt `Q = P.withDensity(e^{cW − c²/2})`, `W − c` is `N(0, 1)`
  (`BSCallHyp.exists_of_physical`, static Girsanov), so `BSCallHyp` holds for the ratio with
  driver `W − c` (`margrabe_bsCallHyp_of_gaussian`), and the `S²`-scaled ratio call under `Q`
  is the Margrabe price (`margrabe_price_of_gaussian`).

**Scope.** `Q` is the Esscher tilt of `P` along the normalized spread; that it is the
`S²`-numéraire measure is not proved. The price-level statement is proved directly under `P`
instead: `margrabe_exchange_price` shows `𝔼_P[e^{−rT}max(S¹_T − S²_T, 0)] = margrabePrice`, by
splitting `W₂` into its regression on `W` and an independent residual (uncorrelated linear
images of a Gaussian pair are independent, `HasGaussianLaw.indepFun_of_covariance_eq_zero`).

## Main results

* `normalizedSpread_hasLaw_std` — the normalized log-spread driver
  `(σ₁W₁ − σ₂W₂)/σ_eff` is `N(0,1)` (bivariate → univariate reduction).
* `bsTerminal_div_bsTerminal` — the ratio of two Black–Scholes terminals is a Black–Scholes
  terminal of the ratio at the spread volatility.
* `margrabe_bsCallHyp_of_gaussian` — the Esscher tilt `Q` and the driver `W − c`, with
  `BSCallHyp` for the ratio and the pathwise identity for the actual ratio.
* `margrabe_price_of_gaussian` — `S²₀·𝔼_Q[max(S¹_T/S²_T − 1, 0)] = margrabePrice`.
* `margrabe_exchange_price` — Margrabe's formula is the discounted expected exchange payoff
  under the model measure `P`.
* `integral_betterOfTwo` — the better-of-two payoff `max(S¹_T, S²_T)` is worth
  `S²₀ + margrabePrice`.

## References

* [W. Margrabe, *The value of an option to exchange one asset for another*][Margrabe1978]
* [R. M. Stulz, *Options on the minimum or the maximum of two risky assets: analysis and
  applications*][Stulz1982]

## Tags

Margrabe formula, joint geometric Brownian motions, correlated assets, exchange option,
effective volatility, ratio of prices, MSC 91G20, MSC 60G15, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Bivariate → univariate reduction.** For a jointly-gaussian pair
`(W₁, W₂)` of standard-normal drivers with correlation `ρ`, the normalized
log-spread driver `(σ₁·W₁ − σ₂·W₂)/σ_eff` is standard normal, where
`σ_eff² = σ₁² + σ₂² − 2ρσ₁σ₂ > 0`. The variance is pinned to `1` by covariance
bilinearity (`margrabe_effective_variance`); gaussianity is preserved under the
linear map. -/
theorem normalizedSpread_hasLaw_std
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff : ℝ}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ) (hσeff : 0 < σeff)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    HasLaw (fun ω ↦ (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) (gaussianReal 0 1) P := by
  set W : Ω → ℝ := fun ω ↦ (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff with hW_def
  have hWmeas : Measurable W := ((hW₁meas.const_mul σ₁).sub (hW₂meas.const_mul σ₂)).div_const _
  -- `W` is a continuous-linear image of the gaussian vector, hence gaussian.
  have hWgl : HasGaussianLaw W P := by
    let L : ℝ × ℝ →L[ℝ] ℝ :=
      (σeff⁻¹ • (σ₁ • ContinuousLinearMap.fst ℝ ℝ ℝ - σ₂ • ContinuousLinearMap.snd ℝ ℝ ℝ))
    have hcomp : W = L ∘ (fun ω ↦ (W₁ ω, W₂ ω)) := by
      funext ω
      simp only [hW_def, L, FunLike.coe_smul, FunLike.coe_sub,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
    rw [hcomp]
    exact hjoint.map_of_measurable L L.continuous.measurable
  -- Mean zero and variance one.
  have hmem₁ : MemLp W₁ 2 P := (hW₁.hasGaussianLaw).memLp_two
  have hmem₂ : MemLp W₂ 2 P := (hW₂.hasGaussianLaw).memLp_two
  have hint₁ : Integrable W₁ P := hmem₁.integrable (by norm_num)
  have hint₂ : Integrable W₂ P := hmem₂.integrable (by norm_num)
  have hmean₁ : ∫ ω, W₁ ω ∂P = 0 := by rw [hW₁.integral_eq, integral_id_gaussianReal]
  have hmean₂ : ∫ ω, W₂ ω ∂P = 0 := by rw [hW₂.integral_eq, integral_id_gaussianReal]
  have hvar₁ : Var[W₁; P] = 1 := by rw [hW₁.variance_eq, variance_id_gaussianReal]; norm_num
  have hvar₂ : Var[W₂; P] = 1 := by rw [hW₂.variance_eq, variance_id_gaussianReal]; norm_num
  have hWmean : ∫ ω, W ω ∂P = 0 := by
    simp only [hW_def]
    rw [integral_div, integral_sub (hint₁.const_mul σ₁) (hint₂.const_mul σ₂),
        integral_const_mul, integral_const_mul, hmean₁, hmean₂]
    simp
  -- Var[W] = (1/σeff²)·Var[σ₁W₁ − σ₂W₂] = (1/σeff²)·σeff² = 1.
  have hmemL₁ : MemLp (fun ω ↦ σ₁ * W₁ ω) 2 P := hmem₁.const_mul σ₁
  have hmemL₂ : MemLp (fun ω ↦ σ₂ * W₂ ω) 2 P := hmem₂.const_mul σ₂
  have hvarspread : Var[fun ω ↦ σ₁ * W₁ ω - σ₂ * W₂ ω; P] = σeff ^ 2 := by
    have hV₁ : Var[fun ω ↦ σ₁ * W₁ ω; P] = σ₁ ^ 2 * 1 := by rw [variance_const_mul, hvar₁]
    have hV₂ : Var[fun ω ↦ σ₂ * W₂ ω; P] = σ₂ ^ 2 * 1 := by rw [variance_const_mul, hvar₂]
    have hC : cov[fun ω ↦ σ₁ * W₁ ω, fun ω ↦ σ₂ * W₂ ω; P] = ρ * σ₁ * σ₂ * 1 := by
      rw [covariance_const_mul_left, covariance_const_mul_right, hcov]; ring
    have hv := margrabe_effective_variance (T := 1) hmemL₁ hmemL₂ hV₁ hV₂ hC
    rw [mul_one] at hv
    rw [hσeff_sq]
    exact hv
  have hWvar : Var[W; P] = 1 := by
    have hWeq : W = fun ω ↦ σeff⁻¹ * (σ₁ * W₁ ω - σ₂ * W₂ ω) := by
      funext ω; simp only [hW_def]; rw [div_eq_inv_mul]
    rw [hWeq, variance_const_mul, hvarspread]
    field_simp
  -- Pin the law from gaussianity + (mean, variance).
  refine ⟨hWmeas.aemeasurable, ?_⟩
  have hg : IsGaussian (P.map W) := hWgl.isGaussian_map
  have hmap_mean : (P.map W)[id] = 0 := by
    rw [integral_map hWmeas.aemeasurable aestronglyMeasurable_id]
    simpa using hWmean
  have hmap_var : Var[id; P.map W] = 1 := by
    rw [variance_map aemeasurable_id hWmeas.aemeasurable]
    simpa using hWvar
  rw [hg.eq_gaussianReal (P.map W), hmap_mean, hmap_var, Real.toNNReal_one]

/-- **The ratio of two Black–Scholes terminals is a Black–Scholes terminal.** For spots
`S¹₀, S²₀ > 0`, a common rate `r` and volatilities `σ₁, σ₂`, with `σ_eff > 0`,
`σ_eff² = σ₁² + σ₂² − 2ρσ₁σ₂` and `T ≥ 0`:

  `bsTerminal S¹₀ r σ₁ T w₁ / bsTerminal S²₀ r σ₂ T w₂
     = bsTerminal (S¹₀/S²₀) 0 σ_eff T ((σ₁w₁ − σ₂w₂)/σ_eff − c)`,  `c = (ρσ₁σ₂ − σ₂²)√T/σ_eff`.

The rate cancels, and the drift `(σ₂² − σ₁²)T/2` of the log-ratio is the zero-rate drift
`−σ_eff²T/2` plus the shift `−σ_eff√T·c`. -/
theorem bsTerminal_div_bsTerminal {S1 S2 r σ₁ σ₂ ρ σeff T : ℝ} (w₁ w₂ : ℝ)
    (hσeff : 0 < σeff) (hT : 0 ≤ T) (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    bsTerminal S1 r σ₁ T w₁ / bsTerminal S2 r σ₂ T w₂
      = bsTerminal (S1 / S2) 0 σeff T
          ((σ₁ * w₁ - σ₂ * w₂) / σeff - (ρ * σ₁ * σ₂ - σ₂ ^ 2) * Real.sqrt T / σeff) := by
  have hshift : σeff * Real.sqrt T *
      ((σ₁ * w₁ - σ₂ * w₂) / σeff - (ρ * σ₁ * σ₂ - σ₂ ^ 2) * Real.sqrt T / σeff)
      = Real.sqrt T * (σ₁ * w₁ - σ₂ * w₂) - (ρ * σ₁ * σ₂ - σ₂ ^ 2) * Real.sqrt T ^ 2 := by
    field_simp
  unfold bsTerminal
  rw [mul_div_mul_comm, ← Real.exp_sub, hshift, Real.sq_sqrt hT]
  congr 2
  linear_combination (T / 2) * hσeff_sq

/-- **The Margrabe `BSCallHyp`, with its witnesses.** From a joint Gaussian model of the two
standard-normal drivers `(W₁, W₂)` with covariance `ρ`, take the normalized spread
`W = (σ₁W₁ − σ₂W₂)/σ_eff` and the shift `c = (ρσ₁σ₂ − σ₂²)√T/σ_eff` (`hc`). Then
`Q = P.withDensity(e^{cW − c²/2})` is a probability measure, the driver `Z = W − c` satisfies
`BSCallHyp Q (S¹₀/S²₀) 1 0 σ_eff T Z`, and `Z` drives the *actual* ratio of the two
Black–Scholes terminals: `S¹_T/S²_T = bsTerminal (S¹₀/S²₀) 0 σ_eff T Z` pointwise
(`bsTerminal_div_bsTerminal`). `Q` is not shown to be the `S²`-numéraire measure. -/
theorem margrabe_bsCallHyp_of_gaussian
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff S1 S2 r T c : ℝ}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hσeff : 0 < σeff) (hT : 0 < T)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂)
    (hc : c = (ρ * σ₁ * σ₂ - σ₂ ^ 2) * Real.sqrt T / σeff) :
    ∃ (Q : Measure Ω) (hQ : IsProbabilityMeasure Q) (Z : Ω → ℝ),
      Q = P.withDensity (fun ω ↦
        ENNReal.ofReal (Real.exp (c * ((σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) - c ^ 2 / 2))) ∧
      @BSCallHyp _ _ Q hQ (S1 / S2) 1 0 σeff T Z ∧
      ∀ ω, bsTerminal S1 r σ₁ T (W₁ ω) / bsTerminal S2 r σ₂ T (W₂ ω)
        = bsTerminal (S1 / S2) 0 σeff T (Z ω) := by
  have hW : HasLaw (fun ω ↦ (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) (gaussianReal 0 1) P :=
    normalizedSpread_hasLaw_std hjoint hW₁meas hW₂meas hW₁ hW₂ hcov hσeff hσeff_sq
  have hWmeas : Measurable (fun ω ↦ (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) :=
    ((hW₁meas.const_mul σ₁).sub (hW₂meas.const_mul σ₂)).div_const _
  obtain ⟨Q, hQ, hQeq, hbs⟩ :=
    BSCallHyp.exists_of_physical c (div_pos hS1 hS2) one_pos hσeff hT hWmeas hW
  refine ⟨Q, hQ, _, hQeq, hbs, fun ω ↦ ?_⟩
  subst hc
  exact bsTerminal_div_bsTerminal (W₁ ω) (W₂ ω) hσeff hT.le hσeff_sq

/-- **The ratio call under the tilted measure is the Margrabe price.** With the Esscher tilt
`Q` and shift `c` of `margrabe_bsCallHyp_of_gaussian`, the `S²₀`-scaled call on the actual
ratio of the two Black–Scholes terminals, struck at `1`, has value
`S²₀·𝔼_Q[max(S¹_T/S²_T − 1, 0)] = margrabePrice S¹₀ S²₀ σ_eff T`
(`margrabe_price_via_call`). `Q` is not shown to be the `S²`-numéraire measure; the
expected exchange payoff under `P` is `margrabe_exchange_price`. -/
theorem margrabe_price_of_gaussian
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff S1 S2 r T c : ℝ}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hσeff : 0 < σeff) (hT : 0 < T)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂)
    (hc : c = (ρ * σ₁ * σ₂ - σ₂ ^ 2) * Real.sqrt T / σeff) :
    ∃ (Q : Measure Ω) (_ : IsProbabilityMeasure Q),
      Q = P.withDensity (fun ω ↦
        ENNReal.ofReal (Real.exp (c * ((σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) - c ^ 2 / 2))) ∧
      S2 * ∫ ω, max (bsTerminal S1 r σ₁ T (W₁ ω) / bsTerminal S2 r σ₂ T (W₂ ω) - 1) 0 ∂Q
        = margrabePrice S1 S2 σeff T := by
  obtain ⟨Q, hQ, Z, hQeq, hbs, hratio⟩ :=
    margrabe_bsCallHyp_of_gaussian (r := r) hjoint hW₁meas hW₂meas hW₁ hW₂ hcov
      hS1 hS2 hσeff hT hσeff_sq hc
  refine ⟨Q, hQ, hQeq, ?_⟩
  simp_rw [hratio]
  exact margrabe_price_via_call hS2 hbs

/-! ### Margrabe's formula as the expected exchange payoff -/

/-- **Margrabe's formula is the discounted expected exchange payoff.** For two Black–Scholes
terminals `Sⁱ_T = bsTerminal Sⁱ₀ r σᵢ T Wᵢ` driven by a jointly Gaussian pair of standard
normals with covariance `ρ`, and `σ_eff > 0` with `σ_eff² = σ₁² + σ₂² − 2ρσ₁σ₂`,

  `𝔼_P[e^{−rT}·max(S¹_T − S²_T, 0)] = margrabePrice S¹₀ S²₀ σ_eff T`.

The normalized spread `W = (σ₁W₁ − σ₂W₂)/σ_eff` and the residual `V = W₂ − κW`,
`κ = cov(W₂, W)`, are uncorrelated linear images of the Gaussian pair, hence independent
(`HasGaussianLaw.indepFun_of_covariance_eq_zero`). The discounted payoff factors as
`S²₀ · e^{σ₂√T·V − σ₂²T(1−κ²)/2} · e^{cW − c²/2}·max(S¹_T/S²_T − 1, 0)` with `c = σ₂√T·κ`;
the `V`-factor has mean `1`, and the `W`-factor is the ratio call under the Esscher tilt along
`W`, which is Margrabe's price (`margrabe_bsCallHyp_of_gaussian`, `margrabe_price_via_call`). -/
theorem margrabe_exchange_price
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff S1 S2 r T : ℝ}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hσeff : 0 < σeff) (hT : 0 < T)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    ∫ ω, Real.exp (-(r * T)) *
        max (bsTerminal S1 r σ₁ T (W₁ ω) - bsTerminal S2 r σ₂ T (W₂ ω)) 0 ∂P
      = margrabePrice S1 S2 σeff T := by
  -- coefficients: `W = aW₁ + bW₂`, `κ = aρ + b = cov(W₂, W)`, `V = pW₁ + qW₂ = W₂ − κW`,
  -- and the shift `c = σ₂√T·κ`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = σ₁ / σeff := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = -σ₂ / σeff := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = a * ρ + b := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = -(k * a) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - k * b := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (ρ * σ₁ * σ₂ - σ₂ ^ 2) * Real.sqrt T / σeff := ⟨_, rfl⟩
  have hab : a ^ 2 + 2 * a * b * ρ + b ^ 2 = 1 := by
    rw [ha, hb, show (σ₁ / σeff) ^ 2 + 2 * (σ₁ / σeff) * (-σ₂ / σeff) * ρ + (-σ₂ / σeff) ^ 2
        = (σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) / σeff ^ 2 by ring, ← hσeff_sq,
      div_self (pow_ne_zero 2 hσeff.ne')]
  have hc : c = σ₂ * Real.sqrt T * k := by
    rw [hcdef, hk, ha, hb]
    ring
  have hcov0 : p * a + (p * b + q * a) * ρ + q * b = 0 := by
    rw [hp, hq]
    linear_combination (-k) * hab - hk
  have hVvar : p ^ 2 + 2 * p * q * ρ + q ^ 2 = 1 - k ^ 2 := by
    rw [hp, hq]
    linear_combination k ^ 2 * hab + 2 * k * hk
  have hWform (w₁ w₂ : ℝ) : a * w₁ + b * w₂ = (σ₁ * w₁ - σ₂ * w₂) / σeff := by
    rw [ha, hb]
    ring
  -- laws, measurability, independence
  have hU1 : Var[W₁; P] = 1 := by
    rw [hW₁.variance_eq, variance_id_gaussianReal, NNReal.coe_one]
  have hV1 : Var[W₂; P] = 1 := by
    rw [hW₂.variance_eq, variance_id_gaussianReal, NNReal.coe_one]
  have hWlaw : HasLaw (fun ω ↦ a * W₁ ω + b * W₂ ω) (gaussianReal 0 1) P := by
    have h := hasLaw_linear_gaussianPair hjoint hW₁ hW₂ hcov a b
    rwa [hab, Real.toNNReal_one] at h
  have hWmeas : Measurable fun ω ↦ a * W₁ ω + b * W₂ ω := by fun_prop
  have hVmeas : Measurable fun ω ↦ p * W₁ ω + q * W₂ ω := by fun_prop
  have hVW : HasGaussianLaw (fun ω ↦ (p * W₁ ω + q * W₂ ω, a * W₁ ω + b * W₂ ω)) P := by
    simpa only [ContinuousLinearMap.prod_apply, add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul] using
      hjoint.map_fun ((p • ContinuousLinearMap.fst ℝ ℝ ℝ + q • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hind : IndepFun (fun ω ↦ p * W₁ ω + q * W₂ ω) (fun ω ↦ a * W₁ ω + b * W₂ ω) P := by
    refine hVW.indepFun_of_covariance_eq_zero ?_
    rw [covariance_linear_of_unit hW₁.hasGaussianLaw.memLp_two hW₂.hasGaussianLaw.memLp_two
      hU1 hV1 hcov p q a b]
    exact hcov0
  -- the Esscher tilt along `W` and the ratio call under it
  obtain ⟨Q, hQ, hQeq, hbs⟩ :=
    BSCallHyp.exists_of_physical (K := 1) (r := 0) c (div_pos hS1 hS2) one_pos hσeff hT
      hWmeas hWlaw
  have hdens : Measurable fun ω ↦ Real.exp (c * (a * W₁ ω + b * W₂ ω) - c ^ 2 / 2) := by
    fun_prop
  -- the `V`-factor has mean `1`
  have hfV : ∫ ω, Real.exp (σ₂ * Real.sqrt T * (p * W₁ ω + q * W₂ ω)
      - σ₂ ^ 2 * T * (1 - k ^ 2) / 2) ∂P = 1 := by
    have hfun : (fun ω ↦ Real.exp (σ₂ * Real.sqrt T * (p * W₁ ω + q * W₂ ω)
        - σ₂ ^ 2 * T * (1 - k ^ 2) / 2))
        = fun ω ↦ Real.exp (-(σ₂ ^ 2 * T * (1 - k ^ 2) / 2)) *
          Real.exp (σ₂ * Real.sqrt T * p * W₁ ω + σ₂ * Real.sqrt T * q * W₂ ω) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfun, integral_const_mul, integral_exp_linear_gaussianPair hjoint hW₁ hW₂ hcov,
      ← Real.exp_add]
    rw [show -(σ₂ ^ 2 * T * (1 - k ^ 2) / 2) + ((σ₂ * Real.sqrt T * p) ^ 2
        + 2 * (σ₂ * Real.sqrt T * p) * (σ₂ * Real.sqrt T * q) * ρ
        + (σ₂ * Real.sqrt T * q) ^ 2) / 2 = 0 by
      linear_combination (σ₂ ^ 2 * Real.sqrt T ^ 2 / 2) * hVvar
        + (σ₂ ^ 2 * (1 - k ^ 2) / 2) * Real.sq_sqrt hT.le]
    exact Real.exp_zero
  -- the `W`-factor is the ratio call under `Q`
  have hgW : ∫ ω, Real.exp (c * (a * W₁ ω + b * W₂ ω) - c ^ 2 / 2) *
        max (bsTerminal (S1 / S2) 0 σeff T (a * W₁ ω + b * W₂ ω - c) - 1) 0 ∂P
      = ∫ ω, max (bsTerminal (S1 / S2) 0 σeff T (a * W₁ ω + b * W₂ ω - c) - 1) 0 ∂Q := by
    rw [hQeq, integral_withDensity_eq_integral_toReal_smul hdens.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  -- the payoff factors pointwise
  have hpt (ω : Ω) : Real.exp (-(r * T)) *
      max (bsTerminal S1 r σ₁ T (W₁ ω) - bsTerminal S2 r σ₂ T (W₂ ω)) 0
      = S2 * (Real.exp (σ₂ * Real.sqrt T * (p * W₁ ω + q * W₂ ω)
          - σ₂ ^ 2 * T * (1 - k ^ 2) / 2) *
        (Real.exp (c * (a * W₁ ω + b * W₂ ω) - c ^ 2 / 2) *
          max (bsTerminal (S1 / S2) 0 σeff T (a * W₁ ω + b * W₂ ω - c) - 1) 0)) := by
    have hs2 : 0 < bsTerminal S2 r σ₂ T (W₂ ω) := mul_pos hS2 (Real.exp_pos _)
    have hratio : bsTerminal S1 r σ₁ T (W₁ ω) / bsTerminal S2 r σ₂ T (W₂ ω)
        = bsTerminal (S1 / S2) 0 σeff T (a * W₁ ω + b * W₂ ω - c) := by
      rw [bsTerminal_div_bsTerminal (W₁ ω) (W₂ ω) hσeff hT.le hσeff_sq, hWform, hcdef]
    have hexp : Real.exp (-(r * T)) * bsTerminal S2 r σ₂ T (W₂ ω)
        = S2 * (Real.exp (σ₂ * Real.sqrt T * (p * W₁ ω + q * W₂ ω)
            - σ₂ ^ 2 * T * (1 - k ^ 2) / 2) *
          Real.exp (c * (a * W₁ ω + b * W₂ ω) - c ^ 2 / 2)) := by
      unfold bsTerminal
      rw [mul_left_comm, ← Real.exp_add, ← Real.exp_add]
      congr 2
      rw [hc, hp, hq]
      linear_combination (σ₂ ^ 2 * k ^ 2 / 2) * Real.sq_sqrt hT.le
    rw [exchange_payoff_eq_ratio _ _ hs2, hratio, ← mul_assoc, hexp]
    ring
  calc ∫ ω, Real.exp (-(r * T)) *
        max (bsTerminal S1 r σ₁ T (W₁ ω) - bsTerminal S2 r σ₂ T (W₂ ω)) 0 ∂P
      = S2 * ((∫ ω, Real.exp (σ₂ * Real.sqrt T * (p * W₁ ω + q * W₂ ω)
            - σ₂ ^ 2 * T * (1 - k ^ 2) / 2) ∂P) *
          ∫ ω, Real.exp (c * (a * W₁ ω + b * W₂ ω) - c ^ 2 / 2) *
            max (bsTerminal (S1 / S2) 0 σeff T (a * W₁ ω + b * W₂ ω - c) - 1) 0 ∂P) := by
        simp_rw [hpt]
        rw [integral_const_mul]
        congr 1
        exact hind.integral_fun_comp_mul_comp
          (f := fun v ↦ Real.exp (σ₂ * Real.sqrt T * v - σ₂ ^ 2 * T * (1 - k ^ 2) / 2))
          (g := fun w ↦ Real.exp (c * w - c ^ 2 / 2) *
            max (bsTerminal (S1 / S2) 0 σeff T (w - c) - 1) 0)
          hVmeas.aemeasurable hWmeas.aemeasurable
          (Continuous.aestronglyMeasurable (by fun_prop))
          (Continuous.aestronglyMeasurable (by unfold bsTerminal; fun_prop))
    _ = margrabePrice S1 S2 σeff T := by
        rw [hfV, hgW, one_mul]
        exact margrabe_price_via_call hS2 hbs

/-- **The better-of-two option in the two-GBM model**: with the model of
`margrabe_exchange_price` and `σ₂ > 0`,
`𝔼_P[e^{−rT}·max(S¹_T, S²_T)] = S²₀ + margrabePrice S¹₀ S²₀ σ_eff T`, from
`max(x, y) = y + max(x − y, 0)`, `𝔼_P[e^{−rT}S²_T] = S²₀` (`discounted_terminal_eq_S0`) and
`margrabe_exchange_price`. -/
theorem integral_betterOfTwo
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff S1 S2 r T : ℝ}
    (hjoint : HasGaussianLaw (fun ω ↦ (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ) (hS1 : 0 < S1) (hS2 : 0 < S2) (hσ₂ : 0 < σ₂)
    (hσeff : 0 < σeff) (hT : 0 < T)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    ∫ ω, Real.exp (-(r * T)) *
        max (bsTerminal S1 r σ₁ T (W₁ ω)) (bsTerminal S2 r σ₂ T (W₂ ω)) ∂P
      = S2 + margrabePrice S1 S2 σeff T := by
  have hsplit (ω : Ω) : Real.exp (-(r * T)) *
      max (bsTerminal S1 r σ₁ T (W₁ ω)) (bsTerminal S2 r σ₂ T (W₂ ω))
      = Real.exp (-(r * T)) * bsTerminal S2 r σ₂ T (W₂ ω) + Real.exp (-(r * T)) *
        max (bsTerminal S1 r σ₁ T (W₁ ω) - bsTerminal S2 r σ₂ T (W₂ ω)) 0 := by
    rw [← mul_add]
    congr 1
    rw [← max_add_add_left, add_sub_cancel, add_zero]
  have h₁ : Integrable (fun ω ↦ bsTerminal S1 r σ₁ T (W₁ ω)) P :=
    integrable_bsTerminal hW₁ _ _ _ _
  have h₂ : Integrable (fun ω ↦ bsTerminal S2 r σ₂ T (W₂ ω)) P :=
    integrable_bsTerminal hW₂ _ _ _ _
  simp_rw [hsplit]
  rw [integral_add (h₂.const_mul _) ((h₁.sub' h₂).pos_part.const_mul _),
    discounted_terminal_eq_S0 (K := 1) ⟨hS2, one_pos, hσ₂, hT, hW₂⟩,
    margrabe_exchange_price hjoint hW₁meas hW₂meas hW₁ hW₂ hcov hS1 hS2 hσeff hT hσeff_sq]

end MathFin

/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.GarmanNormalForm
public import LeanPool.MathFin.Probability.Gaussian.GaussianPairLinearLaw

/-!
# Basket option pricing: the moment-matching approximation

**This is an approximation, not an exact closed form.** A basket of
correlated lognormals `B_T = ∑ᵢ wᵢ Sᵢ_T` is *not* itself lognormal — the sum
of lognormals has no closed-form law. The standard market practice (the same
"replace the true law by a moment-matched lognormal" move as single-asset
Asian options, cf. Turnbull-Wakeman) is to match the first two moments of the
basket to a single lognormal and price that lognormal with the ordinary
Black-Scholes closed form.

For forwards `Fᵢ = Sᵢ₀ · e^{rT}`, weights `wᵢ`, vols `σᵢ` and correlations
`ρᵢⱼ`, the basket's first two moments under a joint lognormal
model `Sᵢ_T = Fᵢ · e^{σᵢ√T·Wᵢ − σᵢ²T/2}` are

  `M₁ = ∑ᵢ wᵢ Fᵢ`,
  `M₂ = ∑ᵢ ∑ⱼ wᵢ wⱼ Fᵢ Fⱼ · e^{ρᵢⱼ σᵢ σⱼ T}`,

which this file proves (`integral_basket_eq_basketM1`, `integral_basket_sq_eq_basketM2`)
when each pair `(Wᵢ, Wⱼ)` of standard-normal drivers is jointly Gaussian with covariance
`ρᵢⱼ`. Then

matching the lognormal moments `𝔼[X] = m`, `𝔼[X²] = m² e^{σ_eff² T}` forces
the **effective variance** `σ_eff² = log(M₂ / M₁²) / T`. Feeding `(M₁,
σ_eff)` into the Garman normal form (`GarmanNormalForm.lean`) at `A = DF·M₁`
gives the moment-matched basket price — literally the ordinary BS closed
form, parameterised by the matched moments, in the same spirit as Kirk's
spread approximation, which is BS parameterised by its pseudo-asset.

## Main definitions

* `basketM1`: the matched first moment `M₁ = ∑ᵢ wᵢ Fᵢ`, the basket forward's mean.
* `basketM2`: the matched second moment `M₂ = ∑ᵢ∑ⱼ wᵢwⱼFᵢFⱼ · e^{ρᵢⱼσᵢσⱼT}`.
* `basketEffVol`: the moment-matched effective volatility, solving `M₂ = M₁² · e^{σ_eff²T}` for
  `σ_eff`.
* `basketMomentMatchPrice`: the moment-matching basket call price, an approximation: the
  Black–Scholes closed form at `A = DF · M₁`, discount factor `DF` and the matched effective
  volatility.
* `basketLognormalFactor`: the unit-mean lognormal factor `e^{σ√T·w - σ²T/2}` of one asset of the
  basket at its standard-normal driver `w`.

## Main results

* `basketEffVol_single`: **consistency check** — with a single asset
  (`n = 1`, weight `1`, self-correlation `1`; `F ≠ 0`, `T > 0`, `σ ≥ 0`), the
  matched effective vol is exactly the asset's own vol `σ`. A one-asset basket
  is lognormal, and the matching recovers its volatility.
* `basketMomentMatchPrice_single_eq_bsV`: with one asset, forward `F = S·e^{rT}` and
  `DF = e^{−rT}`, the moment-matched price is the Black–Scholes call `bsV K r σ S T`;
  `basketMomentMatchPrice_single_eq_integral` adds that, under `BSCallHyp`, this is the
  discounted expected call payoff — so the approximation is exact for one asset.
* `integral_basket_eq_basketM1`, `integral_basket_sq_eq_basketM2`: `M₁` and `M₂` are the
  first and second moments of the basket in the joint lognormal model above. That the
  matched lognormal prices an `n ≥ 2` basket well is not claimed.

## References

* [D. Brigo et al., *Approximated moment-matching dynamics for basket-options
  pricing*][BrigoMercurioRapisardaScotti2004]
* [M. Levy, *Pricing European average rate currency options*][Levy1992]

## Tags

basket option, moment matching, lognormal approximation, correlated assets, effective volatility,
sum of lognormals, MSC 91G20, MSC 91G60, JEL G13
-/

@[expose] public section

namespace MathFin

open Real Finset MeasureTheory ProbabilityTheory

/-- **The matched first moment**: `M₁ = ∑ᵢ wᵢ Fᵢ`, the basket forward's mean. -/
noncomputable def basketM1 {n : ℕ} (w F : Fin n → ℝ) : ℝ :=
  ∑ i, w i * F i

/-- **The matched second moment**: `M₂ = ∑ᵢ∑ⱼ wᵢwⱼFᵢFⱼ · e^{ρᵢⱼσᵢσⱼT}`, from the
pairwise lognormal cross-moments `𝔼[Sᵢ_T Sⱼ_T] = Fᵢ Fⱼ e^{ρᵢⱼσᵢσⱼT}`. That it is the second
moment of the basket in the joint lognormal model is `integral_basket_sq_eq_basketM2`. -/
noncomputable def basketM2 {n : ℕ} (w F σ : Fin n → ℝ) (ρ : Fin n → Fin n → ℝ) (T : ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * F i * F j * Real.exp (ρ i j * σ i * σ j * T)

/-- **The moment-matched effective volatility**: solving
`M₂ = M₁² · e^{σ_eff²T}` for `σ_eff`. Meaningful when `M₂ ≥ M₁² > 0` and `T > 0`
(`M₂ ≥ M₁²` holds for a positive semidefinite correlation matrix and `T ≥ 0`, and
`M₁ > 0` for nonnegative weights and positive forwards with some weight positive;
neither is proved here). Otherwise the value comes from Mathlib's conventions for
`Real.log`, division and `Real.sqrt` and carries no meaning; it need not be `0`
(for example `M₂/M₁² < −1` with `T > 0` gives a positive value). -/
noncomputable def basketEffVol {n : ℕ} (w F σ : Fin n → ℝ) (ρ : Fin n → Fin n → ℝ) (T : ℝ) : ℝ :=
  Real.sqrt (Real.log (basketM2 w F σ ρ T / (basketM1 w F) ^ 2) / T)

/-- **The moment-matching basket call price**: the Garman-normal BS closed
form at `A = DF · M₁`, discount factor `DF`, and the matched effective
volatility. Documented as an **approximation**: the true basket law is not
lognormal, so this is not claimed to equal the discounted expected basket
payoff — only that it is literally the BS closed form at these matched
moments. -/
noncomputable def basketMomentMatchPrice {n : ℕ} (w F σ : Fin n → ℝ) (ρ : Fin n → Fin n → ℝ)
    (K DF T : ℝ) : ℝ :=
  bsVGarman (DF * basketM1 w F) K DF (basketEffVol w F σ ρ T) T

/-- **Single-asset consistency check**: a "basket" of one asset with weight
`1` and (trivial) self-correlation `1` collapses the moment-matched
effective vol to exactly that asset's own volatility `σ`, for `F ≠ 0`, `T > 0`
and `σ ≥ 0`. A one-asset basket is lognormal, and the matching recovers its
volatility; the statement is about `basketEffVol`, not about the price. -/
theorem basketEffVol_single (F σ T : ℝ) (hF : F ≠ 0) (hT : 0 < T) (hσ : 0 ≤ σ) :
    basketEffVol (n := 1) (fun _ ↦ 1) (fun _ ↦ F) (fun _ ↦ σ) (fun _ _ ↦ 1) T = σ := by
  unfold basketEffVol basketM2 basketM1
  simp only [Fin.sum_univ_one, one_mul, mul_one]
  rw [show F * F * Real.exp (σ * σ * T) / F ^ 2 = Real.exp (σ * σ * T) by
    field_simp]
  rw [Real.log_exp, show σ * σ * T / T = σ ^ 2 by field_simp]
  exact Real.sqrt_sq hσ


/-! ### One asset: the matched price is the Black–Scholes call -/

/-- **A one-asset basket is priced exactly by `bsV`.** With weight `1`, forward
`F = S·e^{rT}`, discount factor `e^{−rT}` and self-correlation `1`, the moment-matched price
is the Black–Scholes call `bsV K r σ S T`: the matched volatility is `σ`
(`basketEffVol_single`), `DF·M₁ = S`, and `bsV` is the Garman form at `DF = e^{−rT}`
(`bsV_eq_bsVGarman_standard`). -/
theorem basketMomentMatchPrice_single_eq_bsV (S K r σ T : ℝ) (hS : 0 < S) (hK : 0 < K)
    (hT : 0 < T) (hσ : 0 ≤ σ) :
    basketMomentMatchPrice (n := 1) (fun _ ↦ 1) (fun _ ↦ S * Real.exp (r * T)) (fun _ ↦ σ)
      (fun _ _ ↦ 1) K (Real.exp (-(r * T))) T = bsV K r σ S T := by
  have hM1 : basketM1 (n := 1) (fun _ ↦ 1) (fun _ ↦ S * Real.exp (r * T))
      = S * Real.exp (r * T) := by
    simp [basketM1]
  have hA : Real.exp (-(r * T)) * (S * Real.exp (r * T)) = S := by
    rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  unfold basketMomentMatchPrice
  rw [basketEffVol_single _ σ T (mul_pos hS (Real.exp_pos _)).ne' hT hσ, hM1, hA,
    bsV_eq_bsVGarman_standard K r σ S T hS hK]

/-- **For one asset the moment-matching approximation is exact**: under the Black–Scholes
lognormal hypothesis, the one-asset moment-matched price equals the discounted expected call
payoff (`basketMomentMatchPrice_single_eq_bsV` and `integral_bsCall_payoff_eq_bsV`). -/
theorem basketMomentMatchPrice_single_eq_integral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {S K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S K r σ T Z) :
    basketMomentMatchPrice (n := 1) (fun _ ↦ 1) (fun _ ↦ S * Real.exp (r * T)) (fun _ ↦ σ)
        (fun _ _ ↦ 1) K (Real.exp (-(r * T))) T
      = ∫ ω, Real.exp (-r * T) * max (bsTerminal S r σ T (Z ω) - K) 0 ∂Q := by
  rw [basketMomentMatchPrice_single_eq_bsV S K r σ T h.S_0_pos h.K_pos h.T_pos h.σ_pos.le,
    integral_bsCall_payoff_eq_bsV h]

/-! ### `M₁` and `M₂` are the basket's moments in the joint lognormal model -/

/-- The unit-mean lognormal factor `e^{σ√T·w − σ²T/2}` of one asset of the basket: the asset's
terminal value is its forward times this factor at its standard-normal driver `w`. -/
noncomputable def basketLognormalFactor (σ T w : ℝ) : ℝ :=
  Real.exp (σ * Real.sqrt T * w - σ ^ 2 * T / 2)

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The lognormal factor of a standard-normal driver has mean `1`:
`𝔼[e^{σ√T·W − σ²T/2}] = 1`, the standard-normal moment generating function. -/
lemma integral_basketLognormalFactor {W : Ω → ℝ} (hW : HasLaw W (gaussianReal 0 1) P)
    (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, basketLognormalFactor σ T (W ω) ∂P = 1 := by
  have := hW.isProbabilityMeasure
  have hmgf : ∫ ω, Real.exp (σ * Real.sqrt T * W ω) ∂P
      = Real.exp ((σ * Real.sqrt T) ^ 2 / 2) := by
    simpa [mgf] using mgf_gaussianReal hW (σ * Real.sqrt T)
  have hfun : (fun ω ↦ basketLognormalFactor σ T (W ω))
      = fun ω ↦ Real.exp (-(σ ^ 2 * T / 2)) * Real.exp (σ * Real.sqrt T * W ω) := by
    funext ω
    simp only [basketLognormalFactor]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_const_mul, hmgf, ← Real.exp_add, mul_pow, Real.sq_sqrt hT, neg_add_cancel,
    Real.exp_zero]

/-- The lognormal factor of a Gaussian driver is integrable. -/
lemma integrable_basketLognormalFactor {W : Ω → ℝ} (hW : HasLaw W (gaussianReal 0 1) P)
    (σ T : ℝ) : Integrable (fun ω ↦ basketLognormalFactor σ T (W ω)) P := by
  have h := (gaussianReal_sub_const (gaussianReal_const_mul hW (σ * Real.sqrt T))
    (σ ^ 2 * T / 2)).integrable_fun_comp (integrable_exp_mul_gaussianReal 1)
  simp only [one_mul] at h
  exact h

/-- **Cross-moment of two correlated lognormal factors**: for a jointly Gaussian pair of
standard normals with covariance `ρ`, `𝔼[e^{σ₁√T·U − σ₁²T/2} · e^{σ₂√T·V − σ₂²T/2}] =
e^{ρσ₁σ₂T}`. -/
lemma integral_basketLognormalFactor_mul {U V : Ω → ℝ} {ρ : ℝ}
    (hUV : HasGaussianLaw (fun ω ↦ (U ω, V ω)) P)
    (hU : HasLaw U (gaussianReal 0 1) P) (hV : HasLaw V (gaussianReal 0 1) P)
    (hcov : cov[U, V; P] = ρ) (σ₁ σ₂ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, basketLognormalFactor σ₁ T (U ω) * basketLognormalFactor σ₂ T (V ω) ∂P
      = Real.exp (ρ * σ₁ * σ₂ * T) := by
  have hfun : (fun ω ↦ basketLognormalFactor σ₁ T (U ω) * basketLognormalFactor σ₂ T (V ω))
      = fun ω ↦ Real.exp (-(σ₁ ^ 2 * T / 2 + σ₂ ^ 2 * T / 2)) *
          Real.exp (σ₁ * Real.sqrt T * U ω + σ₂ * Real.sqrt T * V ω) := by
    funext ω
    simp only [basketLognormalFactor]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_const_mul,
    integral_exp_linear_gaussianPair hUV hU hV hcov (σ₁ * Real.sqrt T) (σ₂ * Real.sqrt T),
    ← Real.exp_add]
  congr 1
  linear_combination (σ₁ ^ 2 / 2 + σ₁ * σ₂ * ρ + σ₂ ^ 2 / 2) * Real.sq_sqrt hT

/-- The product of two lognormal factors of a jointly Gaussian pair is integrable. -/
lemma integrable_basketLognormalFactor_mul {U V : Ω → ℝ} {ρ : ℝ}
    (hUV : HasGaussianLaw (fun ω ↦ (U ω, V ω)) P)
    (hU : HasLaw U (gaussianReal 0 1) P) (hV : HasLaw V (gaussianReal 0 1) P)
    (hcov : cov[U, V; P] = ρ) (σ₁ σ₂ T : ℝ) :
    Integrable (fun ω ↦ basketLognormalFactor σ₁ T (U ω) * basketLognormalFactor σ₂ T (V ω))
      P := by
  have h := (gaussianReal_sub_const
      (hasLaw_linear_gaussianPair hUV hU hV hcov (σ₁ * Real.sqrt T) (σ₂ * Real.sqrt T))
      (σ₁ ^ 2 * T / 2 + σ₂ ^ 2 * T / 2)).integrable_fun_comp
    (integrable_exp_mul_gaussianReal 1)
  simp only [one_mul] at h
  refine h.congr (ae_of_all _ fun ω ↦ ?_)
  simp only [basketLognormalFactor]
  rw [← Real.exp_add]
  congr 1
  ring

variable {n : ℕ} {W : Fin n → Ω → ℝ}

/-- **`M₁` is the basket's mean.** If each driver `Wᵢ` is standard normal, the basket
`B_T = ∑ᵢ wᵢ Fᵢ e^{σᵢ√T·Wᵢ − σᵢ²T/2}` has mean `∑ᵢ wᵢ Fᵢ = basketM1 w F`. -/
theorem integral_basket_eq_basketM1 (hstd : ∀ i, HasLaw (W i) (gaussianReal 0 1) P)
    (w F σ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, ∑ i, w i * (F i * basketLognormalFactor (σ i) T (W i ω)) ∂P = basketM1 w F := by
  rw [integral_finsetSum _ fun i _ ↦
    ((integrable_basketLognormalFactor (hstd i) (σ i) T).const_mul (F i)).const_mul (w i)]
  unfold basketM1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, integral_basketLognormalFactor (hstd i) (σ i) hT,
    mul_one]

/-- **`M₂` is the basket's second moment.** If each pair of drivers `(Wᵢ, Wⱼ)` is jointly
Gaussian with standard-normal margins and covariance `ρᵢⱼ`, the basket
`B_T = ∑ᵢ wᵢ Fᵢ e^{σᵢ√T·Wᵢ − σᵢ²T/2}` has `𝔼[B_T²] = ∑ᵢ∑ⱼ wᵢwⱼFᵢFⱼ e^{ρᵢⱼσᵢσⱼT} =
basketM2 w F σ ρ T`. -/
theorem integral_basket_sq_eq_basketM2 {ρ : Fin n → Fin n → ℝ}
    (hpair : ∀ i j, HasGaussianLaw (fun ω ↦ (W i ω, W j ω)) P)
    (hstd : ∀ i, HasLaw (W i) (gaussianReal 0 1) P)
    (hcorr : ∀ i j, cov[W i, W j; P] = ρ i j)
    (w F σ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, (∑ i, w i * (F i * basketLognormalFactor (σ i) T (W i ω))) ^ 2 ∂P
      = basketM2 w F σ ρ T := by
  have hint : ∀ i j, Integrable (fun ω ↦ basketLognormalFactor (σ i) T (W i ω) *
      basketLognormalFactor (σ j) T (W j ω)) P := fun i j ↦
    integrable_basketLognormalFactor_mul (hpair i j) (hstd i) (hstd j) (hcorr i j) _ _ _
  have hexpand : ∀ ω, (∑ i, w i * (F i * basketLognormalFactor (σ i) T (W i ω))) ^ 2
      = ∑ i, ∑ j, w i * w j * F i * F j *
          (basketLognormalFactor (σ i) T (W i ω) * basketLognormalFactor (σ j) T (W j ω)) :=
    fun ω ↦ by
      rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hint i j).const_mul _]
  unfold basketM2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hint i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul, integral_basketLognormalFactor_mul (hpair i j) (hstd i) (hstd j)
    (hcorr i j) _ _ hT]

end Moments

end MathFin

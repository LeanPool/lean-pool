/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralIndicator
public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralGaussian

/-!
# Exponential moments of a Wiener integral

For a deterministic kernel `f ∈ L²((0, T])` the Wiener integral `∫₀ᵀ f dB`
(`wienerIntegralLp`) is centred Gaussian with variance `‖f‖² = ∫₀ᵀ f²`
(`wienerIntegralLp_map_eq_gaussianReal`). This file reads off its exponential moments, the form
in which Gaussian short-rate models use it.

* `integral_exp_mul_wienerIntegralLp`: `𝔼[exp(c·∫f dB)] = exp(c²‖f‖²/2)`.
* `integral_exp_neg_add_mul_wienerIntegralLp`, **the bond-price lemma**: for every constant `m`,
  `𝔼[exp(−(m + c·∫₀ᵀ f dB))] = exp(−m + c²·∫₀ᵀ f²/2)`. A short-rate model whose integrated rate
  has the Wiener representation `m + c·∫₀ᵀ f dB` has `𝔼_μ[exp(−∫r)] = exp(−m + c²∫f²/2)`, its
  zero-coupon bond price when `μ` is read as the pricing measure.
  The Vasicek (`vasicekBondPrice_eq`), Hull–White (`HullWhite.bondPrice_eq`) and two-piece GSR
  (`gsrBondPrice_eq`) bond prices are its instances.
* `integral_exp_mul_exp_neg_wienerIntegralLp`, the covariance identity
  `𝔼[e^{a + c₁∫f dB}·e^{−(b + c₂∫g dB)}]
    = 𝔼[e^{a + c₁∫f dB}]·𝔼[e^{−(b + c₂∫g dB)}]·e^{−c₁c₂⟪f, g⟫}`.
  `⟪f, g⟫` is the covariance of the two Wiener integrals (polarize the isometry). No joint law
  of the pair is needed: by linearity the product is the exponential of the single Wiener
  integral of `c₁f − c₂g`.

Linearity holds only almost surely, because the integral takes values in `L²(μ)`; it is recorded
as `wienerIntegralLp_smul_ae` and `wienerIntegralLp_smul_add_smul_ae`. The Brownian value `B_T` is
the Wiener integral of the indicator of the whole window `(0, T]`
(`eval_ae_eq_wienerIntegralLp_stepIndicator`), with `⟪𝟙_{(0,T]}, f⟫ = ∫₀ᵀ f` and
`‖𝟙_{(0,T]}‖² = T`. These identities feed the Girsanov shift of
`Probability/Brownian/Girsanov/WienerIntegralGirsanov`.

## Main definitions

* `StepIndex.whole`: the step index of the whole window `(0, T]`.

## Main results

* `integral_exp_mul_wienerIntegralLp`: `𝔼[exp(c·∫₀ᵀ f dB)] = exp(c²‖f‖²/2)` for a
  deterministic kernel `f ∈ L²((0, T])`.
* `integral_exp_neg_add_mul_wienerIntegralLp`: `𝔼[exp(−(m + c·∫₀ᵀ f dB))] = exp(−m + c²·∫₀ᵀ f²/2)`
  for constants `m` and `c`.
* `integral_exp_mul_exp_neg_wienerIntegralLp`: for two kernels `f`, `g`,
  `𝔼[e^{a + c₁∫f dB}·e^{−(b + c₂∫g dB)}]` is the product of the two expectations times
  `exp(−c₁c₂⟪f, g⟫)`.
* `wienerIntegralLp_smul_ae`, `wienerIntegralLp_smul_add_smul_ae`: the Wiener integral is
  homogeneous and linear almost surely.
* `eval_ae_eq_wienerIntegralLp_stepIndicator`: `B_T` is a.s. the Wiener integral of `𝟙_{(0, T]}`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.2.1 and §3.3
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], Thm.
  4.4.9

## Tags

Wiener integral, exponential moment, zero-coupon bond price, Gaussian short rate, Vasicek model,
Hull–White model, bond-price lemma, MSC 60H05, MSC 91G30, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

/-- The square of the norm of a linear combination in a real inner product space. -/
lemma norm_smul_add_smul_sq_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : ℝ) (x y : E) :
    ‖a • x + b • y‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 + 2 * (a * b) * ⟪x, y⟫_ℝ + b ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

namespace WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### Linearity, almost surely -/

omit [IsProbabilityMeasure μ] in
/-- The Wiener integral is homogeneous almost surely: `∫ (c f) dB = c·∫ f dB` a.e. -/
lemma wienerIntegralLp_smul_ae (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (c : ℝ)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ∀ᵐ ω ∂μ, wienerIntegralLp B hB T (c • f) ω = c * wienerIntegralLp B hB T f ω := by
  filter_upwards [Lp.coeFn_smul c (wienerIntegralLp B hB T f)] with ω h
  rw [map_smul, h, Pi.smul_apply, smul_eq_mul]

omit [IsProbabilityMeasure μ] in
/-- The Wiener integral is linear almost surely:
`∫ (a f + b g) dB = a·∫ f dB + b·∫ g dB` a.e. -/
lemma wienerIntegralLp_smul_add_smul_ae (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (a b : ℝ)
    (f g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ∀ᵐ ω ∂μ, wienerIntegralLp B hB T (a • f + b • g) ω
      = a * wienerIntegralLp B hB T f ω + b * wienerIntegralLp B hB T g ω := by
  filter_upwards [Lp.coeFn_add (a • wienerIntegralLp B hB T f) (b • wienerIntegralLp B hB T g),
    Lp.coeFn_smul a (wienerIntegralLp B hB T f), Lp.coeFn_smul b (wienerIntegralLp B hB T g)]
    with ω h h₁ h₂
  rw [map_add, map_smul, map_smul, h, Pi.add_apply, h₁, h₂, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]

/-! ### The Brownian value as a Wiener integral -/

/-- The step index of the whole window `(0, T]`. -/
abbrev StepIndex.whole (T : ℝ≥0) : StepIndex T := ⟨(0, T), zero_le, le_rfl⟩

lemma StepIndex.interval_whole (T : ℝ≥0) :
    (StepIndex.whole T).interval = Set.Ioc (0 : ℝ) (T : ℝ) := by
  simp [StepIndex.interval, StepIndex.lo, StepIndex.hi]

/-- `B_T` is the Wiener integral of the indicator of `(0, T]`, almost surely: the integral of a
step indicator is the increment (`wienerIntegralLp_stepIndicator`), and `B_0 = 0` a.s. -/
lemma eval_ae_eq_wienerIntegralLp_stepIndicator (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, B T ω = wienerIntegralLp B hB T (stepIndicatorLp T (StepIndex.whole T)) ω := by
  rw [wienerIntegralLp_stepIndicator]
  filter_upwards [(memLp_increment hB (StepIndex.whole T).1.1 (StepIndex.whole T).1.2).coeFn_toLp,
    hB.eval_zero_ae_eq_zero] with ω h h0
  rw [show (wienerIncrementLp B hB (StepIndex.whole T) : Ω → ℝ) ω = B T ω - B 0 ω from h, h0,
    sub_zero]

/-- `⟪𝟙_{(0,T]}, f⟫ = ∫₀ᵀ f` in `L²((0, T])`. -/
lemma inner_stepIndicatorLp_whole (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ⟪stepIndicatorLp T (StepIndex.whole T), f⟫_ℝ = ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), f s := by
  rw [stepIndicatorLp, L2.inner_indicatorConstLp_one,
    Measure.restrict_restrict (StepIndex.measurableSet_interval _), StepIndex.interval_whole,
    Set.inter_self]

/-- `‖𝟙_{(0,T]}‖² = T` in `L²((0, T])`. -/
lemma norm_stepIndicatorLp_whole_sq (T : ℝ≥0) :
    ‖stepIndicatorLp T (StepIndex.whole T)‖ ^ 2 = (T : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, stepIndicatorLp,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, Set.inter_self,
    measureReal_restrict_apply (StepIndex.measurableSet_interval _), StepIndex.interval_whole,
    Set.inter_self, Real.volume_real_Ioc_of_le T.coe_nonneg, sub_zero]

/-! ### Exponential moments -/

/-- **The moment-generating function of a Wiener integral**: `𝔼[exp(c·∫f dB)] = exp(c²‖f‖²/2)`,
the Gaussian MGF of `wienerIntegralLp_map_eq_gaussianReal`. -/
theorem integral_exp_mul_wienerIntegralLp (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) (c : ℝ) :
    ∫ ω, Real.exp (c * wienerIntegralLp B hB T f ω) ∂μ = Real.exp (c ^ 2 * ‖f‖ ^ 2 / 2) := by
  have h := mgf_gaussianReal
    (⟨(Lp.aestronglyMeasurable _).aemeasurable, wienerIntegralLp_map_eq_gaussianReal hB T f⟩ :
      HasLaw (fun ω ↦ wienerIntegralLp B hB T f ω) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) μ) c
  simp only [mgf] at h
  rw [h, Real.coe_toNNReal _ (sq_nonneg _)]
  congr 1
  ring

/-- **The bond-price lemma.** For a deterministic kernel `f ∈ L²((0, T])` and constants `m, c`,

  `𝔼[exp(−(m + c·∫₀ᵀ f dB))] = exp(−m + c²·∫₀ᵀ f²/2)`.

A short-rate model whose integrated rate has the Wiener representation `m + c·∫₀ᵀ f dB` has
`𝔼_μ[exp(−∫r)] = exp(−m + c²∫₀ᵀf²/2)`, its bond price when `μ` is read as the pricing measure:
the Vasicek, Hull–White and two-piece GSR bond prices are its instances. -/
theorem integral_exp_neg_add_mul_wienerIntegralLp (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (m c : ℝ) (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ∫ ω, Real.exp (-(m + c * wienerIntegralLp B hB T f ω)) ∂μ
      = Real.exp (-m + c ^ 2 * (∫ s in Set.Ioc (0 : ℝ) (T : ℝ), f s ^ 2) / 2) := by
  simp_rw [neg_add, Real.exp_add, ← neg_mul]
  rw [integral_const_mul, integral_exp_mul_wienerIntegralLp, lp_two_norm_sq, neg_sq]

/-- **The covariance identity for two Wiener integrals**: with `⟪f, g⟫ = Cov(∫f dB, ∫g dB)`,

  `𝔼[e^{a + c₁∫f dB}·e^{−(b + c₂∫g dB)}] = 𝔼[e^{a + c₁∫f dB}]·𝔼[e^{−(b + c₂∫g dB)}]·e^{−c₁c₂⟪f,g⟫}`.

The product is a.s. `e^{a − b}·e^{∫(c₁f − c₂g) dB}` (linearity), and the three exponential moments
are Gaussian; the cross term of `‖c₁f − c₂g‖²` is the covariance. -/
theorem integral_exp_mul_exp_neg_wienerIntegralLp (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (a b c₁ c₂ : ℝ) (f g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ∫ ω, Real.exp (a + c₁ * wienerIntegralLp B hB T f ω)
        * Real.exp (-(b + c₂ * wienerIntegralLp B hB T g ω)) ∂μ
      = (∫ ω, Real.exp (a + c₁ * wienerIntegralLp B hB T f ω) ∂μ)
        * (∫ ω, Real.exp (-(b + c₂ * wienerIntegralLp B hB T g ω)) ∂μ)
        * Real.exp (-(c₁ * c₂ * ⟪f, g⟫_ℝ)) := by
  have hprod : ∫ ω, Real.exp (a + c₁ * wienerIntegralLp B hB T f ω)
        * Real.exp (-(b + c₂ * wienerIntegralLp B hB T g ω)) ∂μ
      = Real.exp (a - b)
        * ∫ ω, Real.exp (1 * wienerIntegralLp B hB T (c₁ • f + (-c₂) • g) ω) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [wienerIntegralLp_smul_add_smul_ae hB T c₁ (-c₂) f g] with ω hω
    rw [hω, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hF : ∫ ω, Real.exp (a + c₁ * wienerIntegralLp B hB T f ω) ∂μ
      = Real.exp a * Real.exp (c₁ ^ 2 * ‖f‖ ^ 2 / 2) := by
    simp_rw [Real.exp_add]
    rw [integral_const_mul, integral_exp_mul_wienerIntegralLp]
  have hG : ∫ ω, Real.exp (-(b + c₂ * wienerIntegralLp B hB T g ω)) ∂μ
      = Real.exp (-b) * Real.exp ((-c₂) ^ 2 * ‖g‖ ^ 2 / 2) := by
    simp_rw [neg_add, Real.exp_add, ← neg_mul]
    rw [integral_const_mul, integral_exp_mul_wienerIntegralLp]
  rw [hprod, hF, hG, integral_exp_mul_wienerIntegralLp, norm_smul_add_smul_sq_real]
  simp only [← Real.exp_add]
  congr 1
  ring

end WienerIntegralL2

end MathFin

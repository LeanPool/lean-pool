/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralIndicator
public import LeanPool.MathFin.Models.BlackScholes.Call
public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralGaussian

/-!
# The geometric-average Asian option: `n` averaging dates, closed-form price

`Models/BlackScholes/AsianGeometric.lean` proves the *two-date* geometric-Asian log-driver
`(B_s + B_t)/2` Gaussian. This file lifts that to an arbitrary number `n` of averaging
dates `τ₁, …, τₙ` and cashes the resulting lognormality into a **closed-form price**.

The log-driver of the geometric average `(∏ᵢ S_{τᵢ})^{1/n}` of a Black–Scholes GBM
`S_u = S₀·exp((r − σ²/2)u + σ B_u)` is the **average of the Brownian values**
`D = (1/n) ∑ᵢ B_{τᵢ}`. Read as a single Wiener integral of the step kernel
`f = (1/n) ∑ᵢ 𝟙_{(0,τᵢ]}` (via `wienerIntegralLp_stepIndicator`), it is centred Gaussian
with variance the `L²`-norm of `f`, evaluated on the Ω-side through the Brownian covariance
`∫ B_u·B_v = min(u,v)`:

  `Var(D) = (1/n²) ∑ᵢ ∑ⱼ min(τᵢ, τⱼ) =: Vₙ`.

So the geometric average is lognormal, `(∏ᵢ S_{τᵢ})^{1/n} = S₀·exp((r − σ²/2)·t_bar + σ·D)`
with `t_bar = (1/n) ∑ τᵢ`, and matches a vanilla Black–Scholes terminal `bsTerminal S_hat₀ r σ_G T`
under the standardized driver `Z = D/√Vₙ ~ N(0,1)`, with effective spot
`S_hat₀ = S₀·exp((r − σ²/2)t_bar + σ²Vₙ/2 − rT)` and effective volatility `σ_G = σ·√(Vₙ/T)`
(so `σ_G√T = σ√Vₙ`). Feeding that into `bs_call_formula` gives the geometric-Asian
call price in closed form — the same "reduce to one effective BS driver" move as Margrabe.

## Main definitions

* `geomAsianTbar`: the average of the sampling dates, `t_bar = (1/n) ∑ τᵢ`.
* `geomAsianVar`: the geometric-Asian log-driver variance `Vₙ = (1/n²) ∑ᵢ∑ⱼ min(τᵢ,τⱼ)`.
* `geomAsianEffVol`: the effective volatility `σ_G = σ·√(Vₙ/T)` reducing the geometric-Asian call to
  a vanilla call.
* `geomAsianEffSpot`: the effective spot `S_hat₀ = S₀·exp((r-σ²/2)t_bar + σ²Vₙ/2 - rT)` reducing the
  geometric-Asian call to a vanilla call.

## Main results

* `geomAsianN_driver_hasLaw` — `(1/n) ∑ᵢ B_{τᵢ} ~ N(0, (1/n²) ∑ᵢ∑ⱼ min(τᵢ,τⱼ))`.

## References

* [A. G. Z. Kemna and A. C. F. Vorst, *A pricing method for options based on average asset
  values*][KemnaVorst1990]

## Tags

geometric Asian option, average price option, closed-form price, effective volatility,
Wiener integral, lognormal, MSC 91G20, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The `n`-date geometric-Asian log-driver is Gaussian.** For a pre-Brownian motion `B`
and averaging dates `τ : Fin n → ℝ≥0` all `≤ T`, the average of the Brownian values
`(1/n) ∑ᵢ B_{τᵢ}` — the Gaussian part of the log geometric average — has the centred
Gaussian law `N(0, (1/n²) ∑ᵢ∑ⱼ min(τᵢ,τⱼ))`, the variance coming from the Brownian
covariance `∫ B_u·B_v = min(u,v)`. `asianGeom_driver_hasLaw` is its `n = 2` case. -/
theorem geomAsianN_driver_hasLaw (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    {n : ℕ} (hn : 0 < n) (τ : Fin n → ℝ≥0) (hτT : ∀ i, τ i ≤ T) :
    HasLaw (fun ω ↦ (∑ i, B (τ i) ω) / n)
      (gaussianReal 0 ((∑ i, ∑ j, min (τ i : ℝ) (τ j)) / (n : ℝ) ^ 2).toNNReal) μ := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- The step indices `(0, τ i]` and the kernel `f = (1/n) ∑ᵢ 𝟙_{(0,τᵢ]}`.
  set idx : Fin n → StepIndex T := fun i ↦ ⟨(0, τ i), ⟨zero_le, hτT i⟩⟩ with hidx
  set f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
    (n : ℝ)⁻¹ • ∑ i, stepIndicatorLp T (idx i) with hf
  -- Its Wiener integral is `(1/n) ∑ᵢ wInc(0,τᵢ]`.
  have hf_eq : wienerIntegralLp B hB T f
      = (n : ℝ)⁻¹ • ∑ i, wienerIncrementLp B hB (idx i) := by
    rw [hf]; simp only [map_smul, map_sum, wienerIntegralLp_stepIndicator]
  -- The memberships and per-index increment coeFns.
  have hmem : ∀ i, MemLp (B (τ i)) 2 μ := fun i ↦
    (hB.isGaussianProcess.hasGaussianLaw_eval (τ i)).memLp_two
  have hincr : ∀ i, (wienerIncrementLp B hB (idx i) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ B (τ i) ω - B 0 ω := fun i ↦
        (memLp_increment hB (idx i).1.1 (idx i).1.2).coeFn_toLp
  -- The Wiener integral's coeFn is `(1/n) ∑ᵢ B_{τᵢ}` a.e. (zero start).
  have hD : (fun ω ↦ wienerIntegralLp B hB T f ω) =ᵐ[μ] fun ω ↦ (∑ i, B (τ i) ω) / n := by
    rw [hf_eq]
    have hsmul := Lp.coeFn_smul (n : ℝ)⁻¹ (∑ i, wienerIncrementLp B hB (idx i))
    have hsum := Lp.coeFn_finsetSum (Finset.univ) (fun i ↦ wienerIncrementLp B hB (idx i))
    filter_upwards [hsmul, hsum, hB.eval_zero_ae_eq_zero, ae_all_iff.mpr hincr]
      with ω h1 h2 hz hincrω
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, h2, Finset.sum_apply]
    rw [div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [hincrω i, hz, sub_zero]
  -- The variance `∫ f² = (∑ᵢ∑ⱼ min)/n²`, computed on the Ω-side via `∫ B_u·B_v = min`.
  have hvar : (∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (f s) ^ 2 ∂volume)
      = (∑ i, ∑ j, min (τ i : ℝ) (τ j)) / (n : ℝ) ^ 2 := by
    rw [← wienerIntegralLp_integral_sq hB T f]
    have hsq : (fun ω ↦ (wienerIntegralLp B hB T f ω) ^ 2)
        =ᵐ[μ] fun ω ↦ (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, (B (τ i) ω * B (τ j) ω) := by
      filter_upwards [hD] with ω hω
      rw [hω, div_pow, pow_two (∑ i, B (τ i) ω), Finset.sum_mul_sum]
      ring
    rw [integral_congr_ae hsq]
    have hintij : ∀ i j, Integrable (fun ω ↦ B (τ i) ω * B (τ j) ω) μ := fun i j ↦
      (hmem i).integrable_mul (hmem j)
    have hinti : ∀ i, Integrable (fun ω ↦ ∑ j, (B (τ i) ω * B (τ j) ω)) μ := fun i ↦
      integrable_finsetSum _ (fun j _ ↦ hintij i j)
    rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hinti i)]
    have hji : ∀ i, (∫ ω, ∑ j, (B (τ i) ω * B (τ j) ω) ∂μ) = ∑ j, min (τ i : ℝ) (τ j) := by
      intro i
      rw [integral_finsetSum _ (fun j _ ↦ hintij i j)]
      exact Finset.sum_congr rfl (fun j _ ↦ integral_mul_eval hB (τ i) (τ j))
    simp_rw [hji]
    ring
  -- Assemble the Gaussian law and transfer along the a.e. equality.
  have h0 := wienerIntegralLp_hasLaw_gaussian hB T f
  rw [hvar] at h0
  exact ⟨h0.aemeasurable.congr hD, (Measure.map_congr hD).symm.trans h0.map_eq⟩

/-! ### The closed-form geometric-Asian call price -/

/-- The average of the sampling dates, `t_bar = (1/n) ∑ τᵢ`. -/
noncomputable def geomAsianTbar {n : ℕ} (τ : Fin n → ℝ≥0) : ℝ := (∑ i, (τ i : ℝ)) / n

/-- The geometric-Asian log-driver variance `Vₙ = (1/n²) ∑ᵢ∑ⱼ min(τᵢ,τⱼ)`. -/
noncomputable def geomAsianVar {n : ℕ} (τ : Fin n → ℝ≥0) : ℝ :=
  (∑ i, ∑ j, min (τ i : ℝ) (τ j)) / (n : ℝ) ^ 2

/-- Effective Black–Scholes volatility `σ_G = σ·√(Vₙ/T)` reducing the geometric-Asian
call to a vanilla call. -/
noncomputable def geomAsianEffVol (σ Tmat : ℝ) {n : ℕ} (τ : Fin n → ℝ≥0) : ℝ :=
  σ * Real.sqrt (geomAsianVar τ / Tmat)

/-- Effective Black–Scholes spot `S_hat₀ = S₀·exp((r−σ²/2)t_bar + σ²Vₙ/2 − rT)` reducing the
geometric-Asian call to a vanilla call. -/
noncomputable def geomAsianEffSpot (S₀ r σ Tmat : ℝ) {n : ℕ} (τ : Fin n → ℝ≥0) : ℝ :=
  S₀ * Real.exp ((r - σ ^ 2 / 2) * geomAsianTbar τ + σ ^ 2 * geomAsianVar τ / 2 - r * Tmat)

/-- **The geometric average of GBM prices is one lognormal factor.** For a positive spot
`S₀` and any log-increments `a : Fin n → ℝ`,
`∏ᵢ (S₀·exp(aᵢ))^{1/n} = S₀·exp((∑ᵢ aᵢ)/n)`. -/
lemma prod_mul_exp_rpow_inv_eq {n : ℕ} (hn : 0 < n) (S₀ : ℝ) (hS₀ : 0 < S₀) (a : Fin n → ℝ) :
    (∏ i, (S₀ * Real.exp (a i)) ^ ((n : ℝ)⁻¹)) = S₀ * Real.exp ((∑ i, a i) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hexp_rpow : ∀ x y : ℝ, (Real.exp x) ^ y = Real.exp (x * y) := fun x y ↦ by
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  have hfac : ∀ i, (S₀ * Real.exp (a i)) ^ ((n : ℝ)⁻¹)
      = S₀ ^ ((n : ℝ)⁻¹) * Real.exp (a i * (n : ℝ)⁻¹) := fun i ↦ by
    rw [Real.mul_rpow hS₀.le (Real.exp_pos _).le, hexp_rpow]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_natCast (S₀ ^ (n : ℝ)⁻¹) n, ← Real.rpow_mul hS₀.le, inv_mul_cancel₀ hn0,
    Real.rpow_one, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_mul, ← div_eq_mul_inv]

/-- **The effective-BS reduction.** The geometric-average lognormal `S₀·exp((r−σ²/2)t_bar + σ·d)`
is exactly the vanilla Black–Scholes terminal `bsTerminal S_hat₀ r σ_G T` at the standardized
driver `z = d/√Vₙ`, with `S_hat₀ = S₀·exp((r−σ²/2)t_bar + σ²Vₙ/2 − rT)` and `σ_G = σ√(Vₙ/T)`. -/
private lemma bsTerminal_geomAsian_eq {S₀ r σ Tmat V tbar d : ℝ}
    (hTmat : 0 < Tmat) (hV : 0 < V) :
    bsTerminal (S₀ * Real.exp ((r - σ ^ 2 / 2) * tbar + σ ^ 2 * V / 2 - r * Tmat)) r
        (σ * Real.sqrt (V / Tmat)) Tmat (d / Real.sqrt V)
      = S₀ * Real.exp ((r - σ ^ 2 / 2) * tbar + σ * d) := by
  have hsV : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hVT : (0 : ℝ) ≤ V / Tmat := by positivity
  have key1 : σ * Real.sqrt (V / Tmat) * Real.sqrt Tmat = σ * Real.sqrt V := by
    rw [mul_assoc, ← Real.sqrt_mul hVT, div_mul_cancel₀ _ hTmat.ne']
  have key2 : (σ * Real.sqrt (V / Tmat)) ^ 2 = σ ^ 2 * (V / Tmat) := by
    rw [mul_pow, Real.sq_sqrt hVT]
  have key3 : σ * Real.sqrt (V / Tmat) * Real.sqrt Tmat * (d / Real.sqrt V) = σ * d := by
    rw [key1]; field_simp
  unfold bsTerminal
  rw [mul_assoc, ← Real.exp_add, key2, key3]
  congr 2
  field_simp
  ring

/-- **The `n`-date geometric-Asian call price in closed form.** For a Black–Scholes GBM
`S_u = S₀·exp((r − σ²/2)u + σ B_u)` sampled at dates `τ : Fin n → ℝ≥0` (all `≤ T`), with a
non-degenerate log-driver variance `Vₙ > 0`, the discounted expected geometric-Asian call
payoff `e^{−rT}·𝔼[max((∏ᵢ S_{τᵢ})^{1/n} − K, 0)]` equals the Black–Scholes call price with
effective spot `S_hat₀` and volatility `σ_G` — the same "reduce to one effective BS driver"
move as Margrabe, here with the geometric-average forward carrying the `σ²Vₙ/2` convexity. -/
theorem geomAsianN_call_price (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    {n : ℕ} (hn : 0 < n) (τ : Fin n → ℝ≥0) (hτT : ∀ i, τ i ≤ T)
    (S₀ K r σ Tmat : ℝ) (hS₀ : 0 < S₀) (hK : 0 < K) (hσ : 0 < σ) (hTmat : 0 < Tmat)
    (hV : 0 < geomAsianVar τ) :
    ∫ ω, Real.exp (-r * Tmat) *
        max ((∏ i, (S₀ * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ) + σ * B (τ i) ω)) ^ ((n : ℝ)⁻¹))
          - K) 0 ∂μ
      = geomAsianEffSpot S₀ r σ Tmat τ *
          Phi (bsd1 (geomAsianEffSpot S₀ r σ Tmat τ) K r (geomAsianEffVol σ Tmat τ) Tmat)
        - K * Real.exp (-r * Tmat) *
          Phi (bsd2 (geomAsianEffSpot S₀ r σ Tmat τ) K r (geomAsianEffVol σ Tmat τ) Tmat) := by
  -- Unfold the effective-parameter defs everywhere, then name the raw variance/mean.
  simp only [geomAsianEffSpot, geomAsianEffVol, geomAsianVar, geomAsianTbar] at hV ⊢
  set V : ℝ := (∑ i, ∑ j, min (τ i : ℝ) (τ j)) / (n : ℝ) ^ 2 with hVdef
  set tb : ℝ := (∑ i, (τ i : ℝ)) / n with htb
  have hsV : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.mpr hV
  -- The driver `D = (1/n) ∑ B_{τᵢ}` has law `N(0, V)`; standardize to `Z = D/√V ~ N(0,1)`.
  have hD_law : HasLaw (fun ω ↦ (∑ i, B (τ i) ω) / n) (gaussianReal 0 V.toNNReal) μ :=
    geomAsianN_driver_hasLaw hB T hn τ hτT
  have hZ_law : HasLaw (fun ω ↦ (∑ i, B (τ i) ω) / n / Real.sqrt V) (gaussianReal 0 1) μ := by
    have h := gaussianReal_const_mul hD_law (Real.sqrt V)⁻¹
    have hfun : (fun ω ↦ (Real.sqrt V)⁻¹ * ((∑ i, B (τ i) ω) / n))
        = fun ω ↦ (∑ i, B (τ i) ω) / n / Real.sqrt V := by funext ω; ring
    rw [hfun] at h
    have hvar1 : (Real.sqrt V)⁻¹ ^ 2 * (V.toNNReal : ℝ) = 1 := by
      rw [Real.coe_toNNReal V hV.le, inv_pow, Real.sq_sqrt hV.le, inv_mul_cancel₀ hV.ne']
    convert h using 2
    · rw [mul_zero]
    · refine NNReal.coe_injective ?_
      rw [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_mk]
      exact hvar1.symm
  -- Name the effective spot/vol (now in terms of the raw `V`, `tb`), positivity, price formula.
  set S_hat : ℝ := S₀ * Real.exp ((r - σ ^ 2 / 2) * tb + σ ^ 2 * V / 2 - r * Tmat) with hS_hat
  set σG : ℝ := σ * Real.sqrt (V / Tmat) with hσG
  have hS_hatpos : 0 < S_hat := by rw [hS_hat]; positivity
  have hσGpos : 0 < σG := by rw [hσG]; positivity
  have hbs := bs_call_formula (Q := μ) (S_0 := S_hat) (K := K) (r := r) (σ := σG) (T := Tmat)
    (Z := fun ω ↦ (∑ i, B (τ i) ω) / n / Real.sqrt V) ⟨hS_hatpos, hK, hσGpos, hTmat, hZ_law⟩
  -- Rewrite the vanilla terminal into the geometric average, pointwise.
  have hterm : ∀ ω, bsTerminal S_hat r σG Tmat ((∑ i, B (τ i) ω) / n / Real.sqrt V)
      = ∏ i, (S₀ * Real.exp ((r - σ ^ 2 / 2) * (τ i : ℝ) + σ * B (τ i) ω)) ^ ((n : ℝ)⁻¹) := by
    intro ω
    rw [prod_mul_exp_rpow_inv_eq hn S₀ hS₀, hS_hat, hσG, bsTerminal_geomAsian_eq hTmat hV]
    congr 2
    rw [htb, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  simp_rw [hterm] at hbs
  exact hbs

end MathFin

/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.GaussianMoments
public import LeanPool.MathFin.Probability.Gaussian.GaussianPartialMoments
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.Probability.Independence.Integration

/-!
# Estimation: Gaussian variance-ratio divergence and realised-volatility bias

**Detection.** Between two centred Gaussian regimes with variance ratio
`r = σ²_high/σ²_low`, the per-observation discrimination information is the Kullback–Leibler
divergence `D = ½(r − 1 − ln r)` (`kl_gaussianReal_var_ratio`), stated as the integral of the
log-likelihood ratio `MeasureTheory.llr` against the high-variance law. The proof writes both
laws in `withDensity` form (`gaussianReal_of_var_ne_zero`) and identifies the Radon–Nikodym
derivative with the pdf ratio (`MeasureTheory.Measure.rnDeriv_withDensity_right`). `D` is the
denominator of Wald's sequential-test delay `≈ ln(1/α)/D`; near `r = 1` it is `(r − 1)²/4` up
to a cubic remainder (`abs_klVarRatio_sub_sq_le`).

**Realised volatility.** Observing `n` increments of second moment `σ²Δt` through mean-zero
noise of variance `η²` (each increment independent of its two noise draws, and adjacent noise
draws independent of each other) makes the expected realised variance
`σ²T + 2nη²`: a bias linear in the sampling frequency (`integral_sum_sq_noisy_increments`;
Zhang, Mykland and Aït-Sahalia). The square-root estimator of a nondegenerate variance target
is biased low, `E[σ̂] < σ` (`sqrtBias_oneSided`, with the one-sample Gaussian instance
`sqrtBias_absGaussianSample`). For one Gaussian sample the bias is exact:
`E|Z| = √(2v/π)` for `Z ∼ N(0, v)` (`integral_abs_gaussianReal`), read off the truncated first
moment of the standard normal in `Probability/Gaussian/GaussianPartialMoments.lean`. The endpoint
drift estimator `(X_T − X_0)/T` of `X_t = μt + σB_t` has law `N(μ, σ²/T)`, so its standard error
`σ/√T` does not depend on the sampling frequency (`drift_se_endpoint_hasLaw`,
`drift_se_endpoint_var`).

## Scope

Not proved here: the sequential-test delay `ln(1/α)/D` itself (only `D` is formalised); the
identification of the stated `∫ llr` with Mathlib's `InformationTheory.klDiv` (it needs absolute
continuity and integrability of `llr`, `InformationTheory.toReal_klDiv`); the exact constant
`√(2/n)·Γ((n+1)/2)/Γ(n/2)` of the square-root bias for `n ≥ 2` (the `n = 1` value is
`integral_abs_gaussianReal`); and noise-robust estimators such as two-scale realised variance.
The drift statements here take a single `B_T ∼ N(0, T)` and the endpoint estimator
`(μT + σB_T)/T` as given, so `n` does not appear in them; that the `n`-sample estimator of a
pre-Brownian motion with drift, on an equally spaced grid, reduces to this endpoint form is
`hasLaw_fracDiff_one_driftEstimator` in `Choice/Performance/FracDiffWeights.lean`.

## Main results

* `kl_gaussianReal_var_ratio`: the integral of the log-likelihood ratio `llr` of `N(0, r·v)` against
  `N(0, v)`, taken under `N(0, r·v)`, is `(r − 1 − ln r) / 2`, for `v ≠ 0` and `r ≠ 0`.
* `abs_klVarRatio_sub_sq_le`: for `|r − 1| ≤ 1/2`, `(r − 1 − ln r)/2` differs from
  `(r − 1)²/4` by at most `|r − 1|³`.
* `integral_sum_sq_noisy_increments`: with increments of second moment `σ²·Δt` observed through
  mean-zero noise of second moment `η²` (independence hypotheses as stated), the noisy realised
  sum of squares has expectation `σ²T + 2nη²`, where `T = n·Δt`.
* `sqrtBias_oneSided`: for a nonnegative, integrable, nondegenerate `Y` with `E[Y] = σ²` and
  `σ > 0`, `E[√Y] < σ`.
* `sqrtBias_absGaussianSample`, `integral_abs_gaussianReal`: for `Z ∼ N(0, v)` with `v ≠ 0`,
  `E|Z| < √v`; and `E|Z| = √(2v/π)`.
* `drift_se_endpoint_hasLaw`, `drift_se_endpoint_var`: for `X_t = μt + σB_t` with `B_T ∼ N(0, T)`,
  the endpoint estimator `(X_T − X_0)/T` has law `N(μ, σ²/T)` and variance `σ²/T`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][CoverThomas2006].
* [L. Zhang, P. A. Mykland and Y. Aït-Sahalia, *A tale of two time scales: determining
  integrated volatility with noisy high-frequency data*][ZhangMyklandAitSahalia2005].
* [A. Wald, *Sequential Analysis*][Wald1947].
* [N. L. Johnson, S. Kotz and N. Balakrishnan, *Continuous Univariate Distributions,
  Vol.~1*][JohnsonKotzBalakrishnan1994], ch. 13

## Tags

Kullback–Leibler divergence, realised volatility, microstructure noise, variance ratio,
estimator bias, MSC 62F10, MSC 62P05, JEL C58
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace MathFin

/-! ## The D-term: KL divergence between variance-ratio Gaussians -/

section KL

/-- Pointwise identity: the log of the pdf ratio between `N(0, r·v)` and `N(0, v)` is
the quadratic `−½·ln r + x²(r−1)/(2rv)` (completing-the-square algebra, the
one-observation form of the D-term). -/
lemma log_ratio_gaussianPDFReal_eq {r v : ℝ≥0} (hv : v ≠ 0) (hr : r ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) =
      -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
  have hvpc : 0 < v := hv.bot_lt
  have hrpc : 0 < r := hr.bot_lt
  have hposP : 0 < gaussianPDFReal 0 (r * v) x := gaussianPDFReal_pos _ _ _ (mul_ne_zero hr hv)
  have hposQ : 0 < gaussianPDFReal 0 v x := gaussianPDFReal_pos _ _ _ hv
  have h2piv : (0 : ℝ) < 2 * π * v := mul_pos two_pi_pos (NNReal.coe_pos.mpr hvpc)
  have h2pirv : (0 : ℝ) < 2 * π * ((r : ℝ) * (v : ℝ)) :=
    mul_pos two_pi_pos (mul_pos (NNReal.coe_pos.mpr hrpc) (NNReal.coe_pos.mpr hvpc))
  have hrvcoe : ((r * v : ℝ≥0) : ℝ) = (r : ℝ) * (v : ℝ) := by push_cast; ring
  have hlr : Real.log (2 * π * (v : ℝ)) - Real.log (2 * π * ((r : ℝ) * (v : ℝ))) =
      -(Real.log (r : ℝ)) := by
    rw [← Real.log_div h2piv.ne' h2pirv.ne',
      show (2 * π * (v : ℝ)) / (2 * π * ((r : ℝ) * (v : ℝ))) = ((r : ℝ))⁻¹ by field_simp,
      Real.log_inv]
  have hA : Real.log (gaussianPDFReal 0 (r * v) x)
      = -(Real.log (2 * π * ((r : ℝ) * (v : ℝ)))) / 2
        - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ))) := by
    change Real.log ((Real.sqrt (2 * π * ((r * v : ℝ≥0) : ℝ)))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * ((r * v : ℝ≥0) : ℝ)))) = _
    rw [sub_zero, hrvcoe]
    rw [Real.log_mul (by positivity :
        (0 : ℝ) < (Real.sqrt (2 * π * ((r : ℝ) * (v : ℝ))))⁻¹).ne' (Real.exp_pos _).ne',
      Real.log_inv, Real.log_exp,
      Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * π * ((r : ℝ) * (v : ℝ)))]
    ring
  have hB : Real.log (gaussianPDFReal 0 v x)
      = -(Real.log (2 * π * (v : ℝ))) / 2 - x ^ 2 / (2 * (v : ℝ)) := by
    change Real.log ((Real.sqrt (2 * π * (v : ℝ≥0) : ℝ))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ≥0) : ℝ))) = _
    rw [sub_zero]
    rw [Real.log_mul (by positivity : (0 : ℝ) < (Real.sqrt (2 * π * (v : ℝ)))⁻¹).ne'
      (Real.exp_pos _).ne', Real.log_inv, Real.log_exp,
      Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * π * (v : ℝ))]
    ring
  calc Real.log (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x)
      = Real.log (gaussianPDFReal 0 (r * v) x) - Real.log (gaussianPDFReal 0 v x) :=
        Real.log_div hposP.ne' hposQ.ne'
    _ = (Real.log (2 * π * (v : ℝ)) - Real.log (2 * π * ((r : ℝ) * (v : ℝ)))) / 2
        + (x ^ 2 / (2 * (v : ℝ)) - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ)))) := by
        rw [hA, hB]; ring
    _ = -(Real.log (r : ℝ)) / 2
        + (x ^ 2 / (2 * (v : ℝ)) - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ)))) := by rw [hlr]
    _ = -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
        have hx1 : x ^ 2 / (2 * (v : ℝ)) - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ)))
            = x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
          field_simp
        rw [hx1]

/-- **The D-term.** `KL(N(0, r·v) ‖ N(0, v))` — the integral of the log
likelihood ratio `llr` against `N(0, r·v)` (the high-variance law when `r > 1`) — is
`½(r − 1 − ln r)`, the denominator of Wald's sequential-test delay `≈ ln(1/α)/D`
observations (the delay itself is not proved here).
The proof writes both laws in `withDensity` form, computes the RN derivative as the
pdf ratio via `Measure.rnDeriv_withDensity_right` and `Measure.rnDeriv_withDensity`,
and integrates the resulting quadratic termwise with the second moment
`MathFin.integral_sq_gaussianReal`. -/
theorem kl_gaussianReal_var_ratio {r v : ℝ≥0} (hv : v ≠ 0) (hr : r ≠ 0) :
    ∫ x, llr (gaussianReal 0 (r * v)) (gaussianReal 0 v) x ∂(gaussianReal 0 (r * v)) =
      ((r : ℝ) - 1 - Real.log (r : ℝ)) / 2 := by
  have hrv : r * v ≠ 0 := mul_ne_zero hr hv
  have hP : gaussianReal 0 (r * v) = volume.withDensity (gaussianPDF 0 (r * v)) :=
    gaussianReal_of_var_ne_zero _ hrv
  have hQ : gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v) :=
    gaussianReal_of_var_ne_zero _ hv
  -- the RN derivative of P against volume is the pdf:
  have hrnvol : (volume.withDensity (gaussianPDF 0 (r * v))).rnDeriv volume
      =ᵐ[volume] gaussianPDF 0 (r * v) :=
    Measure.rnDeriv_withDensity volume (measurable_gaussianPDF _ _)
  -- hence the RN derivative of P against Q is the pdf ratio, a.e. volume:
  have hrn := Measure.rnDeriv_withDensity_right (μ := gaussianReal 0 (r * v)) (ν := volume)
    (f := gaussianPDF 0 v) (measurable_gaussianPDF _ _).aemeasurable
    (ae_of_all volume fun x ↦ by
      simp only [gaussianPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact gaussianPDFReal_pos _ _ x hv)
    (ae_of_all volume fun x ↦ ENNReal.ofReal_ne_top)
  rw [← hQ, hP] at hrn
  have hcomb : (volume.withDensity (gaussianPDF 0 (r * v))).rnDeriv (gaussianReal 0 v)
      =ᵐ[volume] fun x ↦ (gaussianPDF 0 v x)⁻¹ * gaussianPDF 0 (r * v) x := by
    filter_upwards [hrn, hrnvol] with x h1 h2
    rw [h2] at h1
    exact h1
  have hreal : ∀ x : ℝ, (gaussianPDF 0 v x)⁻¹ * gaussianPDF 0 (r * v) x
      = ENNReal.ofReal (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) := by
    intro x
    calc (gaussianPDF 0 v x)⁻¹ * gaussianPDF 0 (r * v) x
        = (ENNReal.ofReal (gaussianPDFReal 0 v x))⁻¹ *
            ENNReal.ofReal (gaussianPDFReal 0 (r * v) x) := by rw [gaussianPDF, gaussianPDF]
      _ = ENNReal.ofReal (gaussianPDFReal 0 v x)⁻¹ *
            ENNReal.ofReal (gaussianPDFReal 0 (r * v) x) := by
          rw [ENNReal.ofReal_inv_of_pos (gaussianPDFReal_pos _ _ x hv)]
      _ = ENNReal.ofReal ((gaussianPDFReal 0 v x)⁻¹ * gaussianPDFReal 0 (r * v) x) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 (gaussianPDFReal_nonneg _ _ x))]
      _ = ENNReal.ofReal (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) := by
          rw [div_eq_inv_mul]
  -- the llr integrand is the log pdf ratio, a.e. volume, hence a.e. P:
  have hllr : llr (gaussianReal 0 (r * v)) (gaussianReal 0 v)
      =ᵐ[volume] fun x ↦ Real.log (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) := by
    filter_upwards [hcomb] with x hx
    change Real.log (((gaussianReal 0 (r * v)).rnDeriv (gaussianReal 0 v) x).toReal) = _
    rw [hP, hx, hreal x,
      ENNReal.toReal_ofReal
        (div_nonneg (gaussianPDFReal_nonneg _ _ x) (gaussianPDFReal_nonneg _ _ x))]
  have hPac : gaussianReal 0 (r * v) ≪ volume := gaussianReal_absolutelyContinuous _ hrv
  have hllr' : llr (gaussianReal 0 (r * v)) (gaussianReal 0 v)
      =ᵐ[gaussianReal 0 (r * v)] fun x ↦
        -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
    filter_upwards [hPac.ae_le hllr] with x hx
    rw [hx, log_ratio_gaussianPDFReal_eq hv hr]
  rw [integral_congr_ae hllr']
  have hsplit : ∫ x : ℝ, -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))
        ∂(gaussianReal 0 (r * v))
      = -(Real.log (r : ℝ)) / 2
        + (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (r * v)))
          * (((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))) := by
    have h0 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 (r * v)) :=
      (memLp_id_gaussianReal 2).integrable_sq
    have hint1 : Integrable (fun _ : ℝ ↦ -(Real.log (r : ℝ)) / 2) (gaussianReal 0 (r * v)) :=
      integrable_const _
    have hshape : ∀ x : ℝ, -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))
        = -(Real.log (r : ℝ)) / 2 + x ^ 2 * (((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))) :=
      fun _ ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hshape),
      integral_add hint1 (h0.mul_const _),
      integral_const, integral_mul_const, probReal_univ, one_smul]
  rw [hsplit, MathFin.integral_sq_gaussianReal]
  push_cast
  field_simp
  ring

/-- **The small-shift quadratic (to leading order, halving the gap between the regimes quarters
the information).** Near `r = 1` the value `D(r) = (r − 1 − ln r)/2` of
`kl_gaussianReal_var_ratio` is `(r−1)²/4` up to a cubic remainder:
`|D(r) − (r−1)²/4| ≤ |r−1|³` whenever `|r − 1| ≤ ½`. The statement is about this real
function; it does not mention the Gaussian laws. So the discrimination information vanishes
quadratically as the two regimes coalesce, and a delay `≈ ln(1/α)/D` would grow like
`1/(r−1)²`. From the second-order log-series bound
`Real.abs_log_sub_add_sum_range_le` at `x = 1 − r`. -/
theorem abs_klVarRatio_sub_sq_le {r : ℝ} (hr : |r - 1| ≤ 1 / 2) :
    |(r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4| ≤ |r - 1| ^ 3 := by
  have h := abs_log_sub_add_sum_range_le (x := 1 - r) (by rw [abs_sub_comm]; linarith) 2
  rw [sub_sub_cancel, abs_sub_comm] at h
  have hsum : ∑ i ∈ Finset.range 2, (1 - r) ^ (i + 1) / (i + 1) = (1 - r) + (1 - r) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  have hb : |r - 1| ^ 3 / (1 - |r - 1|) ≤ 2 * |r - 1| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg (r - 1)) 3)
      (by linarith : (0 : ℝ) ≤ 1 / 2 - |r - 1|)]
  rw [show (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4
      = -((1 - r) + (1 - r) ^ 2 / 2 + Real.log r) / 2 by ring, abs_div, abs_neg, abs_two]
  linarith

end KL

/-! ## Realised variance under mean-zero noise -/

section RealizedVol

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The realised-variance noise bias is linear in sampling frequency** (Zhang, Mykland and
Aït-Sahalia 2005). Over `n` increments `ΔX_i` with second moment `E[(ΔX_i)²] = σ²·Δt` (the
`MathFin.integral_sq_gaussianReal` moment in the Gaussian instance)
observed through mean-zero noise `ε_j` of scale `η` (`E[ε_j] = 0`, `E[ε_j²] = η²`), so that
the observed price is `Y = X + ε` and the observed increment is
`ΔY_i = ΔX_i + (ε_{i+1} − ε_i)`, the noisy realised sum has expectation `σ²T + 2nη²`
where `T = n·Δt`: each increment contributes its signal second moment plus **two** noise
second moments, and all cross-terms vanish by independence + mean-zero
(`IndepFun.integral_mul_eq_mul_integral`). Only the independences the cross-terms use are
assumed — each increment against its two noise draws, and adjacent noise draws pairwise — so
iid noise independent of the signal is a special case. No probability hypothesis on `μ` is
needed; the integrability hypotheses are kept explicit. -/
theorem integral_sum_sq_noisy_increments {n : ℕ} {dt T sigma eta : ℝ} (hT : T = (n : ℝ) * dt)
    (dX : ℕ → α → ℝ) (e : ℕ → α → ℝ)
    (hdXi : ∀ i ∈ Finset.range n, Integrable (dX i) μ)
    (hei : ∀ j ∈ Finset.range (n + 1), Integrable (e j) μ)
    (hdXsq : ∀ i ∈ Finset.range n, Integrable (fun x ↦ dX i x * dX i x) μ)
    (hesq : ∀ j ∈ Finset.range (n + 1), Integrable (fun x ↦ e j x * e j x) μ)
    (h_mom : ∀ i ∈ Finset.range n, ∫ x, dX i x * dX i x ∂μ = sigma * sigma * dt)
    (h_noise_sq : ∀ j ∈ Finset.range (n + 1), ∫ x, e j x * e j x ∂μ = eta * eta)
    (h_noise_mean : ∀ j ∈ Finset.range (n + 1), ∫ x, e j x ∂μ = 0)
    (h_noise_indep : ∀ i ∈ Finset.range n, e i ⟂ᵢ[μ] e (i + 1))
    (h_cross : ∀ i ∈ Finset.range n, dX i ⟂ᵢ[μ] e i ∧ dX i ⟂ᵢ[μ] e (i + 1)) :
    ∫ x, ∑ i ∈ Finset.range n, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ
      = sigma * sigma * T + 2 * (n : ℝ) * eta * eta := by
  have hexp : ∀ (i : ℕ) (x : α), (dX i x + (e (i + 1) x - e i x)) ^ 2 =
      dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
        + 2 * (dX i x * e (i + 1) x) - 2 * (dX i x * e i x)
        - 2 * (e i x * e (i + 1) x) :=
    fun _ _ ↦ by ring
  have key : ∀ i ∈ Finset.range n,
      (∫ x : α, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ = sigma * sigma * dt + 2 * eta * eta)
        ∧ Integrable (fun x : α ↦ (dX i x + (e (i + 1) x - e i x)) ^ 2) μ := by
    intro i hi
    have h0 : i ∈ Finset.range (n + 1) := by simp at hi ⊢; omega
    have h1 : i + 1 ∈ Finset.range (n + 1) := by simp at hi ⊢; omega
    -- the six integrable pieces
    have i1 : Integrable (fun x : α ↦ dX i x * dX i x) μ := hdXsq i hi
    have i2 : Integrable (fun x : α ↦ e i x * e i x) μ := hesq i h0
    have i3 : Integrable (fun x : α ↦ e (i + 1) x * e (i + 1) x) μ := hesq (i + 1) h1
    have c1 : Integrable (fun x : α ↦ dX i x * e i x) μ :=
      (h_cross i hi).1.integrable_mul (hdXi i hi) (hei i h0)
    have c2 : Integrable (fun x : α ↦ dX i x * e (i + 1) x) μ :=
      (h_cross i hi).2.integrable_mul (hdXi i hi) (hei (i + 1) h1)
    have c3 : Integrable (fun x : α ↦ e i x * e (i + 1) x) μ :=
      (h_noise_indep i hi).integrable_mul (hei i h0) (hei (i + 1) h1)
    have c1' : Integrable (fun x : α ↦ 2 * (dX i x * e i x)) μ := c1.const_mul 2
    have c2' : Integrable (fun x : α ↦ 2 * (dX i x * e (i + 1) x)) μ := c2.const_mul 2
    have c3' : Integrable (fun x : α ↦ 2 * (e i x * e (i + 1) x)) μ := c3.const_mul 2
    have i12 : Integrable (fun x : α ↦ dX i x * dX i x + e i x * e i x) μ := i1.add i2
    have i123 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x) μ :=
      i12.add i3
    have i1234 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e (i + 1) x)) μ := i123.add c2'
    have i12345 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e (i + 1) x) - 2 * (dX i x * e i x)) μ := i1234.sub c1'
    have p6 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e (i + 1) x) - 2 * (dX i x * e i x)
          - 2 * (e i x * e (i + 1) x)) μ := i12345.sub c3'
    refine ⟨?_, p6.congr (ae_of_all μ fun x ↦ (hexp i x).symm)⟩
    rw [integral_congr_ae (ae_of_all μ fun x ↦ hexp i x)]
    -- split into the six integrals; each cross-term factors and vanishes
    have z1 : ∫ x : α, dX i x * e i x ∂μ = (∫ x, dX i x ∂μ) * (∫ x, e i x ∂μ) :=
      (h_cross i hi).1.integral_mul_eq_mul_integral (hdXi i hi).1 (hei i h0).1
    have z2 : ∫ x : α, dX i x * e (i + 1) x ∂μ
        = (∫ x, dX i x ∂μ) * (∫ x, e (i + 1) x ∂μ) :=
      (h_cross i hi).2.integral_mul_eq_mul_integral (hdXi i hi).1 (hei (i + 1) h1).1
    have z3 : ∫ x : α, e i x * e (i + 1) x ∂μ
        = (∫ x, e i x ∂μ) * (∫ x, e (i + 1) x ∂μ) :=
      (h_noise_indep i hi).integral_mul_eq_mul_integral (hei i h0).1 (hei (i + 1) h1).1
    rw [integral_sub i12345 c3', integral_sub i1234 c1', integral_add i123 c2',
      integral_add i12 i3, integral_add i1 i2,
      h_mom i hi, h_noise_sq i h0, h_noise_sq (i + 1) h1,
      integral_const_mul, z2, h_noise_mean (i + 1) h1, mul_zero,
      integral_const_mul, z1, h_noise_mean i h0, mul_zero,
      integral_const_mul, z3, h_noise_mean i h0, h_noise_mean (i + 1) h1, mul_zero, mul_zero]
    ring
  calc ∫ x, ∑ i ∈ Finset.range n, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ
      = ∑ i ∈ Finset.range n, ∫ x : α, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ :=
        integral_finsetSum (Finset.range n) fun i hi ↦ (key i hi).2
    _ = ∑ i ∈ Finset.range n, (sigma * sigma * dt + 2 * eta * eta) :=
        Finset.sum_congr rfl fun i hi ↦ (key i hi).1
    _ = sigma * sigma * T + 2 * (n : ℝ) * eta * eta := by
        rw [hT, Finset.sum_const, Finset.card_range]
        ring

end RealizedVol

/-! ## The square-root estimator is biased low -/

section SqrtBias

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- **The sign of the square-root bias: `E[σ̂] < σ`.** If `Y ≥ 0` is a nondegenerate target with
`E[Y] = σ²` (the sample reading: `Y = RV/T`, the noise-free annualised realised variance
whose square root is the volatility estimator `σ̂ = √Y`), then `E[√Y] < σ` — the
square-root estimator of a nondegenerate volatility is **biased low**. Strictness comes
from the tangent-line identity at `σ²`: `√y = (y + σ²)/(2σ) − (√y − σ)²/(2σ)`, whose
remainder is strictly positive on `{Y ≠ σ²}`, a set of positive measure by nondegeneracy.
The exact Gaussian constant `√(2/n)·Γ((n+1)/2)/Γ(n/2)` of the bias is not formalized here
for `n ≥ 2`; for `n = 1` it is `integral_abs_gaussianReal`. -/
theorem sqrtBias_oneSided {Y : α → ℝ} (hYnn : ∀ ω, 0 ≤ Y ω)
    {sigma : ℝ} (hsig : 0 < sigma) (hint : Integrable Y μ)
    (hmean : ∫ ω, Y ω ∂μ = sigma * sigma) (hnd : μ {ω | Y ω ≠ sigma * sigma} ≠ 0) :
    ∫ ω, Real.sqrt (Y ω) ∂μ < sigma := by
  have hsqrtsig : Real.sqrt (sigma * sigma) = sigma := Real.sqrt_mul_self (le_of_lt hsig)
  set c : ℝ := (2 * Real.sqrt (sigma * sigma))⁻¹ with hc
  have hcpos : 0 < c := by positivity
  -- the tangent identity: √Y = (Y + σ²)/(2σ) − (√Y − σ)²/(2σ), with c = 1/(2σ)
  have hid : ∀ ω : α, Real.sqrt (Y ω) =
      c * Y ω + c * (sigma * sigma)
        - c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 := by
    intro ω
    have e1 : (Real.sqrt (Y ω)) ^ 2 = Y ω := Real.sq_sqrt (hYnn ω)
    have e2 : (Real.sqrt (sigma * sigma)) ^ 2 = sigma * sigma := Real.sq_sqrt (by positivity)
    have hkey : (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
        = Y ω + sigma * sigma - 2 * Real.sqrt (Y ω) * Real.sqrt (sigma * sigma) := by
      rw [sub_sq, e1, e2]
      ring
    rw [hkey, hc]
    field_simp
    ring
  -- integrability of the two pieces
  have hintP : Integrable (fun ω ↦ c * Y ω + c * (sigma * sigma)) μ := by
    have h := (hint.mul_const c).add (integrable_const (c * (sigma * sigma)))
    refine h.congr (ae_of_all μ fun ω ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hkey2 : ∀ ω : α, (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
      ≤ 2 * Y ω + 2 * (sigma * sigma) := by
    intro ω
    have e1 : (Real.sqrt (Y ω)) ^ 2 = Y ω := Real.sq_sqrt (hYnn ω)
    have e2 : (Real.sqrt (sigma * sigma)) ^ 2 = sigma * sigma := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (Y ω) + Real.sqrt (sigma * sigma)), e1, e2]
  have hintD : Integrable (fun ω ↦ 2 * c * Y ω + 2 * c * (sigma * sigma)) μ := by
    have h := (hint.mul_const (2 * c)).add (integrable_const (2 * c * (sigma * sigma)))
    refine h.congr (ae_of_all μ fun ω ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hintg : Integrable (fun ω ↦ c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) μ := by
    refine Integrable.mono hintD ?_ ?_
    · have := hint.1
      fun_prop
    · filter_upwards [] with ω
      change |c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2|
          ≤ |2 * c * Y ω + 2 * c * (sigma * sigma)|
      rw [abs_of_nonneg (mul_nonneg (le_of_lt hcpos) (sq_nonneg _)),
        abs_of_nonneg (by nlinarith [hcpos, hYnn ω, sq_nonneg (sigma * sigma)])]
      calc c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
          ≤ c * (2 * Y ω + 2 * (sigma * sigma)) :=
            mul_le_mul_of_nonneg_left (hkey2 ω) (le_of_lt hcpos)
        _ = 2 * c * Y ω + 2 * c * (sigma * sigma) := by ring
  -- the constant piece integrates to σ = √(σ²)
  have hPint : ∫ ω, c * Y ω + c * (sigma * sigma) ∂μ
      = Real.sqrt (sigma * sigma) := by
    have h1 : Integrable (fun ω : α ↦ c * Y ω) μ :=
      (hint.mul_const c).congr (ae_of_all μ fun ω ↦ mul_comm _ _)
    have hconst : ∫ ω : α, c * (sigma * sigma) ∂μ = c * (sigma * sigma) := by
      have h := integral_const (c * (sigma * sigma)) (μ := μ)
      rw [h]
      simp
    rw [integral_add h1 (integrable_const _),
      show (fun ω : α ↦ c * Y ω) = fun ω ↦ Y ω * c from funext fun _ ↦ mul_comm _ _,
      integral_mul_const c (fun ω ↦ Y ω), hmean, hconst, hc]
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ sigma ^ 2)]
    ring
  -- the remainder has strictly positive integral on the nondegeneracy set
  have hintgpos : 0 < ∫ ω, c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (ae_of_all μ fun ω ↦ mul_nonneg hcpos.le (sq_nonneg _)) hintg, pos_iff_ne_zero]
    intro hzero
    refine hnd (measure_mono_null (fun ω hω ↦ ?_) hzero)
    have hsne : Real.sqrt (Y ω) ≠ Real.sqrt (sigma * sigma) := fun heq ↦ hω (by
      rw [← Real.sq_sqrt (hYnn ω), ← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ sigma * sigma), heq])
    exact (mul_pos hcpos (sq_pos_iff.mpr (sub_ne_zero.mpr hsne))).ne'
  rw [integral_congr_ae (ae_of_all μ hid), integral_sub hintP hintg, hPint]
  linarith [hintgpos, hsqrtsig]

/-- **The Gaussian sample instance: `E[|Z|] < σ` for `Z ~ N(0, σ²)`.** The single-sample
(`n = 1`) realised-volatility estimator is `σ̂ = |Z| = √(Z²)`, whose target
`Y = Z²` is nondegenerate (`P(Z² = σ²) = 0` — a nondegenerate Gaussian has no atoms,
`NullSingletonClass`) — so `sqrtBias_oneSided` applies. The exact value
`E|Z| = σ√(2/π) ≈ 0.798σ` is `integral_abs_gaussianReal`. -/
theorem sqrtBias_absGaussianSample {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, |x| ∂(gaussianReal 0 v) < Real.sqrt (v : ℝ) := by
  have hvpc : 0 < v := hv.bot_lt
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr hvpc
  have : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
  have hsqrtpos : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.2 hvpos
  have hsqrtsq : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hvpos)
  have habs : ∀ x : ℝ, |x| = Real.sqrt (x ^ 2) := fun x ↦ (Real.sqrt_sq_eq_abs x).symm
  -- nondegeneracy: P(Z² = σ²) = 0 since the set is a union of two singletons
  have hsetzero : (gaussianReal 0 v) {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}
      = 0 := by
    have hsub : {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}
        ⊆ {Real.sqrt (v : ℝ)} ∪ {-Real.sqrt (v : ℝ)} := by
      intro x hx
      have habsx : |x| = Real.sqrt (v : ℝ) := by
        rw [habs x, hx, ← sq, Real.sqrt_sq (by positivity)]
      by_cases hx0 : 0 ≤ x
      · exact Or.inl (by rw [abs_of_nonneg hx0] at habsx; exact habsx)
      · refine Or.inr ?_
        have hxneg : -x = Real.sqrt (v : ℝ) := by
          rw [← abs_of_neg (not_le.mp hx0)]
          exact habsx
        change x = -Real.sqrt (v : ℝ)
        linarith
    refine measure_mono_null hsub ?_
    rw [measure_union_null (measure_singleton _) (measure_singleton _)]
  have hnd : (gaussianReal 0 v)
      {x : ℝ | x ^ 2 ≠ Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)} ≠ 0 := by
    have hmeas : MeasurableSet {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)} := by
      change MeasurableSet ((fun x : ℝ ↦ x ^ 2) ⁻¹' {Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)})
      exact MeasurableSet.preimage (measurableSet_singleton _) (by fun_prop)
    have hcompl : {x : ℝ | x ^ 2 ≠ Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}
        = {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}ᶜ := by
      ext x
      simp [ne_eq]
    rw [hcompl, measure_compl hmeas (measure_ne_top _ _), hsetzero, measure_univ]
    simp
  have hmain := sqrtBias_oneSided (μ := gaussianReal 0 v) (Y := fun x : ℝ ↦ x ^ 2)
    (sigma := Real.sqrt (v : ℝ)) (fun _ ↦ sq_nonneg _) hsqrtpos
    (memLp_id_gaussianReal 2).integrable_sq
    (by rw [MathFin.integral_sq_gaussianReal v]; exact hsqrtsq.symm) hnd
  rw [show (fun x : ℝ ↦ |x|) = fun x : ℝ ↦ Real.sqrt (x ^ 2) from funext habs]
  exact hmain

/-- **Mean absolute value of a centred Gaussian: `E|Z| = √(2v/π)` for `Z ∼ N(0, v)`.** The
one-sample volatility estimator `|Z|` therefore underestimates `σ = √v` by the exact factor
`√(2/π) ≈ 0.798` (compare `sqrtBias_absGaussianSample`). For `v = 1`, `|x|ϕ(x)` is the even
function `y ↦ yϕ(y)` of `|x|`, so `E|Z| = 2∫₀^∞ zϕ(z) dz = 2ϕ(0)` by the truncated first
moment `integral_id_mul_gaussianPDFReal_Ioi`; a general `v` is the image of `N(0, 1)` under
`x ↦ √v·x` (`gaussianReal_map_const_mul`). -/
theorem integral_abs_gaussianReal (v : ℝ≥0) :
    ∫ x, |x| ∂(gaussianReal 0 v) = √(2 * v / π) := by
  have hφ (x : ℝ) : gaussianPDFReal 0 1 |x| = gaussianPDFReal 0 1 x := by
    simp [gaussianPDFReal, sq_abs]
  have hstd : ∫ x, |x| ∂(gaussianReal 0 1) = 2 * (√(2 * π))⁻¹ := by
    calc ∫ x, |x| ∂(gaussianReal 0 1)
        = ∫ x, |x| * gaussianPDFReal 0 1 |x| := by
          rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
          congr 1 with x
          rw [hφ, smul_eq_mul, mul_comm]
      _ = 2 * ∫ x in Set.Ioi 0, x * gaussianPDFReal 0 1 x :=
          integral_comp_abs (f := fun y ↦ y * gaussianPDFReal 0 1 y)
      _ = 2 * (√(2 * π))⁻¹ := by
          rw [integral_id_mul_gaussianPDFReal_Ioi]
          simp [gaussianPDFReal]
  have hmap : gaussianReal 0 v = (gaussianReal 0 1).map (√(v : ℝ) * ·) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    exact (Real.sq_sqrt (NNReal.coe_nonneg v)).symm
  rw [hmap, integral_map (continuous_const_mul _).aemeasurable continuous_abs.aestronglyMeasurable]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul, hstd, eq_comm,
    Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have h : √(v : ℝ) * (2 * (√(2 * π))⁻¹) * (√(v : ℝ) * (2 * (√(2 * π))⁻¹)) =
      (√(v : ℝ) * √(v : ℝ)) * 4 * (√(2 * π) * √(2 * π))⁻¹ := by ring
  rw [h, Real.mul_self_sqrt (NNReal.coe_nonneg v), Real.mul_self_sqrt (by positivity)]
  field_simp
  ring

end SqrtBias

/-! ## The drift estimator sees only the endpoints -/

section DriftSE

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The endpoint drift estimator (its law).** For `X_t = μt + σB_t` with `B_T ~ N(0, T)`,
the endpoint drift estimator `(X_T − X_0)/T = μ + (σ/T)·B_T` has law `N(μ, σ²/T)` — an
affine pushforward of the gaussianReal sample (`gaussianReal_const_mul` then
`gaussianReal_const_add`). The variance slot is `σ²/T`, so the drift standard error `σ/√T`
does not depend on the number `n` of sampling points (`n` does not appear in the statement,
which takes the endpoint form as given). -/
theorem drift_se_endpoint_hasLaw {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) {B : Ω → ℝ}
    (hB : HasLaw B (gaussianReal 0 T.toNNReal) P) :
    HasLaw (fun ω ↦ (mu * T + sigma * B ω) / T)
      (gaussianReal mu (sigma ^ 2 / T).toNNReal) P := by
  have h1 := gaussianReal_const_mul hB (sigma / T)
  have h2 := gaussianReal_const_add h1 mu
  have hcong : (fun ω ↦ (mu * T + sigma * B ω) / T)
      = (fun ω ↦ mu + sigma / T * B ω) := by
    funext ω
    field_simp
  rw [hcong]
  convert h2 using 2
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hT.le]
    field_simp

/-- **The endpoint drift estimator (its variance).** `Var[(X_T − X_0)/T] = σ²/T`: the drift
estimator's standard error is `σ/√T`, independent of the sampling frequency `n`, because the
estimator is a function of the endpoints only. Via `HasLaw.variance_eq` and
`variance_id_gaussianReal`. -/
theorem drift_se_endpoint_var {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) {B : Ω → ℝ}
    (hB : HasLaw B (gaussianReal 0 T.toNNReal) P) :
    Var[fun ω ↦ (mu * T + sigma * B ω) / T; P] = sigma ^ 2 / T := by
  rw [(drift_se_endpoint_hasLaw hT mu sigma hB).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity)]

end DriftSE

end MathFin

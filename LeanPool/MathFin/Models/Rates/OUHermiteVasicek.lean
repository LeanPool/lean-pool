/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.SDE.OUSpectral
public import LeanPool.MathFin.Models.Rates.VasicekSDEGaussian

/-!
# The OU Hermite modes decay at their eigenvalues under the Vasicek law

`Probability/Brownian/SDE/OUSpectral.lean` proves, as polynomial algebra, that the scaled Hermite
polynomials `q_n(x) = He_n(x/s)` are eigenfunctions of the OU generator
`L p = −κx·p' + (σ²/2)·p''` at the stationary scale `2κs² = σ²`, with eigenvalue `−nκ`
(`ouGen_scaledHermite`); no process appears there. The semigroup statement that the eigenvalue
predicts is `𝔼[q_n(X_T)] = e^{−nκT}·q_n(x₀)` for the OU process `X` started at `x₀`.

This file checks that statement against the library's OU process: the centred Vasicek short rate
`X_T = r_T − θ`, with `r_T` in the Wiener representation whose Gaussian law
`N(vasicekSDEMean, vasicekSDEVariance)` is derived in `vasicekShortRate_hasLaw_gaussian`
(`Models/Rates/VasicekSDEGaussian.lean`), started at `x₀ = r₀ − θ`. For the first three modes,
`n ≤ 2`, the expectation of `q_n(r_T − θ)` is `e^{−nκT}·q_n(r₀ − θ)`
(`integral_scaledHermite_vasicekShortRate`). For `n = 1` this is the decay of the mean; for
`n = 2` it uses the variance `s²(1 − e^{−2κT})`, which is where the stationary scale enters.

**Scope.** Only `n ≤ 2` is proved: the general mode needs either Gaussian integration by parts
or the Hermite generating function, neither of which is available here. That `ouGen` is the
infinitesimal generator of the Vasicek process is not proved; the decay is computed from the
explicit Gaussian law.

## Main results

* `integral_scaledHermite_vasicekShortRate` — `𝔼[q_n(r_T − θ)] = e^{−nκT}·q_n(r₀ − θ)` for
  `n ≤ 2`, `κ > 0`, `s ≠ 0`, `2κs² = σ²`.

## References

* [G. A. Pavliotis, *Stochastic Processes and Applications*][Pavliotis2014], ch. 4
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

Ornstein–Uhlenbeck, Hermite polynomials, Vasicek model, generator eigenfunctions, mean reversion,
MSC 91G30, MSC 60J60, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Polynomial OUSpectral
open scoped NNReal
open WienerIntegralL2

/-- `He₁ = X` over `ℝ`. -/
private theorem hermiteReal_one : hermiteReal 1 = X := by
  simp [hermiteReal]

/-- `𝔼[(c + Y)/s] = c/s` for `Y ~ N(0, v)`. -/
theorem integral_add_div_gaussianReal (c s : ℝ) (v : ℝ≥0) :
    ∫ x, (c + x) / s ∂(gaussianReal 0 v) = c / s := by
  have h1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  rw [integral_div, integral_add (integrable_const c) h1, integral_id_gaussianReal]
  simp

/-- `𝔼[(c + Y)²] = c² + v` for `Y ~ N(0, v)`. -/
theorem integral_add_sq_gaussianReal (c : ℝ) (v : ℝ≥0) :
    ∫ x, (c + x) ^ 2 ∂(gaussianReal 0 v) = c ^ 2 + v := by
  have h1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have h2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hlin : Integrable (fun x : ℝ ↦ c ^ 2 + 2 * c * x) (gaussianReal 0 v) :=
    (integrable_const _).add (h1.const_mul _)
  rw [show (fun x : ℝ ↦ (c + x) ^ 2) = fun x ↦ c ^ 2 + 2 * c * x + x ^ 2 from
      funext fun x ↦ by ring,
    integral_add hlin h2, integral_add (integrable_const _) (h1.const_mul _), integral_const_mul,
    integral_id_gaussianReal, integral_sq_gaussianReal]
  simp

/-- `(c + Y)²` is integrable for `Y ~ N(0, v)`. -/
theorem integrable_add_sq_gaussianReal (c : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ (c + x) ^ 2) (gaussianReal 0 v) := by
  have h1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have h2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  rw [show (fun x : ℝ ↦ (c + x) ^ 2) = fun x ↦ c ^ 2 + 2 * c * x + x ^ 2 from
    funext fun x ↦ by ring]
  exact ((integrable_const _).add (h1.const_mul _)).add h2

/-- The first three scaled Hermite modes under `c + Y`, `Y ~ N(0, v)`:
`𝔼[q₀] = 1`, `𝔼[q₁] = c/s`, `𝔼[q₂] = (c² + v)/s² − 1`. -/
private theorem integral_scaledHermite_gaussianReal (c s : ℝ) (v : ℝ≥0) :
    ∫ x, (scaledHermite s 0).eval (c + x) ∂(gaussianReal 0 v) = 1
      ∧ ∫ x, (scaledHermite s 1).eval (c + x) ∂(gaussianReal 0 v) = c / s
      ∧ ∫ x, (scaledHermite s 2).eval (c + x) ∂(gaussianReal 0 v) = (c ^ 2 + v) / s ^ 2 - 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [scaledHermite_eval, hermiteReal_zero]
  · simp only [scaledHermite_eval, hermiteReal_one, eval_X]
    exact integral_add_div_gaussianReal c s v
  · simp only [scaledHermite_eval, hermiteReal_two, eval_sub, eval_mul, eval_X, eval_one]
    rw [show (fun x : ℝ ↦ (c + x) / s * ((c + x) / s) - 1)
        = fun x ↦ (c + x) ^ 2 / s ^ 2 - 1 from funext fun x ↦ by ring,
      integral_sub ((integrable_add_sq_gaussianReal c v).div_const _) (integrable_const 1),
      integral_div, integral_add_sq_gaussianReal]
    simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The diffusion part `σ ∫₀ᵀ e^{−κ(T−u)} dB_u` of the Vasicek short rate has law
`N(0, vasicekSDEVariance σ κ T)`: `vasicekShortRate_hasLaw_gaussian` shifted by its mean. -/
private theorem vasicekNoise_hasLaw (hB : IsPreBrownianReal B μ) (σ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (T : ℝ≥0) :
    HasLaw (fun ω ↦ σ * wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω)
      (gaussianReal 0 (vasicekSDEVariance σ κ T).toNNReal) μ := by
  have h := gaussianReal_sub_const (vasicekShortRate_hasLaw_gaussian hB 0 0 σ hκ T)
    (vasicekSDEMean 0 0 κ T)
  rw [sub_self] at h
  convert h using 1
  funext ω
  ring

/-- **The OU Hermite modes decay at their eigenvalues under the Vasicek law** (`n ≤ 2`). For the
Vasicek short rate `r_T` started at `r₀`, in its Wiener representation, and the stationary scale
`s` (`2κs² = σ²`, `s ≠ 0`), the scaled Hermite mode `q_n(x) = He_n(x/s)` of the centred rate
satisfies `𝔼[q_n(r_T − θ)] = e^{−nκT}·q_n(r₀ − θ)` for `n = 0, 1, 2`: the semigroup form of the
eigenidentity `ouGen κ σ q_n = −nκ·q_n` (`ouGen_scaledHermite`). -/
theorem integral_scaledHermite_vasicekShortRate (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ)
    {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) {s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2) {n : ℕ}
    (hn : n ≤ 2) :
    ∫ ω, (scaledHermite s n).eval
        (vasicekSDEMean r₀ θ κ T + σ * wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω - θ)
        ∂μ
      = Real.exp (-(n * κ * T)) * (scaledHermite s n).eval (r₀ - θ) := by
  have hcomp := (vasicekNoise_hasLaw hB σ hκ T).integral_comp
    (f := fun x ↦ (scaledHermite s n).eval (vasicekSDEMean r₀ θ κ T - θ + x))
    (by fun_prop : Continuous fun x : ℝ ↦
      (scaledHermite s n).eval (vasicekSDEMean r₀ θ κ T - θ + x)).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  simp only [add_sub_right_comm _ _ θ]
  rw [hcomp]
  have hc : vasicekSDEMean r₀ θ κ T - θ = (r₀ - θ) * Real.exp (-(κ * T)) := by
    unfold vasicekSDEMean
    ring
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hV : ((vasicekSDEVariance σ κ T).toNNReal : ℝ) = s ^ 2 * (1 - Real.exp (-(2 * κ * T))) := by
    rw [Real.coe_toNNReal _ (vasicekSDEVariance_nonneg σ hκ T.coe_nonneg), vasicekSDEVariance, ← h]
    field_simp
  have hE : Real.exp (-(2 * κ * T)) = Real.exp (-(κ * T)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  obtain ⟨h0, h1, h2⟩ := integral_scaledHermite_gaussianReal (vasicekSDEMean r₀ θ κ T - θ) s
    (vasicekSDEVariance σ κ T).toNNReal
  interval_cases n
  · rw [h0]
    simp [scaledHermite_eval, hermiteReal_zero]
  · rw [h1, hc, scaledHermite_eval, hermiteReal_one, eval_X]
    simp only [Nat.cast_one, one_mul]
    ring
  · rw [h2, hc, hV, hE, scaledHermite_eval, hermiteReal_two]
    simp only [eval_sub, eval_mul, eval_X, eval_one]
    push_cast
    rw [hE]
    field_simp
    ring

end MathFin

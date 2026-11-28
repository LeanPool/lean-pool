/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.CRRCharFun
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Mean and variance of the CRR log-return law, and their Black–Scholes limits

`Models/Binomial/CRRCharFun.lean` defines the law of one CRR risk-neutral log-return step,
`crrStepMeasure r σ T n` (mass `pₙ = crrProb r σ T n` at `+σ√(T/n)` and `1 − pₙ` at
`−σ√(T/n)`), takes the law of the `n`-step log-return to be its `n`-fold convolution
`convPow (crrStepMeasure r σ T n) n`, and proves that this law converges weakly to the
Black–Scholes normal `N((r − σ²/2)T, σ²T)` (`crr_tendsto_gaussian_inDistribution`). Weak
convergence does not by itself carry moments along. This file proves that the first two do
converge: the mean and the variance of the `n`-step law tend to `(r − σ²/2)T` and `σ²T`, the
mean and variance of the limit law (`crrRowLaw_moments_tendsto`).

The route is general first. For a probability law `ν` on `ℝ` carried by a bounded interval,
bounded support propagates through convolution (`ae_abs_le_convPow`), so polynomials are
integrable, and the `k`-fold convolution has mean `k·E_ν[X]` and variance `k·Var_ν(X)`
(`integral_id_convPow`, `variance_convPow`, from `integral_conv`). For the CRR step these are
`(2pₙ − 1)σ√(T/n)` and `4pₙ(1 − pₙ)σ²T/n` (`integral_id_crrStepMeasure`,
`variance_id_crrStepMeasure`), so the `n`-step moments are `n(2pₙ − 1)σ√(T/n)` and
`4σ²T·pₙ(1 − pₙ)`, whose limits are `crr_drift_limit_n` and `crr_variance_limit`.

## Main results

* `integrable_of_continuous_of_ae_abs_le`, `ae_abs_le_conv`, `ae_abs_le_convPow`: bounded
  support and integrability through convolution powers.
* `integral_id_convPow`, `variance_convPow`: mean and variance of a convolution power.
* `integral_id_crrStepMeasure`, `variance_id_crrStepMeasure`: mean and variance of the CRR step.
* `crrRowLaw_moments_tendsto`: mean and variance of the `n`-step CRR log-return law converge to
  those of `N((r − σ²/2)T, σ²T)`.

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]

## Tags

log-return moments, convolution power, mean and variance, Cox–Ross–Rubinstein, weak convergence,
moment convergence, MSC 91G20, MSC 60F05, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-! ### Moments of convolution powers of a boundedly supported law -/

section ConvolutionMoments

/-- A continuous function is integrable against a finite measure carried by a bounded
interval. -/
lemma integrable_of_continuous_of_ae_abs_le {μ : Measure ℝ} [IsFiniteMeasure μ] {c : ℝ}
    (hμ : ∀ᵐ x ∂μ, |x| ≤ c) {g : ℝ → ℝ} (hg : Continuous g) : Integrable g μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -c) (b := c)).exists_bound_of_continuousOn
    hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C (hμ.mono fun x hx ↦ hC x (abs_le.mp hx))

/-- Bounded support adds under convolution: if `|x| ≤ c` `μ`-a.e. and `|y| ≤ a` `ν`-a.e., then
`|z| ≤ c + a` `(μ ∗ ν)`-a.e. -/
lemma ae_abs_le_conv {μ ν : Measure ℝ} {c a : ℝ} (hμ : ∀ᵐ x ∂μ, |x| ≤ c)
    (hν : ∀ᵐ y ∂ν, |y| ≤ a) : ∀ᵐ z ∂(μ ∗ ν), |z| ≤ c + a := by
  refine (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))).2 ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hμ,
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hν] with p h₁ h₂
  exact (abs_add_le _ _).trans (add_le_add h₁ h₂)

/-- Bounded support propagates through convolution powers: if `|y| ≤ a` `ν`-a.e., then
`|x| ≤ k·a` almost everywhere for `convPow ν k`. -/
lemma ae_abs_le_convPow {ν : Measure ℝ} {a : ℝ} (hν : ∀ᵐ y ∂ν, |y| ≤ a) :
    ∀ k : ℕ, ∀ᵐ x ∂(convPow ν k), |x| ≤ k * a
  | 0 => by simp [convPow, ae_dirac_eq]
  | k + 1 => by
    rw [convPow]
    exact (ae_abs_le_conv (ae_abs_le_convPow hν k) hν).mono fun x hx ↦ by
      rwa [Nat.cast_succ, add_one_mul]

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {a : ℝ}

/-- One convolution step against a boundedly supported law: the means add, and the second
moment picks up the cross term `2·E_μ[X]·E_ν[Y]`. -/
lemma integral_id_and_sq_conv {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : ∀ᵐ x ∂μ, |x| ≤ c) (hν : ∀ᵐ y ∂ν, |y| ≤ a) :
    ∫ z, z ∂(μ ∗ ν) = ∫ x, x ∂μ + ∫ y, y ∂ν ∧
      ∫ z, z ^ 2 ∂(μ ∗ ν)
        = ∫ x, x ^ 2 ∂μ + 2 * (∫ x, x ∂μ) * (∫ y, y ∂ν) + ∫ y, y ^ 2 ∂ν := by
  have hconv := ae_abs_le_conv hμ hν
  have hμ1 := integrable_of_continuous_of_ae_abs_le hμ continuous_id'
  have hμ2 := integrable_of_continuous_of_ae_abs_le hμ (continuous_pow 2)
  have hν1 := integrable_of_continuous_of_ae_abs_le hν continuous_id'
  have hν2 := integrable_of_continuous_of_ae_abs_le hν (continuous_pow 2)
  constructor
  · rw [integral_conv (integrable_of_continuous_of_ae_abs_le hconv continuous_id')]
    have hin (x : ℝ) : ∫ y, (x + y) ∂ν = x + ∫ y, y ∂ν := by
      rw [integral_add (integrable_const x) hν1, integral_const, probReal_univ, one_smul]
    simp_rw [hin]
    rw [integral_add hμ1 (integrable_const _), integral_const, probReal_univ, one_smul]
  · rw [integral_conv (integrable_of_continuous_of_ae_abs_le hconv (continuous_pow 2))]
    have hin (x : ℝ) :
        ∫ y, (x + y) ^ 2 ∂ν = x ^ 2 + 2 * x * ∫ y, y ∂ν + ∫ y, y ^ 2 ∂ν := by
      rw [show (fun y ↦ (x + y) ^ 2) = fun y ↦ (x ^ 2 + 2 * x * y) + y ^ 2 from
          funext fun y ↦ by ring,
        integral_add (show Integrable (fun y ↦ x ^ 2 + 2 * x * y) ν from
          (integrable_const (x ^ 2)).add (hν1.const_mul (2 * x))) hν2,
        integral_add (integrable_const (x ^ 2)) (hν1.const_mul (2 * x)), integral_const_mul,
        integral_const, probReal_univ, one_smul]
    simp_rw [hin]
    have hμ1' : Integrable (fun x ↦ 2 * x * ∫ y, y ∂ν) μ := (hμ1.const_mul 2).mul_const _
    rw [integral_add (show Integrable (fun x ↦ x ^ 2 + 2 * x * ∫ y, y ∂ν) μ from
        hμ2.add hμ1') (integrable_const _),
      integral_add hμ2 hμ1', integral_mul_const, integral_const_mul, integral_const,
      probReal_univ, one_smul]

/-- **Mean and variance of a convolution power**, in moment form: for a probability law `ν`
carried by a bounded interval, `E[X] = k·E_ν[X]` and `E[X²] − E[X]² = k·(E_ν[X²] − E_ν[X]²)`
under `convPow ν k`. -/
lemma convPow_moments (hν : ∀ᵐ y ∂ν, |y| ≤ a) :
    ∀ k : ℕ, ∫ x, x ∂(convPow ν k) = k * ∫ y, y ∂ν ∧
      ∫ x, x ^ 2 ∂(convPow ν k) - (∫ x, x ∂(convPow ν k)) ^ 2
        = k * (∫ y, y ^ 2 ∂ν - (∫ y, y ∂ν) ^ 2)
  | 0 => by simp [convPow]
  | k + 1 => by
    have := convPow_isProbabilityMeasure ν k
    obtain ⟨h1, h2⟩ := convPow_moments hν k
    obtain ⟨c1, c2⟩ := integral_id_and_sq_conv (ae_abs_le_convPow hν k) hν
    rw [h1] at h2
    rw [convPow, c1, c2, h1]
    push_cast
    exact ⟨by ring, by linear_combination h2⟩

/-- **The mean of a convolution power**: `E[X] = k·E_ν[X]` under `convPow ν k`, for a
probability law `ν` carried by a bounded interval. -/
lemma integral_id_convPow (hν : ∀ᵐ y ∂ν, |y| ≤ a) (k : ℕ) :
    ∫ x, x ∂(convPow ν k) = k * ∫ y, y ∂ν :=
  (convPow_moments hν k).1

/-- The variance of a law carried by a bounded interval, in moment form. -/
lemma variance_id_eq_of_ae_abs_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : ∀ᵐ x ∂μ, |x| ≤ c) :
    variance id μ = ∫ x, x ^ 2 ∂μ - (∫ x, x ∂μ) ^ 2 := by
  rw [variance_eq_sub (MemLp.of_bound continuous_id.aestronglyMeasurable c
    (hμ.mono fun x hx ↦ by simpa [Real.norm_eq_abs] using hx))]
  rfl

/-- **The variance of a convolution power**: `Var(convPow ν k) = k·Var(ν)`, for a probability
law `ν` carried by a bounded interval. -/
lemma variance_convPow (hν : ∀ᵐ y ∂ν, |y| ≤ a) (k : ℕ) :
    variance id (convPow ν k) = k * variance id ν := by
  have := convPow_isProbabilityMeasure ν k
  rw [variance_id_eq_of_ae_abs_le (ae_abs_le_convPow hν k), variance_id_eq_of_ae_abs_le hν]
  exact (convPow_moments hν k).2

end ConvolutionMoments

/-! ### The CRR step law and its `n`-step convolution -/

/-- The CRR step law is carried by `[−|σ√(T/n)|, |σ√(T/n)|]`. -/
lemma crrStepMeasure_ae_abs_le (r σ T : ℝ) (n : ℕ) :
    ∀ᵐ x ∂(crrStepMeasure r σ T n), |x| ≤ |σ * Real.sqrt (T / n)| := by
  rw [crrStepMeasure, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (by simp [ae_dirac_eq]) _,
    Measure.ae_smul_measure (by simp [ae_dirac_eq]) _⟩

/-- **The mean of one CRR log-return step**: `(2pₙ − 1)·σ√(T/n)`, for `0 ≤ pₙ ≤ 1`. -/
lemma integral_id_crrStepMeasure {r σ T : ℝ} {n : ℕ} (hp0 : 0 ≤ crrProb r σ T n)
    (hp1 : crrProb r σ T n ≤ 1) :
    ∫ x, x ∂(crrStepMeasure r σ T n) = (2 * crrProb r σ T n - 1) * (σ * Real.sqrt (T / n)) := by
  rw [integral_crrStepMeasure hp0 hp1 fun x ↦ x]
  ring

/-- **The variance of one CRR log-return step**: `4pₙ(1 − pₙ)·(σ√(T/n))²`, for `0 ≤ pₙ ≤ 1`. -/
lemma variance_id_crrStepMeasure {r σ T : ℝ} {n : ℕ} (hp0 : 0 ≤ crrProb r σ T n)
    (hp1 : crrProb r σ T n ≤ 1) :
    variance id (crrStepMeasure r σ T n)
      = 4 * crrProb r σ T n * (1 - crrProb r σ T n) * (σ * Real.sqrt (T / n)) ^ 2 := by
  have := isProbabilityMeasure_crrStepMeasure hp0 hp1
  rw [variance_id_eq_of_ae_abs_le (crrStepMeasure_ae_abs_le r σ T n),
    integral_crrStepMeasure hp0 hp1 fun x ↦ x ^ 2, integral_id_crrStepMeasure hp0 hp1]
  ring

/-- **Mean and variance of the `n`-step CRR log-return law converge to those of the
Black–Scholes limit.** For `σ, T > 0`, as `n → ∞` the mean and the variance of
`convPow (crrStepMeasure r σ T n) n` converge to the mean `(r − σ²/2)T` and the variance `σ²T`
of `N((r − σ²/2)T, σ²T)` (`bsLimitProbMeasure`), the weak limit of the same laws
(`crr_tendsto_gaussian_inDistribution`). No no-arbitrage hypothesis is needed: `pₙ → 1/2`
(`crrProb_tendsto_half`), so the step law is a probability measure for all large `n`. -/
theorem crrRowLaw_moments_tendsto {r σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun n : ℕ ↦ ∫ x, x ∂(convPow (crrStepMeasure r σ T n) n)) atTop
        (𝓝 (∫ x, x ∂(gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal))) ∧
      Tendsto (fun n : ℕ ↦ variance id (convPow (crrStepMeasure r σ T n) n)) atTop
        (𝓝 (variance id (gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal))) := by
  rw [integral_id_gaussianReal, variance_id_gaussianReal,
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hT.le)]
  have hp : ∀ᶠ n : ℕ in atTop, crrProb r σ T n ∈ Set.Ioo 0 1 :=
    (crrProb_tendsto_half (r := r) hσ hT).eventually_mem (Ioo_mem_nhds (by norm_num) (by norm_num))
  constructor
  · refine (crr_drift_limit_n hσ hT).congr' ?_
    filter_upwards [hp] with n hn
    have := isProbabilityMeasure_crrStepMeasure hn.1.le hn.2.le
    rw [integral_id_convPow (crrStepMeasure_ae_abs_le r σ T n) n,
      integral_id_crrStepMeasure hn.1.le hn.2.le]
    ring
  · refine (crr_variance_limit (r := r) hσ hT).congr' ?_
    filter_upwards [hp, eventually_gt_atTop 0] with n hn hn0
    have := isProbabilityMeasure_crrStepMeasure hn.1.le hn.2.le
    have hcancel : (n : ℝ) * (T / n) = T := mul_div_cancel₀ T (Nat.cast_ne_zero.mpr hn0.ne')
    rw [variance_convPow (crrStepMeasure_ae_abs_le r σ T n) n,
      variance_id_crrStepMeasure hn.1.le hn.2.le, mul_pow,
      Real.sq_sqrt (div_nonneg hT.le n.cast_nonneg)]
    linear_combination (-(4 * σ ^ 2 * crrProb r σ T n * (1 - crrProb r σ T n))) * hcancel

end MathFin

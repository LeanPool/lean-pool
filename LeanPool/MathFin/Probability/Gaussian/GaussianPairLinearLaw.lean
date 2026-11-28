/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.BivariateNormalCDF

/-!
# Linear combinations of a correlated standard Gaussian pair

Let `(U, V)` be jointly Gaussian, each standard normal, with covariance `ρ`. Then `ρ² ≤ 1`
(`sq_le_one_of_covariance_unit`, from `Var[U − ρV] = 1 − ρ² ≥ 0`), and the pair has the
standard bivariate normal law `bivariateNormalLaw ρ` of
`Probability/Gaussian/BivariateNormalCDF.lean`:
a Gaussian law on `ℝ²` is pinned by its means, variances and covariance
(`eq_bivariateNormalLaw`). Every linear combination `aU + bV` is therefore the centred
Gaussian `N(0, a² + 2abρ + b²)` (`map_linear_bivariateNormalLaw`), and its exponential moment
follows from the Gaussian moment generating function:

  `𝔼[e^{aU + bV}] = e^{(a² + 2abρ + b²)/2}`.

This is the computation behind every second moment of a pair of correlated lognormal prices,
such as the cross-moment of a basket (`Models/BlackScholes/BasketMomentMatching.lean`).

## Main results

* `variance_linear_of_unit` — `Var[aU + bV] = a² + 2abρ + b²` for unit variances.
* `covariance_linear_of_unit` — `cov(pU + qV, aU + bV) = pa + (pb + qa)ρ + qb`.
* `sq_le_one_of_covariance_unit` — a covariance of unit-variance variables has `ρ² ≤ 1`.
* `hasLaw_bivariateNormalLaw_of_gaussianPair` — `(U, V) ~ bivariateNormalLaw ρ`.
* `hasLaw_linear_gaussianPair` — `aU + bV ~ N(0, a² + 2abρ + b²)`.
* `integral_exp_linear_gaussianPair` — `𝔼[e^{aU + bV}] = e^{(a² + 2abρ + b²)/2}`.

## Tags

correlated Gaussians, linear combination, basket option, lognormal cross-moment,
moment generating function, bivariate normal, MSC 60E05, MSC 60G15, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Variance of a linear combination of unit-variance variables**:
`Var[aU + bV] = a² + 2abρ + b²` when `Var U = Var V = 1` and `cov(U, V) = ρ`. -/
theorem variance_linear_of_unit [IsFiniteMeasure P] {U V : Ω → ℝ} {ρ : ℝ}
    (hmU : MemLp U 2 P) (hmV : MemLp V 2 P) (hU : Var[U; P] = 1) (hV : Var[V; P] = 1)
    (hcov : cov[U, V; P] = ρ) (a b : ℝ) :
    Var[fun ω ↦ a * U ω + b * V ω; P] = a ^ 2 + 2 * a * b * ρ + b ^ 2 := by
  rw [variance_fun_add (hmU.const_mul a) (hmV.const_mul b), variance_const_mul,
    variance_const_mul, covariance_const_mul_left, covariance_const_mul_right, hcov, hU, hV]
  ring

/-- **Covariance of two linear combinations of unit-variance variables**:
`cov(pU + qV, aU + bV) = pa + (pb + qa)ρ + qb` when `Var U = Var V = 1` and
`cov(U, V) = ρ` (covariance bilinearity). -/
theorem covariance_linear_of_unit [IsFiniteMeasure P] {U V : Ω → ℝ} {ρ : ℝ}
    (hmU : MemLp U 2 P) (hmV : MemLp V 2 P) (hU : Var[U; P] = 1) (hV : Var[V; P] = 1)
    (hcov : cov[U, V; P] = ρ) (p q a b : ℝ) :
    cov[fun ω ↦ p * U ω + q * V ω, fun ω ↦ a * U ω + b * V ω; P]
      = p * a + (p * b + q * a) * ρ + q * b := by
  change cov[(fun ω ↦ p * U ω) + (fun ω ↦ q * V ω), (fun ω ↦ a * U ω) + (fun ω ↦ b * V ω); P] = _
  rw [covariance_add_left (hmU.const_mul p) (hmV.const_mul q)
      ((hmU.const_mul a).add (hmV.const_mul b)),
    covariance_add_right (hmU.const_mul p) (hmU.const_mul a) (hmV.const_mul b),
    covariance_add_right (hmV.const_mul q) (hmU.const_mul a) (hmV.const_mul b)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [covariance_self hmU.aemeasurable, covariance_self hmV.aemeasurable, covariance_comm V U,
    hcov, hU, hV]
  ring

/-- **Correlations are at most one in absolute value**: if `Var U = Var V = 1` and
`cov(U, V) = ρ`, then `ρ² ≤ 1`, since `0 ≤ Var[U − ρV] = 1 − ρ²`. -/
theorem sq_le_one_of_covariance_unit [IsFiniteMeasure P] {U V : Ω → ℝ} {ρ : ℝ}
    (hmU : MemLp U 2 P) (hmV : MemLp V 2 P) (hU : Var[U; P] = 1) (hV : Var[V; P] = 1)
    (hcov : cov[U, V; P] = ρ) : ρ ^ 2 ≤ 1 := by
  have h := variance_nonneg (fun ω ↦ 1 * U ω + -ρ * V ω) P
  rw [variance_linear_of_unit hmU hmV hU hV hcov] at h
  nlinarith [h]

/-- **A standardized Gaussian pair has the standard bivariate normal law**: if `(U, V)` is
jointly Gaussian with `U, V ~ N(0, 1)` and `cov(U, V) = ρ`, then
`(U, V) ~ bivariateNormalLaw ρ`. The law of the pair is Gaussian with the coordinate means,
variances and covariance of `bivariateNormalLaw ρ`, so `eq_bivariateNormalLaw` identifies it. -/
theorem hasLaw_bivariateNormalLaw_of_gaussianPair {U V : Ω → ℝ} {ρ : ℝ}
    (hUV : HasGaussianLaw (fun ω ↦ (U ω, V ω)) P)
    (hU : HasLaw U (gaussianReal 0 1) P) (hV : HasLaw V (gaussianReal 0 1) P)
    (hcov : cov[U, V; P] = ρ) :
    HasLaw (fun ω ↦ (U ω, V ω)) (bivariateNormalLaw ρ) P := by
  have := hUV.isProbabilityMeasure
  have := hUV.isGaussian_map
  have hU1 : Var[U; P] = 1 := by
    rw [hU.variance_eq, variance_id_gaussianReal, NNReal.coe_one]
  have hV1 : Var[V; P] = 1 := by
    rw [hV.variance_eq, variance_id_gaussianReal, NNReal.coe_one]
  have hρ := sq_le_one_of_covariance_unit hU.hasGaussianLaw.memLp_two
    hV.hasGaussianLaw.memLp_two hU1 hV1 hcov
  have hpair : AEMeasurable (fun ω ↦ (U ω, V ω)) P := hUV.aemeasurable
  refine ⟨hpair, eq_bivariateNormalLaw hρ ?_ ?_ ?_ ?_ ?_⟩
  · rw [integral_map hpair measurable_fst.aestronglyMeasurable]
    exact hU.integral_eq.trans integral_id_gaussianReal
  · rw [integral_map hpair measurable_snd.aestronglyMeasurable]
    exact hV.integral_eq.trans integral_id_gaussianReal
  · rw [variance_map measurable_fst.aemeasurable hpair]
    exact hU1
  · rw [variance_map measurable_snd.aemeasurable hpair]
    exact hV1
  · rw [covariance_map measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
      hpair]
    exact hcov

/-- **A linear combination of a correlated standard Gaussian pair is Gaussian**: for `(U, V)`
jointly Gaussian with `U, V ~ N(0, 1)` and `cov(U, V) = ρ`, `aU + bV ~ N(0, a² + 2abρ + b²)`:
the law `map_linear_bivariateNormalLaw` of a linear functional of `bivariateNormalLaw ρ`,
transported along `hasLaw_bivariateNormalLaw_of_gaussianPair`. -/
theorem hasLaw_linear_gaussianPair {U V : Ω → ℝ} {ρ : ℝ}
    (hUV : HasGaussianLaw (fun ω ↦ (U ω, V ω)) P)
    (hU : HasLaw U (gaussianReal 0 1) P) (hV : HasLaw V (gaussianReal 0 1) P)
    (hcov : cov[U, V; P] = ρ) (a b : ℝ) :
    HasLaw (fun ω ↦ a * U ω + b * V ω)
      (gaussianReal 0 (a ^ 2 + 2 * a * b * ρ + b ^ 2).toNNReal) P := by
  have := hUV.isProbabilityMeasure
  have hρ := sq_le_one_of_covariance_unit hU.hasGaussianLaw.memLp_two
    hV.hasGaussianLaw.memLp_two
    (by rw [hU.variance_eq, variance_id_gaussianReal, NNReal.coe_one])
    (by rw [hV.variance_eq, variance_id_gaussianReal, NNReal.coe_one]) hcov
  exact HasLaw.comp ⟨by fun_prop, map_linear_bivariateNormalLaw hρ a b⟩
    (hasLaw_bivariateNormalLaw_of_gaussianPair hUV hU hV hcov)

/-- **Exponential moment of a linear combination of a correlated standard Gaussian pair**:
`𝔼[e^{aU + bV}] = e^{(a² + 2abρ + b²)/2}`, the moment generating function of
`N(0, a² + 2abρ + b²)` (`hasLaw_linear_gaussianPair`) at `1`. -/
theorem integral_exp_linear_gaussianPair {U V : Ω → ℝ} {ρ : ℝ}
    (hUV : HasGaussianLaw (fun ω ↦ (U ω, V ω)) P)
    (hU : HasLaw U (gaussianReal 0 1) P) (hV : HasLaw V (gaussianReal 0 1) P)
    (hcov : cov[U, V; P] = ρ) (a b : ℝ) :
    ∫ ω, Real.exp (a * U ω + b * V ω) ∂P = Real.exp ((a ^ 2 + 2 * a * b * ρ + b ^ 2) / 2) := by
  have := hUV.isProbabilityMeasure
  have hL := hasLaw_linear_gaussianPair hUV hU hV hcov a b
  have hnn : 0 ≤ a ^ 2 + 2 * a * b * ρ + b ^ 2 := by
    rw [← variance_linear_of_unit hU.hasGaussianLaw.memLp_two hV.hasGaussianLaw.memLp_two
      (by rw [hU.variance_eq, variance_id_gaussianReal, NNReal.coe_one])
      (by rw [hV.variance_eq, variance_id_gaussianReal, NNReal.coe_one]) hcov a b]
    exact variance_nonneg _ _
  have hmgf := congrFun (mgf_fun_id_gaussianReal (μ := 0)
    (v := (a ^ 2 + 2 * a * b * ρ + b ^ 2).toNNReal)) 1
  simp only [mgf, one_mul, mul_one, one_pow, zero_add] at hmgf
  rw [← Real.coe_toNNReal _ hnn, ← hmgf]
  exact hL.integral_comp (f := Real.exp) Real.continuous_exp.aestronglyMeasurable

end MathFin

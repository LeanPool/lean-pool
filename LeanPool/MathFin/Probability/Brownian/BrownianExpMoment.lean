/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.BrownianMartingale

/-! # Exponential moments of Brownian marginals

A pre-Brownian motion's marginal `B_s` is `N(0, s)`, so it has *every* exponential
moment. Concretely, transferring the standard Gaussian moment-generating function
(`integrable_exp_mul_gaussianReal`, `mgf_id_gaussianReal`) along the law
`hB.hasLaw_eval s : HasLaw (B s) (gaussianReal 0 s) μ`,

  `∫ exp(c · B_s) ∂μ = exp(c² s / 2)`,

and the absolute-value variant `exp(c · |B_s|) ∈ L²(μ)` with the uniform bound
`∫ exp(c · |B_s|) ∂μ ≤ 2 · exp(c² s / 2)` (via `exp(c|x|) ≤ exp(cx) + exp(−cx)`).

These are the integrability base stones the exponential-growth Itô formula
(`ItoFormulaLocalized`) needs to dominate its cutoff approximants: the marginal
exponential moment, together with Tonelli, controls the `L²` norm of path
integrals of exponential-growth integrands. `GaussianMoments` holds the
*polynomial* moments; this file holds the exponential ones.

## Main results

* `integral_exp_mul_eval`: `∫ exp(c · B_s) ∂μ = exp(c² s / 2)` for a pre-Brownian motion `B`.
* `integrable_exp_mul_eval`, `memLp_exp_mul_eval`: `exp(c · B_s)` is integrable and in `L²(μ)`.
* `memLp_exp_incr`: `exp(c · (B_v − B_u))` is in `L²(μ)`.
* `memLp_exp_abs_eval`, `integrable_exp_abs_eval`: `exp(c · |B_s|)` is in `L²(μ)` and integrable.
* `integral_exp_abs_eval_le`: `∫ exp(c · |B_s|) ∂μ ≤ 2 · exp(c² s / 2)`.

## Tags

exponential moment, moment generating function, Gaussian marginal, lognormal, Brownian motion,
MSC 60J65, MSC 60E10
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- Pointwise: `exp(c|x|) ≤ exp(cx) + exp(−cx)` (the absolute value picks the larger
exponent; the other summand is nonnegative). -/
lemma exp_mul_abs_le_add (c x : ℝ) :
    Real.exp (c * |x|) ≤ Real.exp (c * x) + Real.exp (-c * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]; exact le_add_of_nonneg_left (Real.exp_nonneg _)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- `exp(c · B_s)` is integrable: Mathlib's `integrable_exp_mul_gaussianReal` transferred along
`HasLaw.integrable_fun_comp` at the marginal law `B_s ~ N(0, s)`. -/
lemma integrable_exp_mul_eval (s : ℝ≥0) (c : ℝ) :
    Integrable (fun ω ↦ Real.exp (c * B s ω)) μ :=
  (hB.hasLaw_eval s).integrable_fun_comp (integrable_exp_mul_gaussianReal c)

/-- The Brownian marginal MGF: `∫ exp(c · B_s) ∂μ = exp(c² s / 2)`, the gaussianReal MGF
`integral_exp_mul_gaussianReal_zero` transferred along `B_s ~ N(0, s)`. -/
lemma integral_exp_mul_eval (s : ℝ≥0) (c : ℝ) :
    ∫ ω, Real.exp (c * B s ω) ∂μ = Real.exp (c ^ 2 * (s : ℝ) / 2) := by
  have hg : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (c * x)) (Measure.map (B s) μ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  rw [(integral_map (hB.hasLaw_eval s).aemeasurable hg).symm, (hB.hasLaw_eval s).map_eq,
    integral_exp_mul_gaussianReal_zero]

/-- `exp(c · B_s) ∈ L²(μ)`: its square is `exp(2c · B_s)`, integrable by the marginal MGF. -/
lemma memLp_exp_mul_eval (s : ℝ≥0) (c : ℝ) :
    MemLp (fun ω ↦ Real.exp (c * B s ω)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.exp (c * B s ω)) μ :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp_aemeasurable
      (hB.hasLaw_eval s).aemeasurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : (fun ω ↦ Real.exp (c * B s ω) ^ 2) = (fun ω ↦ Real.exp (2 * c * B s ω)) := by
    funext ω; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hsq]
  exact integrable_exp_mul_eval hB s (2 * c)

/-- `exp(c · |B_s|) ∈ L²(μ)`: dominated by `exp(c · B_s) + exp(−c · B_s) ∈ L²`. -/
lemma memLp_exp_abs_eval (s : ℝ≥0) (c : ℝ) :
    MemLp (fun ω ↦ Real.exp (c * |B s ω|)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.exp (c * |B s ω|)) μ :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
      (hB.hasLaw_eval s).aemeasurable).aestronglyMeasurable
  refine ((memLp_exp_mul_eval hB s c).add (memLp_exp_mul_eval hB s (-c))).mono hmeas
    (ae_of_all _ fun ω ↦ ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp (c * B s ω) + Real.exp (-c * B s ω))]
  exact exp_mul_abs_le_add c (B s ω)

/-- `exp(c · (B_v − B_u)) ∈ L²(μ)`: an increment has a second exponential moment too.
The increment is not a marginal, so the law transfer does not apply to it directly;
instead `xy ≤ ½(x² + y²)` splits it into the two marginals `exp(2c·B_v)` and
`exp(−2c·B_u)`, each already in `L²`. -/
lemma memLp_exp_incr (u v : ℝ≥0) (c : ℝ) :
    MemLp (fun ω ↦ Real.exp (c * (B v ω - B u ω))) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.exp (c * (B v ω - B u ω))) μ :=
    (Real.measurable_exp.comp_aemeasurable
      (((hB.hasLaw_eval v).aemeasurable.sub (hB.hasLaw_eval u).aemeasurable).const_mul
        c)).aestronglyMeasurable
  have key (ω : Ω) : Real.exp (c * (B v ω - B u ω))
      ≤ 1 / 2 * (Real.exp (2 * c * B v ω) + Real.exp (-(2 * c) * B u ω)) := by
    have h1 : Real.exp (c * (B v ω - B u ω))
        = Real.exp (c * B v ω) * Real.exp (-(c * B u ω)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (2 * c * B v ω) = Real.exp (c * B v ω) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(2 * c) * B u ω) = Real.exp (-(c * B u ω)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h1, h2, h3]
    nlinarith [sq_nonneg (Real.exp (c * B v ω) - Real.exp (-(c * B u ω)))]
  refine MemLp.mono (((memLp_exp_mul_eval hB v (2 * c)).add
    (memLp_exp_mul_eval hB u (-(2 * c)))).const_mul (1 / 2)) hmeas (ae_of_all _ fun ω ↦ ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 1 / 2 * (Real.exp (2 * c * B v ω) + Real.exp (-(2 * c) * B u ω)))]
  exact key ω

/-- `exp(c · |B_s|)` is integrable: dominated by `exp(c·B_s) + exp(−c·B_s) ∈ L¹`. -/
lemma integrable_exp_abs_eval (s : ℝ≥0) (c : ℝ) :
    Integrable (fun ω ↦ Real.exp (c * |B s ω|)) μ :=
  ((integrable_exp_mul_eval hB s c).add (integrable_exp_mul_eval hB s (-c))).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
      (hB.hasLaw_eval s).aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]; exact exp_mul_abs_le_add c (B s ω))

/-- Uniform exponential-moment bound: `∫ exp(c · |B_s|) ∂μ ≤ 2 · exp(c² s / 2)`. -/
lemma integral_exp_abs_eval_le (s : ℝ≥0) (c : ℝ) :
    ∫ ω, Real.exp (c * |B s ω|) ∂μ ≤ 2 * Real.exp (c ^ 2 * (s : ℝ) / 2) := by
  have hbnd : ∀ ω, Real.exp (c * |B s ω|)
      ≤ Real.exp (c * B s ω) + Real.exp (-c * B s ω) := fun ω ↦ exp_mul_abs_le_add c (B s ω)
  have hlhs_int : Integrable (fun ω ↦ Real.exp (c * |B s ω|)) μ := integrable_exp_abs_eval hB s c
  have hsum_int : Integrable (fun ω ↦ Real.exp (c * B s ω) + Real.exp (-c * B s ω)) μ :=
    (integrable_exp_mul_eval hB s c).add (integrable_exp_mul_eval hB s (-c))
  calc ∫ ω, Real.exp (c * |B s ω|) ∂μ
      ≤ ∫ ω, (Real.exp (c * B s ω) + Real.exp (-c * B s ω)) ∂μ :=
        integral_mono hlhs_int hsum_int hbnd
    _ = Real.exp (c ^ 2 * (s : ℝ) / 2) + Real.exp ((-c) ^ 2 * (s : ℝ) / 2) := by
        rw [integral_add (integrable_exp_mul_eval hB s c) (integrable_exp_mul_eval hB s (-c)),
          integral_exp_mul_eval hB s c, integral_exp_mul_eval hB s (-c)]
    _ = 2 * Real.exp (c ^ 2 * (s : ℝ) / 2) := by rw [neg_sq]; ring

end MathFin

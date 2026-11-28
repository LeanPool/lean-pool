/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Esscher transform of a law on `ℝ`

The Esscher transform with parameter `θ` reweights a law `μ` on `ℝ` by `e^{θx}` and renormalizes
it: Mathlib's exponentially tilted measure `μ.tilted (θ * ·)`. Gerber and Shiu use it to choose a
pricing measure; here it acts on one law on `ℝ`. For a Gaussian law it is the static Girsanov change
of measure.

* `integral_exp_mul_tilted_const_mul`, `mgf_id_tilted_const_mul`: the exponential moments of the
  tilted law are ratios of those of `μ`, `∫ e^{ux} dμ_θ = ∫ e^{(u + θ)x} dμ / ∫ e^{θx} dμ`
  (Mathlib's `integral_exp_tilted` at linear exponents).
* `integrable_exp_mul_tilted_const_mul`: `μ_θ` has the exponential moment of order `u` when `μ` has
  those of orders `θ` and `u + θ`; so where the moment-generating function of `μ` is finite near
  `θ`, that of `μ_θ` is finite near `0` (`zero_mem_interior_integrableExpSet_tilted`).
* `measure_eq_of_mgf_id_eventuallyEq`: a finite measure whose moment-generating function is finite
  near `0` is determined by that function near `0` (the identity theorem for Mathlib's complex
  moment-generating function); `measure_eq_of_mgf_id_eq` is the case of every exponential moment.
* `ofReal_integral_exp_smul_tilted`: before it is normalized the transform is a density,
  `(∫ e^f dμ)·μ.tilted f = e^f·μ` when `e^f` is integrable, for a measure on any space. On a Lévy
  measure this is how the transform acts on the jumps (`smul_tilted_eq_withDensity`).
* `gaussianReal_tilted_const_mul`: the transform shifts the mean of a Gaussian law, `N(m, v)`
  tilted by `e^{θx}` is `N(m + θv, v)`.

The first three identify a tilted law by computing one function. Their users: the Esscher
transform of the jump-diffusion log-return law (`jumpDiffusionIncrementLaw_tilted`) uses all three;
the Gaussian increments of `isQBrownianMotion_of_expMartingale` are identified by
`measure_eq_of_mgf_id_eq`; and the identification of the Lévy measure from the law
(`jumpDiffusionIncrementLaw_eq_iff`) applies `measure_eq_of_mgf_id_eventuallyEq` to finite measures
that are not probability laws. The Gaussian tilt gives the static Girsanov change of measure
(`gaussianReal_withDensity_esscher`, its case `N(0, 1)`), the change of drift of a jump-diffusion
law (`jumpDiffusionIncrementLaw_absolutelyContinuous`), the no-jump tilt
(`jumpDiffusionIncrementLaw_zero_tilted`) and Merton's tilted jumps (`mertonJump_tilted`).

## Main results

* `mgf_id_tilted_const_mul`: for the Esscher-tilted law `μ_θ = μ.tilted (θ * ·)`,
  `mgf id μ_θ u = mgf id μ (u + θ) / mgf id μ θ`.
* `integral_exp_mul_tilted_const_mul`, `integrable_exp_mul_tilted_const_mul`: the same identity on
  `∫ e^{ux}`, and integrability of `e^{ux}` under `μ_θ` when `e^{θx}` and `e^{(u+θ)x}` are
  `μ`-integrable.
* `measure_eq_of_mgf_id_eventuallyEq`, `measure_eq_of_mgf_id_eq`: a finite measure on `ℝ` is
  determined by its moment-generating function near `0` (when `0` is interior to the set of
  integrable exponents), and by that function when every exponential moment exists.
* `ofReal_integral_exp_smul_tilted`: when `e^f` is `μ`-integrable, `(∫ e^f dμ)·μ.tilted f` is
  the measure with density `e^f` against `μ`.
* `gaussianReal_tilted_const_mul`: tilting `N(m, v)` by `e^{θx}` gives `N(m + θ v, v)`.

## References

* [Esscher, *On the probability function in the collective theory of risk*][Esscher1932]
* [Gerber and Shiu, *Option pricing by Esscher transforms*][GerberShiu1994]

## Tags

Esscher transform, exponential tilting, Gerber–Shiu, pricing measure, Gaussian tilt,
moment generating function, MSC 60E10, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal Topology

/-- **A measure is determined by its moment-generating function near `0`**: if the
moment-generating function of a finite measure `μ` on `ℝ` is finite on a neighbourhood of `0`,
every finite measure `μ'` with the same moment-generating function on a neighbourhood of `0` is
`μ`. On an interval `(-ε, ε)` of exponential moments of both, the complex moment-generating
functions are analytic in the vertical strip `|Re z| < ε` (Mathlib's `analyticOnNhd_complexMGF`)
and agree at its real points, hence on the whole strip (the identity theorem). On the imaginary
axis they are the characteristic functions (`complexMGF_id_mul_I`), which determine the measure
(`Measure.ext_of_charFun`). -/
lemma measure_eq_of_mgf_id_eventuallyEq {μ μ' : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (h0 : 0 ∈ interior (integrableExpSet id μ))
    (h : mgf id μ =ᶠ[𝓝 0] mgf id μ') : μ = μ' := by
  -- the zero measure: `μ'` has total mass `mgf id μ' 0 = 0`
  rcases eq_or_ne μ 0 with rfl | hμ0
  · have h00 : μ'.real Set.univ = 0 := by
      rw [← mgf_zero' (X := id), ← h.eq_of_nhds, mgf_zero_measure, Pi.zero_apply]
    rw [measureReal_eq_zero_iff, Measure.measure_univ_eq_zero] at h00
    exact h00.symm
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((eventually_mem_set.2 (mem_interior_iff_mem_nhds.1 h0)).and h)
  -- both measures have the exponential moments of the orders in `(-ε, ε)`
  have hμ : Metric.ball (0 : ℝ) ε ⊆ interior (integrableExpSet id μ) :=
    interior_maximal (fun t ht ↦ (hball t ht).1) Metric.isOpen_ball
  have hμ' : Metric.ball (0 : ℝ) ε ⊆ interior (integrableExpSet id μ') := by
    refine interior_maximal (fun t ht ↦ ?_) Metric.isOpen_ball
    have hpos : mgf id μ' t ≠ 0 := (hball t ht).2 ▸ (mgf_pos' (X := id) hμ0 (hball t ht).1).ne'
    by_contra hint
    exact hpos (mgf_undef (X := id) hint)
  -- so their complex moment-generating functions agree on the strip `|Re z| < ε`
  have hS : IsPreconnected {z : ℂ | z.re ∈ Metric.ball (0 : ℝ) ε} :=
    ((convex_ball (0 : ℝ) ε).linear_preimage Complex.reLm).isPreconnected
  have hEq : Set.EqOn (complexMGF id μ) (complexMGF id μ')
      {z : ℂ | z.re ∈ Metric.ball (0 : ℝ) ε} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      (analyticOnNhd_complexMGF.mono fun z hz ↦ hμ hz)
      (analyticOnNhd_complexMGF.mono fun z hz ↦ hμ' hz) hS (z₀ := ((0 : ℝ) : ℂ))
      (by simpa using hε) ?_
    have h_real : ∃ᶠ x : ℝ in 𝓝[≠] 0, complexMGF id μ x = complexMGF id μ' x :=
      (Eventually.frequently (h.filter_mono nhdsWithin_le_nhds)).mono fun y hy ↦ by
        rw [complexMGF_ofReal, complexMGF_ofReal, hy]
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n ↦ xs n, ?_, hx_eq⟩
    rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    exact ⟨tendsto_ofReal_iff.2 hx_tendsto.1, by simpa using hx_tendsto.2⟩
  -- on the imaginary axis they are the characteristic functions
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact hEq (by simpa using hε)

/-- **A measure with exponential moments of every order is determined by its moment-generating
function**: a finite measure `μ` on `ℝ` with every exponential moment equals each finite measure
`μ'` with the same moment-generating function (`measure_eq_of_mgf_id_eventuallyEq`). -/
lemma measure_eq_of_mgf_id_eq {μ μ' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hμ : ∀ u, Integrable (fun x ↦ rexp (u * x)) μ) (h : mgf id μ = mgf id μ') : μ = μ' := by
  have hset : integrableExpSet id μ = Set.univ := Set.eq_univ_of_forall hμ
  exact measure_eq_of_mgf_id_eventuallyEq (by simp [hset]) (Eventually.of_forall (congr_fun h))

/-- **The exponential moments of an Esscher-tilted law** are ratios of those of the law:
`∫ e^{ux} dμ_θ = ∫ e^{(u + θ)x} dμ / ∫ e^{θx} dμ`, for `μ_θ = μ.tilted (θ * ·)`. This is Mathlib's
`integral_exp_tilted` at linear exponents. -/
lemma integral_exp_mul_tilted_const_mul (μ : Measure ℝ) (θ u : ℝ) :
    ∫ x, rexp (u * x) ∂(μ.tilted (θ * ·))
      = (∫ x, rexp ((u + θ) * x) ∂μ) / ∫ x, rexp (θ * x) ∂μ := by
  simp only [integral_exp_tilted, Pi.add_apply, ← add_mul, add_comm θ u]

/-- `integral_exp_mul_tilted_const_mul` in Mathlib's terms:
`mgf id μ_θ u = mgf id μ (u + θ) / mgf id μ θ`. -/
lemma mgf_id_tilted_const_mul (μ : Measure ℝ) (θ u : ℝ) :
    mgf id (μ.tilted (θ * ·)) u = mgf id μ (u + θ) / mgf id μ θ :=
  integral_exp_mul_tilted_const_mul μ θ u

/-- **The Esscher transform before normalization**: when `e^f` is `μ`-integrable, `μ` tilted by `f`
and scaled back by its normalizing constant `∫ e^f dμ` is `μ` with density `e^f`. On a Lévy measure
this is how the transform acts on the jumps (`smul_tilted_eq_withDensity`). -/
lemma ofReal_integral_exp_smul_tilted {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} (hf : Integrable (fun x ↦ rexp (f x)) μ) :
    ENNReal.ofReal (∫ x, rexp (f x) ∂μ) • μ.tilted f
      = μ.withDensity fun x ↦ ENNReal.ofReal (rexp (f x)) := by
  rcases eq_zero_or_neZero μ with rfl | _
  · simp
  have hm : 0 < ∫ x, rexp (f x) ∂μ := integral_exp_pos hf
  rw [Measure.tilted, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine congrArg μ.withDensity (funext fun x ↦ ?_)
  rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hm.le, mul_div_cancel₀ _ hm.ne']

/-- An Esscher-tilted law has the exponential moment of order `u` when the law has those of orders
`θ` and `u + θ`. -/
lemma integrable_exp_mul_tilted_const_mul {μ : Measure ℝ} {θ u : ℝ}
    (hθ : Integrable (fun x ↦ rexp (θ * x)) μ) (hu : Integrable (fun x ↦ rexp ((u + θ) * x)) μ) :
    Integrable (fun x ↦ rexp (u * x)) (μ.tilted (θ * ·)) := by
  rw [integrable_tilted_iff hθ]
  simpa only [smul_eq_mul, ← Real.exp_add, ← add_mul, add_comm θ u] using hu

/-- Where the moment-generating function of `μ` is finite near `θ`, `μ` has the exponential
moments of the orders `u + θ` for `u` near `0`. -/
lemma eventually_integrable_exp_add_mul {μ : Measure ℝ} {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet id μ)) :
    ∀ᶠ u in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp ((u + θ) * x)) μ :=
  ((continuous_add_const θ).tendsto' 0 θ (zero_add θ)).eventually_mem
    (mem_interior_iff_mem_nhds.1 hθ)

/-- Where the moment-generating function of `μ` is finite near `θ`, that of the tilted law
`μ.tilted (θ * ·)` is finite near `0` (`integrable_exp_mul_tilted_const_mul`). -/
lemma zero_mem_interior_integrableExpSet_tilted {μ : Measure ℝ} {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet id μ)) :
    0 ∈ interior (integrableExpSet id (μ.tilted (θ * ·))) := by
  have hint : ∀ᶠ u in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp (u * x)) (μ.tilted (θ * ·)) :=
    (eventually_integrable_exp_add_mul hθ).mono fun u hu ↦
      integrable_exp_mul_tilted_const_mul (interior_subset (s := integrableExpSet id μ) hθ) hu
  exact mem_interior_iff_mem_nhds.2 hint

/-- **The Esscher transform of a Gaussian law shifts its mean**: `N(m, v)` tilted by `e^{θx}` is
`N(m + θv, v)`. The Gaussian `N(m + θv, v)` has every exponential moment, and the two
moment-generating functions agree: `𝔼[e^{(u + θ)X}] / 𝔼[e^{θX}] = e^{(m + θv)u + vu²/2}` for
`X ~ N(m, v)` (Mathlib's `mgf_id_gaussianReal`). -/
lemma gaussianReal_tilted_const_mul (m : ℝ) (v : ℝ≥0) (θ : ℝ) :
    (gaussianReal m v).tilted (θ * ·) = gaussianReal (m + θ * v) v := by
  refine Eq.symm (measure_eq_of_mgf_id_eq integrable_exp_mul_gaussianReal (funext fun u ↦ ?_))
  simp only [mgf_id_tilted_const_mul, mgf_id_gaussianReal, ← Real.exp_sub]
  congr 1
  ring

end MathFin

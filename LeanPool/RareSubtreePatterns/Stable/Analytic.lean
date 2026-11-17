/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Analytic helpers for the stable toolbox

* `PoissonDeclumping.Stable.eqOn_halfPlane_of_eq_real`: identity theorem on a left
  half-plane `{Re z < c}` from agreement at real points.
* `PoissonDeclumping.Stable.integral_cexp_neg_mul_rpow`: the complex Gamma integral
  `∫_0^∞ exp(-r θ^p) dθ = Γ(1/p + 1) r^{-1/p}` for `Re r > 0` (mathlib only has real `r`);
  proved by analytic continuation in `r`, through the complex moment generating function of
  `θ ↦ θ^p` under the finite measure `e^{-θ^p} dθ` on `(0,∞)`.
* integrability on `ℝ` of `|θ|^s exp(-c|θ|^p)`.

These are used to identify the characteristic function and the density of the limit law
(source lines 846–864).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology NNReal ENNReal

namespace PoissonDeclumping.Stable

/-- Identity theorem on a left half-plane: analytic functions agreeing on the real points of
`{Re z < c}` agree on the half-plane. -/
lemma eqOn_halfPlane_of_eq_real {f g : ℂ → ℂ} {c : ℝ}
    (hf : AnalyticOnNhd ℂ f {z | z.re < c}) (hg : AnalyticOnNhd ℂ g {z | z.re < c})
    (h : ∀ t : ℝ, t < c → f t = g t) : EqOn f g {z | z.re < c} := by
  have hU : IsPreconnected {z : ℂ | z.re < c} := (convex_halfSpace_re_lt c).isPreconnected
  have hmem : ((c - 1 : ℝ) : ℂ) ∈ {z : ℂ | z.re < c} := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg hU hmem ?_
  have ht : Tendsto (fun n : ℕ => ((c - 1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop
      (𝓝[≠] ((c - 1 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun n : ℕ => (c - 1 + 1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 (c - 1 + 0)) := by
        apply Tendsto.add tendsto_const_nhds
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      rw [add_zero] at this
      have := (Complex.continuous_ofReal.tendsto _).comp this
      simpa [Function.comp_def] using this
    · refine Eventually.of_forall fun n => ?_
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h2 : (c - 1 + 1 / ((n:ℝ) + 2) : ℝ) = c - 1 := by exact_mod_cast h
      have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith
  apply ht.frequently
  refine Frequently.of_forall fun n => h _ ?_
  have : 1 / ((n : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  linarith

section GammaIntegral

variable {p : ℝ}

/-- The finite measure `e^{-θ^p} dθ` on `(0,∞)`. -/
noncomputable def gammaMeasure (p : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun θ => ((Real.exp (-θ ^ p)).toNNReal : ℝ≥0∞))

lemma measurable_gammaDensity (p : ℝ) :
    Measurable fun θ : ℝ => (Real.exp (-θ ^ p)).toNNReal := by
  apply Measurable.real_toNNReal
  exact (Measurable.pow_const measurable_id _).neg.exp

lemma complexMGF_gammaMeasure (z : ℂ) :
    complexMGF (fun θ : ℝ => θ ^ p) (gammaMeasure p) z =
      ∫ θ in Ioi (0 : ℝ), cexp ((z - 1) * ((θ ^ p : ℝ) : ℂ)) := by
  rw [complexMGF, gammaMeasure, integral_withDensity_eq_integral_smul (measurable_gammaDensity p)]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]
  rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma Iio_one_subset_integrableExpSet_gamma (hp : 0 < p) :
    Iio (1 : ℝ) ⊆ integrableExpSet (fun θ : ℝ => θ ^ p) (gammaMeasure p) := by
  intro t ht
  simp only [integrableExpSet, mem_ofPred_eq, gammaMeasure]
  rw [integrable_withDensity_iff_integrable_smul (measurable_gammaDensity p)]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (b := 1 - t) (by norm_num) hp
    (by simpa using ht)
  refine (h.congr_fun (fun θ hθ => ?_) measurableSet_Ioi)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, smul_eq_mul,
    Real.rpow_zero, one_mul, ← Real.exp_add]
  congr 1
  ring

/-- `∫_0^∞ exp(-r θ^p) dθ = Γ(1/p + 1) r^{-1/p}` for complex `r` with `Re r > 0`. -/
theorem integral_cexp_neg_mul_rpow (hp : 0 < p) {r : ℂ} (hr : 0 < r.re) :
    ∫ θ in Ioi (0 : ℝ), cexp (-r * ((θ ^ p : ℝ) : ℂ)) =
      (Real.Gamma (1 / p + 1) : ℂ) * r ^ (-(1 / p : ℝ) : ℂ) := by
  set X : ℝ → ℝ := fun θ => θ ^ p
  have hsub : {z : ℂ | z.re < 1} ⊆ {z | z.re ∈ interior (integrableExpSet X (gammaMeasure p))} := by
    intro z hz
    exact interior_maximal (Iio_one_subset_integrableExpSet_gamma hp) isOpen_Iio hz
  have hf : AnalyticOnNhd ℂ (complexMGF X (gammaMeasure p)) {z | z.re < 1} :=
    fun z hz => analyticAt_complexMGF (hsub hz)
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => (Real.Gamma (1 / p + 1) : ℂ) *
      (1 - z) ^ (-(1 / p : ℝ) : ℂ)) {z | z.re < 1} := by
    intro z hz
    apply analyticAt_const.mul
    apply AnalyticAt.cpow (analyticAt_const.sub analyticAt_id) analyticAt_const
    rw [mem_slitPlane_iff]; left
    have : z.re < 1 := hz
    change 0 < (1 - z).re
    rw [sub_re, one_re]; linarith
  have heq := eqOn_halfPlane_of_eq_real hf hg (fun t ht => by
    rw [complexMGF_gammaMeasure]
    have h1 := integral_exp_neg_mul_rpow hp (b := 1 - t) (by linarith)
    have h2 : ∀ θ : ℝ, cexp (((t : ℂ) - 1) * ((θ ^ p : ℝ) : ℂ)) =
        ((Real.exp (-(1 - t) * θ ^ p) : ℝ) : ℂ) := by
      intro θ; rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    simp_rw [h2]
    rw [integral_complex_ofReal, h1, show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      show -((1 / p : ℝ) : ℂ) = ((-1 / p : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by linarith)]
    push_cast; ring)
  have := heq (show (1 - r).re < 1 by simp; linarith)
  rw [complexMGF_gammaMeasure] at this
  simpa using this

end GammaIntegral


/-- An even function built from a function integrable on `(0,∞)` is integrable. -/
lemma integrable_comp_abs_of_integrableOn_Ioi {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
    Integrable (fun θ : ℝ => g |θ|) := by
  have h1 : Integrable ((Ioi (0 : ℝ)).indicator g) := (integrable_indicator_iff
    measurableSet_Ioi).2 hg
  have h2 : Integrable ((Ici (0 : ℝ)).indicator g) :=
    (integrable_indicator_iff measurableSet_Ici).2 ((integrableOn_Ici_iff_integrableOn_Ioi (by
      simp)).2 hg)
  have h3 : Integrable (fun θ : ℝ => (Ici (0 : ℝ)).indicator g (-θ)) := h2.comp_neg
  refine (h1.add h3).congr (Eventually.of_forall fun θ => ?_)
  rcases lt_or_ge 0 θ with h | h
  · simp [indicator, h, abs_of_pos h]
  · have : ¬ (0 < θ) := not_lt.mpr h
    simp [indicator, this, h, abs_of_nonpos h]

lemma integrable_rpow_abs_mul_exp_neg {s p c : ℝ} (hs : -1 < s) (hp : 0 < p) (hc : 0 < c) :
    Integrable (fun θ : ℝ => |θ| ^ s * Real.exp (-c * |θ| ^ p)) :=
  integrable_comp_abs_of_integrableOn_Ioi (g := fun x => x ^ s * Real.exp (-c * x ^ p))
    (integrableOn_rpow_mul_exp_neg_mul_rpow hs hp hc)

end PoissonDeclumping.Stable

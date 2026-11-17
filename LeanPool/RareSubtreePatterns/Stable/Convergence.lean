/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.Lattice
public import LeanPool.RareSubtreePatterns.Stable.Density
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Characteristic-function convergence of the normalized walk

Under `(H_α)` (`PoissonDeclumping.StableDomain μ α a`), the laws of `S_m / a_m`
(`PoissonDeclumping.Stable.scaledLaw`) converge weakly to `ν`, whose characteristic function is
`exp((-iθ)^α)` (`PoissonDeclumping.Stable.charFun_eq_stableCF`).

* `PoissonDeclumping.Stable.tendsto_stepCF_pow`: for times `ψ j → ∞` and arguments `s_j → t`,
  `φ(s_j / a_{ψ j})^{ψ j} → exp((-it)^α)`; the moving argument is handled by the uniform
  modulus `|E e^{isY} - E e^{itY}| ≤ E min(2, |s-t||Y|)` and the weak convergence of the
  bounded continuous test function `min(2, δ|x|)` (no tightness argument is needed).
* `PoissonDeclumping.Stable.tendsto_norm_stepCF_pow`: the same for `|φ|`, with limit
  `exp(cos(πα/2)|t|^α)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

variable (μ a) in
/-- The law of `S_m / a_m` on `ℝ`. -/
noncomputable def scaledLaw (m : ℕ) : Measure ℝ :=
  (walkLaw μ m).map (fun z : ℤ => (z : ℝ) / a m)

instance (m : ℕ) : IsProbabilityMeasure (scaledLaw μ a m) := by
  unfold scaledLaw
  constructor
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

lemma norm_cexp_mul_I_sub_le (s t x : ℝ) :
    ‖cexp (s * x * I) - cexp (t * x * I)‖ ≤ min 2 (|s - t| * |x|) := by
  apply le_min
  · calc ‖cexp (s * x * I) - cexp (t * x * I)‖ ≤ ‖cexp (s * x * I)‖ + ‖cexp (t * x * I)‖ :=
          norm_sub_le _ _
      _ = 2 := by
        rw [show (s : ℂ) * x * I = ((s * x : ℝ) : ℂ) * I by push_cast; ring,
          show (t : ℂ) * x * I = ((t * x : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num
  · have h : cexp (s * x * I) - cexp (t * x * I) =
        cexp (t * x * I) * (cexp (I * (((s - t) * x : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]
      congr 2
      push_cast; ring
    rw [h, norm_mul, show (t : ℂ) * x * I = ((t * x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_mul]

/-- The bounded continuous function `x ↦ min 2 (|δ| |x|)`. -/
noncomputable def bumpFn (δ : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min 2 (|δ| * |x|))
    (by fun_prop) 2 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (by positivity))]
      exact min_le_left _ _)

lemma bumpFn_apply (δ x : ℝ) : bumpFn δ x = min 2 (|δ| * |x|) := rfl

lemma norm_charFun_sub_le (P : Measure ℝ) [IsProbabilityMeasure P] {s t δ : ℝ}
    (hst : |s - t| ≤ δ) : ‖charFun P s - charFun P t‖ ≤ ∫ x, bumpFn δ x ∂P := by
  have hi : ∀ u : ℝ, Integrable (fun x : ℝ => cexp (u * x * I)) P := fun u =>
    Integrable.of_bound (C := 1) (by fun_prop) (Eventually.of_forall fun x => by
      rw [show (u : ℂ) * x * I = ((u * x : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply_real, charFun_apply_real, ← integral_sub (hi s) (hi t)]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    (BoundedContinuousFunction.integrable P (bumpFn δ))
  refine Eventually.of_forall fun x => ?_
  refine (norm_cexp_mul_I_sub_le s t x).trans ?_
  rw [bumpFn_apply]
  apply min_le_min le_rfl
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact hst.trans (le_abs_self δ)

lemma tendsto_integral_bumpFn (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Tendsto (fun δ : ℝ => ∫ x, bumpFn δ x ∂ν) (𝓝 0) (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ x, (fun _ => (0 : ℝ)) x ∂ν := by simp
  rw [h0]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (2 : ℝ))
  · exact Eventually.of_forall fun δ => (bumpFn δ).continuous.aestronglyMeasurable
  · refine Eventually.of_forall fun δ => Eventually.of_forall fun x => ?_
    rw [bumpFn_apply, Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (by positivity))]
    exact min_le_left _ _
  · exact integrable_const 2
  · refine Eventually.of_forall fun x => ?_
    have : Continuous fun δ : ℝ => min 2 (|δ| * |x|) := by fun_prop
    simpa [bumpFn_apply] using this.tendsto 0

/-- **Characteristic-function convergence along moving arguments.** Under `(H_α)`, for every
sequence of times `ψ j → ∞` and arguments `s j → t`, `φ(s_j / a_{ψ j})^{ψ j} → exp((-it)^α)`. -/
theorem tendsto_stepCF_pow (h : StableDomain μ α a) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {s : ℕ → ℝ} {t : ℝ} (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun j => stepCF μ (s j / a (ψ j)) ^ ψ j) atTop (𝓝 (stableCF α t)) := by
  obtain ⟨ν, hν, hL, hconv⟩ := h.converges
  have hα0 : 0 < α := by linarith [h.alpha_mem.1]
  rw [← charFun_eq_stableCF hα0 hL]
  have hr : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(scaledLaw μ a (ψ j))) atTop (𝓝 (∫ x, f x ∂ν)) :=
    fun f => (hconv f).comp hψ
  set PL : ℕ → ProbabilityMeasure ℝ := fun j => ⟨scaledLaw μ a (ψ j), inferInstance⟩
  set Pν : ProbabilityMeasure ℝ := ⟨ν, hν⟩
  have hw : Tendsto PL atTop (𝓝 Pν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact hr
  have hcf : Tendsto (fun j => charFun (scaledLaw μ a (ψ j)) t) atTop (𝓝 (charFun ν t)) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at hw
    have := hw (BoundedContinuousFunction.innerProbChar t)
    simpa [PL, Pν, charFun_eq_integral_innerProbChar] using this
  have hgoal : Tendsto (fun j => charFun (scaledLaw μ a (ψ j)) (s j)) atTop
      (𝓝 (charFun ν t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : ∃ δ : ℝ, 0 < δ ∧ ∫ x, bumpFn δ x ∂ν < ε / 4 := by
      have h1 := (tendsto_integral_bumpFn ν).eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 4))
      have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∫ x, bumpFn δ x ∂ν < ε / 4 ∧ 0 < δ :=
        (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      obtain ⟨δ, hδ1, hδ2⟩ := h2.exists
      exact ⟨δ, hδ2, hδ1⟩
    obtain ⟨δ, hδpos, hδν⟩ := hδ
    have e1 : ∀ᶠ j in atTop, |s j - t| ≤ δ := by
      have := (Metric.tendsto_nhds.1 hs) δ hδpos
      filter_upwards [this] with j hj
      rw [Real.dist_eq] at hj; exact hj.le
    have e2 : ∀ᶠ j in atTop, ∫ x, bumpFn δ x ∂(scaledLaw μ a (ψ j)) < ε / 2 :=
      (hr (bumpFn δ)).eventually (gt_mem_nhds (by linarith))
    have e3 : ∀ᶠ j in atTop, dist (charFun (scaledLaw μ a (ψ j)) t) (charFun ν t) < ε / 4 :=
      (Metric.tendsto_nhds.1 hcf) (ε / 4) (by linarith)
    obtain ⟨N, hN⟩ := (e1.and (e2.and e3)).exists_forall_of_atTop
    refine ⟨N, fun j hj => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hN j hj
    calc dist (charFun (scaledLaw μ a (ψ j)) (s j)) (charFun ν t)
        ≤ dist (charFun (scaledLaw μ a (ψ j)) (s j)) (charFun (scaledLaw μ a (ψ j)) t) +
          dist (charFun (scaledLaw μ a (ψ j)) t) (charFun ν t) := dist_triangle _ _ _
      _ < ε / 2 + ε / 4 := by
          gcongr
          rw [dist_eq_norm]
          exact (norm_charFun_sub_le _ h1).trans_lt h2
      _ < ε := by linarith
  refine hgoal.congr fun j => ?_
  exact charFun_walkLaw_map_div μ (ψ j) (a (ψ j)) (s j)

/-- The norm version: `|φ(s_j / a_{ψ j})|^{ψ j} → exp(cos(πα/2) |t|^α)`. -/
theorem tendsto_norm_stepCF_pow (h : StableDomain μ α a) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {s : ℕ → ℝ} {t : ℝ} (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun j => ‖stepCF μ (s j / a (ψ j))‖ ^ ψ j) atTop
      (𝓝 (Real.exp (Real.cos (Real.pi * α / 2) * |t| ^ α))) := by
  have hα0 : α ≠ 0 := by linarith [h.alpha_mem.1]
  rw [← norm_stableCF hα0]
  have := (continuous_norm.tendsto _).comp (tendsto_stepCF_pow h hψ hs)
  simpa [Function.comp_def, norm_pow] using this

end PoissonDeclumping.Stable

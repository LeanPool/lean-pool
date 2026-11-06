/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.Analytic

/-!
# The limit law `Y_α`: characteristic function and uniqueness (Stage 1)

Source lines 174–178 and 846: `Y_α` has Laplace transform `E exp(-λ Y_α) = exp(λ^α)` for
`λ > 0`, with `α ∈ (1,2]`. We prove:

* `PoissonDeclumping.Stable.charFun_eq_stableCF`: `E exp(iθY_α) = exp((-iθ)^α)` (principal
  complex power), by analytic continuation of the Laplace transform to `{Re z < 0}`
  (identity theorem for the complex moment generating function) and dominated convergence to
  the boundary `Re z = 0`;
* `PoissonDeclumping.Stable.norm_stableCF`: `|E exp(iθY_α)| = exp(cos(πα/2) |θ|^α)`, where
  `cos(πα/2) < 0` for `α ∈ (1,2]` (`cos(πα/2) = -1` for `α = 2`);
* `PoissonDeclumping.Stable.integrable_stableCF`: the characteristic function is integrable;
* `PoissonDeclumping.Stable.limitLaw_unique`: the law with this Laplace transform is unique.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

/-- The characteristic function `θ ↦ exp((-iθ)^α)` of the limit law (principal power). -/
noncomputable def stableCF (α θ : ℝ) : ℂ := cexp ((-(θ * I)) ^ (α : ℂ))

lemma stableCF_zero {α : ℝ} (hα : α ≠ 0) : stableCF α 0 = 1 := by
  simp [stableCF, Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hα)]

lemma neg_mul_I_cpow_of_pos {θ : ℝ} (hθ : 0 < θ) (α : ℝ) :
    (-((θ : ℂ) * I)) ^ (α : ℂ) =
      ((θ ^ α : ℝ) : ℂ) * cexp (((-(Real.pi * α / 2)) : ℝ) * I) := by
  have h1 : -((θ : ℂ) * I) = (θ : ℂ) * (-I) := by ring
  rw [h1, cpow_def_of_ne_zero (by simp [hθ.ne']), log_ofReal_mul hθ (by simp), log_neg_I,
    Real.rpow_def_of_pos hθ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma neg_mul_I_cpow_of_neg {θ : ℝ} (hθ : θ < 0) (α : ℝ) :
    (-((θ : ℂ) * I)) ^ (α : ℂ) =
      (((-θ) ^ α : ℝ) : ℂ) * cexp (((Real.pi * α / 2) : ℝ) * I) := by
  have hθ' : 0 < -θ := by linarith
  have h1 : -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, cpow_def_of_ne_zero (by simp [hθ.ne]), log_ofReal_mul hθ' (by simp), log_I,
    Real.rpow_def_of_pos hθ', Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma re_neg_mul_I_cpow {α : ℝ} (hα : α ≠ 0) (θ : ℝ) :
    ((-((θ : ℂ) * I)) ^ (α : ℂ)).re = |θ| ^ α * Real.cos (Real.pi * α / 2) := by
  rcases lt_trichotomy θ 0 with h | rfl | h
  · rw [neg_mul_I_cpow_of_neg h, re_ofReal_mul, Complex.exp_ofReal_mul_I_re, abs_of_neg h]
  · simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hα), Real.zero_rpow hα]
  · rw [neg_mul_I_cpow_of_pos h, re_ofReal_mul, Complex.exp_ofReal_mul_I_re, abs_of_pos h,
      Real.cos_neg]

lemma norm_stableCF {α : ℝ} (hα : α ≠ 0) (θ : ℝ) :
    ‖stableCF α θ‖ = Real.exp (Real.cos (Real.pi * α / 2) * |θ| ^ α) := by
  rw [stableCF, Complex.norm_exp, re_neg_mul_I_cpow hα, mul_comm]

lemma stableCF_neg {α : ℝ} (hα : α ≠ 0) (θ : ℝ) :
    stableCF α (-θ) = (starRingEnd ℂ) (stableCF α θ) := by
  rcases lt_trichotomy θ 0 with h | rfl | h
  · have h' : 0 < -θ := by linarith
    unfold stableCF
    rw [neg_mul_I_cpow_of_pos h' α, neg_mul_I_cpow_of_neg h α, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    congr 3
    push_cast; ring
  · rw [neg_zero, stableCF_zero hα, map_one]
  · have h' : -θ < 0 := by linarith
    unfold stableCF
    rw [neg_mul_I_cpow_of_neg h' α, neg_mul_I_cpow_of_pos h α, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, neg_neg]
    congr 3
    push_cast; ring

lemma cos_pi_mul_div_two_neg {α : ℝ} (hα : 1 < α ∧ α ≤ 2) :
    Real.cos (Real.pi * α / 2) < 0 := by
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

lemma continuous_stableCF {α : ℝ} (hα : 0 < α) : Continuous (stableCF α) := by
  refine continuous_iff_continuousAt.2 fun θ => ?_
  have h1 : ContinuousAt (fun w : ℂ => w ^ (α : ℂ)) (-((θ : ℂ) * I)) :=
    continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by simpa using hα)
  have h2 : ContinuousAt (fun θ : ℝ => -((θ : ℂ) * I)) θ := by fun_prop
  have h3 : ContinuousAt (fun θ : ℝ => (-((θ : ℂ) * I)) ^ (α : ℂ)) θ :=
    ContinuousAt.comp (f := fun θ : ℝ => -((θ : ℂ) * I)) (g := fun w : ℂ => w ^ (α : ℂ)) h1 h2
  exact h3.cexp


section LimitLaw

variable {ν : Measure ℝ} {α : ℝ}

lemma integrable_exp_neg_mul_of_laplace
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α))
    {lam : ℝ} (hlam : 0 < lam) : Integrable (fun y => Real.exp (-lam * y)) ν := by
  by_contra h
  have := hL lam hlam
  rw [integral_undef h] at this
  exact (Real.exp_pos _).ne' this.symm

lemma Iio_subset_interior_integrableExpSet
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α)) :
    Iio (0 : ℝ) ⊆ interior (integrableExpSet id ν) := by
  apply interior_maximal _ isOpen_Iio
  intro t ht
  have := integrable_exp_neg_mul_of_laplace hL (lam := -t) (by simpa using ht)
  simpa [integrableExpSet] using this

lemma complexMGF_eq_of_re_neg
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α))
    {z : ℂ} (hz : z.re < 0) :
    complexMGF id ν z = cexp ((-z) ^ (α : ℂ)) := by
  set U : Set ℂ := {z | z.re < 0}
  have hU : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro w hw
    apply analyticAt_complexMGF
    exact Iio_subset_interior_integrableExpSet hL hw
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => cexp ((-w) ^ (α : ℂ))) U := by
    intro w hw
    apply AnalyticAt.cexp
    apply AnalyticAt.cpow (analyticAt_id.neg) analyticAt_const
    rw [mem_slitPlane_iff]; left
    have hw' : w.re < 0 := hw
    change 0 < (-w).re
    rw [neg_re]; linarith
  have hmem : (-1 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ), complexMGF id ν w = cexp ((-w) ^ (α : ℂ)) := by
    have ht : Tendsto (fun n : ℕ => ((-1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (-1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun n : ℕ => (-1 + 1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 (-1 + 0)) := by
          apply Tendsto.add tendsto_const_nhds
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        rw [add_zero] at this
        have := (Complex.continuous_ofReal.tendsto _).comp this
        simpa [Function.comp_def] using this
      · refine Eventually.of_forall fun n => ?_
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h2 : (-1 + 1 / ((n:ℝ) + 2) : ℝ) = -1 := by exact_mod_cast h
        have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    apply ht.frequently
    refine Frequently.of_forall fun n => ?_
    set t : ℝ := -1 + 1 / ((n : ℝ) + 2)
    have htneg : t < 0 := by
      have : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      simp only [t]; linarith
    rw [complexMGF_ofReal]
    simp only [mgf, id_eq]
    have h1 := hL (-t) (by linarith)
    simp only [neg_neg] at h1
    rw [h1]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ -t)]
    simp
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg hU hmem hfreq hz

lemma tendsto_complexMGF_boundary [IsProbabilityMeasure ν]
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α)) (θ : ℝ) :
    Tendsto (fun ε : ℝ => complexMGF id ν (-(ε : ℂ) + θ * I)) (𝓝[>] 0)
      (𝓝 (complexMGF id ν (θ * I))) := by
  unfold complexMGF
  apply tendsto_integral_filter_of_dominated_convergence (fun y => 1 + Real.exp (-1 * y))
  · exact Eventually.of_forall fun ε => (by fun_prop : Continuous fun y : ℝ =>
      cexp ((-(ε : ℂ) + θ * I) * (id y : ℂ))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
    refine Eventually.of_forall fun y => ?_
    rw [Complex.norm_exp]
    have hre : ((-(ε : ℂ) + θ * I) * ((id y : ℝ) : ℂ)).re = -ε * y := by
      simp [mul_re]
    rw [hre]
    rcases le_or_gt 0 y with hy | hy
    · have : Real.exp (-ε * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hε.1])
      linarith [Real.exp_pos (-1 * y)]
    · have : Real.exp (-ε * y) ≤ Real.exp (-1 * y) :=
        Real.exp_le_exp.mpr (by nlinarith [hε.2])
      linarith
  · exact (integrable_const 1).add (integrable_exp_neg_mul_of_laplace hL one_pos)
  · refine Eventually.of_forall fun y => ?_
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous fun ε : ℝ => cexp ((-(ε : ℂ) + θ * I) * ((id y : ℝ) : ℂ)) := by fun_prop
    simpa using this.tendsto 0

/-- **Characteristic function of the limit law.** If `ν` is a probability measure with
`∫ e^{-λ y} dν = e^{λ^α}` for all `λ > 0`, then `E e^{iθY} = exp((-iθ)^α)`. -/
theorem charFun_eq_stableCF [IsProbabilityMeasure ν] (hα : 0 < α)
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α)) (θ : ℝ) :
    charFun ν θ = stableCF α θ := by
  rw [← complexMGF_id_mul_I]
  rcases eq_or_ne θ 0 with rfl | hθ
  · rw [stableCF_zero hα.ne']
    simp [complexMGF]
  · have h1 := tendsto_complexMGF_boundary hL θ
    have h2 : Tendsto (fun ε : ℝ => complexMGF id ν (-(ε : ℂ) + θ * I)) (𝓝[>] 0)
        (𝓝 (stableCF α θ)) := by
      have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, complexMGF id ν (-(ε : ℂ) + θ * I)
          = cexp ((-(-(ε : ℂ) + θ * I)) ^ (α : ℂ)) := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        apply complexMGF_eq_of_re_neg hL
        simp only [add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero]
        simpa using hε
      refine Tendsto.congr' (hev.mono fun ε h => h.symm) ?_
      have hc : ContinuousAt (fun w : ℂ => cexp ((-w) ^ (α : ℂ))) ((θ : ℂ) * I) := by
        apply ContinuousAt.cexp
        apply ContinuousAt.comp (g := fun w : ℂ => w ^ (α : ℂ))
        · apply continuousAt_cpow_const
          rw [mem_slitPlane_iff]; right
          simpa using hθ
        · exact continuousAt_neg
      have hz : Tendsto (fun ε : ℝ => -(ε : ℂ) + θ * I) (𝓝[>] 0) (𝓝 ((θ : ℂ) * I)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        have : Continuous fun ε : ℝ => -(ε : ℂ) + θ * I := by fun_prop
        simpa using this.tendsto 0
      exact hc.tendsto.comp hz
    exact tendsto_nhds_unique h1 h2

end LimitLaw


lemma integrable_stableCF {α : ℝ} (hα : 1 < α ∧ α ≤ 2) : Integrable (stableCF α) := by
  have hc : 0 < -Real.cos (Real.pi * α / 2) := neg_pos.2 (cos_pi_mul_div_two_neg hα)
  have h := integrable_rpow_abs_mul_exp_neg (s := 0) (p := α) (by norm_num) (by linarith) hc
  refine h.mono' (continuous_stableCF (by linarith)).aestronglyMeasurable
    (Eventually.of_forall fun θ => ?_)
  rw [norm_stableCF (by linarith)]
  simp

lemma integrable_abs_mul_norm_stableCF {α : ℝ} (hα : 1 < α ∧ α ≤ 2) :
    Integrable (fun θ : ℝ => |θ| * ‖stableCF α θ‖) := by
  have hc : 0 < -Real.cos (Real.pi * α / 2) := neg_pos.2 (cos_pi_mul_div_two_neg hα)
  have h := integrable_rpow_abs_mul_exp_neg (s := 1) (p := α) (by norm_num) (by linarith) hc
  refine h.congr (Eventually.of_forall fun θ => ?_)
  simp only [Real.rpow_one]
  rw [norm_stableCF (by linarith)]
  simp

/-- **Uniqueness of the limit law**: a probability measure on `ℝ` is determined by the
Laplace identity `∫ e^{-λy} dν = e^{λ^α}` (`λ > 0`). -/
theorem limitLaw_unique {α : ℝ} (hα : 0 < α) {ν₁ ν₂ : Measure ℝ} [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂]
    (h₁ : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν₁ = Real.exp (lam ^ α))
    (h₂ : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν₂ = Real.exp (lam ^ α)) :
    ν₁ = ν₂ := by
  apply Measure.ext_of_charFun
  funext θ
  rw [charFun_eq_stableCF hα h₁, charFun_eq_stableCF hα h₂]

end PoissonDeclumping.Stable

/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.LocalLimit
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion

/-!
# `d_α` is the density of `Y_α` (Stage 1, completed)

Source line 864 ("`d_α` is the density of `Y_α`"). The function
`PoissonDeclumping.Stable.stableDensity α` is defined by Fourier inversion of
`exp((-iθ)^α)`; here we prove that it is indeed the density of the limit law:

* `PoissonDeclumping.Stable.stableDensity_nonneg`: `d_α ≥ 0` (from the local limit theorem);
* `PoissonDeclumping.Stable.integral_stableDensity_mul_gaussian_le`:
  `∫ d_α(x) e^{-bx²} dx ≤ 1` (Fubini and the Gaussian Fourier transform);
* `PoissonDeclumping.Stable.integrable_stableDensity`: `d_α ∈ L¹` (monotone convergence);
* `PoissonDeclumping.Stable.charFun_withDensity_stableDensity`: the characteristic function of
  `d_α(x) dx` is `exp((-iθ)^α)` (mathlib's Fourier inversion theorem);
* `PoissonDeclumping.Stable.limitLaw_eq_withDensity`: `ν = d_α(x) dx`;
* `PoissonDeclumping.Stable.integral_stableDensity`: `∫ d_α = 1`.

The hypothesis `StableDomain μ α a` is used only through `d_α ≥ 0` (a property of `α` alone,
obtained here from the local limit theorem of any walk in the domain).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology FourierTransform

namespace PoissonDeclumping.Stable

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

lemma norm_stableCF_le_one (hα : 1 < α ∧ α ≤ 2) (θ : ℝ) : ‖stableCF α θ‖ ≤ 1 := by
  rw [norm_stableCF (by linarith), Real.exp_le_one_iff]
  have := cos_pi_mul_div_two_neg hα
  have : 0 ≤ |θ| ^ α := by positivity
  nlinarith

/-- `d_α ≥ 0` (a consequence of the local limit theorem: `d · d_α` is a limit of `a_n
  P(S_n=k_n)`). -/
theorem stableDensity_nonneg (h : StableDomain μ α a) (x : ℝ) : 0 ≤ stableDensity α x := by
  have hα := h.alpha_mem
  have hd0 : (0 : ℝ) < latticeSpan μ := by exact_mod_cast latticeSpan_pos h.critical h.nondegenerate
  set d : ℝ := (latticeSpan μ : ℝ)
  set K : ℝ := (1 / (2 * Real.pi)) * ∫ θ : ℝ, |θ| * ‖stableCF α θ‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  by_contra hneg
  push Not at hneg
  set ε : ℝ := -stableDensity α x with hεdef
  have hε : 0 < ε := by linarith
  obtain ⟨N, hN⟩ := localLimit h (show 0 < d * ε / 2 by positivity)
  obtain ⟨n, hn⟩ := ((tendsto_atTop h).eventually_gt_atTop (2 * K * d / ε)).and
    (eventually_ge_atTop (max N 1)) |>.exists
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn.2
  have han := h.pos n hn1
  set j : ℤ := ⌊(x * a n + n) / d⌋ with hj
  set k : ℤ := -n + (latticeSpan μ : ℤ) * j with hk
  have hkd : (latticeSpan μ : ℤ) ∣ k + n := ⟨j, by rw [hk]; ring⟩
  have hfl1 : (j : ℝ) ≤ (x * a n + n) / d := Int.floor_le _
  have hfl2 : (x * a n + n) / d < j + 1 := Int.lt_floor_add_one _
  have hkR : (k : ℝ) = -n + d * j := by rw [hk]; push_cast; ring
  have hk1 : (k : ℝ) ≤ x * a n := by
    rw [hkR]; rw [le_div_iff₀ hd0] at hfl1; linarith
  have hk2 : x * a n < k + d := by
    rw [hkR]; rw [div_lt_iff₀ hd0] at hfl2; linarith
  have hdist : |x - k / a n| ≤ d / a n := by
    have : x - k / a n = (x * a n - k) / a n := by field_simp
    rw [this, abs_div, abs_of_pos han, div_le_div_iff_of_pos_right han, abs_le]
    constructor <;> linarith
  have h1 := abs_le.1 (hN n (le_trans (le_max_left _ _) hn.2) k hkd)
  have hP : 0 ≤ walkProb μ n k := by rw [walkProb_coe_nat]; exact measureReal_nonneg
  have h2 : -ε / 2 ≤ stableDensity α (k / a n) := by
    have : -(d * ε / 2) ≤ d * stableDensity α (k / a n) := by nlinarith
    by_contra hc; push Not at hc; nlinarith
  have h3 := abs_le.1 (abs_stableDensity_sub_le hα x (k / a n))
  have h4 : K * |x - k / a n| < ε / 2 := by
    calc K * |x - k / a n| ≤ K * (d / a n) := by gcongr
      _ < ε / 2 := by
          rw [mul_div_assoc', div_lt_iff₀ han]
          have := hn.1
          rw [div_lt_iff₀ hε] at this
          nlinarith
  linarith [h3.1]


lemma integral_cexp_mul_gaussian {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    ∫ x : ℝ, cexp (-((θ : ℂ) * x * I)) * ((Real.exp (-b * x ^ 2) : ℝ) : ℂ) =
      ((Real.sqrt (Real.pi / b) : ℝ) : ℂ) * ((Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (b : ℂ)) (by simpa using hb) (-(θ : ℂ))
  have e1 : ∀ x : ℝ, cexp (-((θ : ℂ) * x * I)) * ((Real.exp (-b * x ^ 2) : ℝ) : ℂ) =
      cexp (I * -(θ : ℂ) * x) * cexp (-(b : ℂ) * x ^ 2) := by
    intro x; rw [Complex.ofReal_exp]; push_cast; ring_nf
  simp_rw [e1, h]
  congr 1
  · rw [show (Real.pi : ℂ) / (b : ℂ) = ((Real.pi / b : ℝ) : ℂ) by push_cast; ring,
      Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  · rw [Complex.ofReal_exp]; push_cast; ring_nf

/-- `∫ d_α(x) e^{-b x²} dx ≤ 1` for every `b > 0` (Fubini and the Gaussian Fourier transform:
the left side is `(1/2π) ∫ exp((-iθ)^α) √(π/b) e^{-θ²/4b} dθ`). -/
theorem integral_stableDensity_mul_gaussian_le (hα : 1 < α ∧ α ≤ 2) {b : ℝ} (hb : 0 < b) :
    ∫ x, stableDensity α x * Real.exp (-b * x ^ 2) ≤ 1 := by
  set g : ℝ → ℝ := fun x => Real.exp (-b * x ^ 2) with hg
  have hgi : Integrable g := integrable_exp_neg_mul_sq hb
  have hcf := integrable_stableCF hα
  set A : ℝ → ℝ → ℂ := fun θ x => stableCF α θ * cexp (-((θ : ℂ) * x * I)) * (g x : ℂ) with hA
  have hAint : Integrable (Function.uncurry A) (volume.prod volume) := by
    have hprod : Integrable (fun z : ℝ × ℝ => ‖stableCF α z.1‖ * g z.2) (volume.prod volume) :=
      hcf.norm.mul_prod hgi
    refine hprod.mono' ?_ (Eventually.of_forall fun z => ?_)
    · apply Continuous.aestronglyMeasurable
      have := continuous_stableCF (α := α) (by linarith)
      simp only [hA, hg]
      fun_prop
    · simp only [Function.uncurry, hA, norm_mul]
      rw [norm_cexp_neg_mul_I' z.1 z.2, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
  have key : ∫ x, stableDensity α x * g x =
      (1 / (2 * Real.pi)) * (∫ θ, ∫ x, A θ x).re := by
    rw [integral_integral_swap hAint]
    have e1 : ∀ x, stableDensity α x * g x =
        (1 / (2 * Real.pi)) * (∫ θ, A θ x).re := by
      intro x
      rw [stableDensity, hA]
      simp only
      rw [integral_mul_const, mul_assoc, mul_comm _ (g x), Complex.re_mul_ofReal]
      ring
    simp_rw [e1]
    rw [integral_const_mul]
    congr 1
    exact integral_re (hAint.integral_prod_right)
  rw [key]
  have e2 : ∀ θ, ∫ x, A θ x = stableCF α θ * (((Real.sqrt (Real.pi / b) : ℝ) : ℂ) *
      ((Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ)) := by
    intro θ
    rw [← integral_cexp_mul_gaussian hb θ, ← integral_const_mul]
    congr 1; funext x; simp only [hA, hg]; ring
  simp_rw [e2]
  have hgauss : ∫ θ : ℝ, Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) = 2 * Real.pi := by
    rw [integral_const_mul]
    have : ∀ θ : ℝ, Real.exp (-θ ^ 2 / (4 * b)) = Real.exp (-(1 / (4 * b)) * θ ^ 2) := by
      intro θ; congr 1; field_simp
    simp_rw [this]
    rw [integral_gaussian, ← Real.sqrt_mul (by positivity)]
    rw [show Real.pi / b * (Real.pi / (1 / (4 * b))) = (2 * Real.pi) ^ 2 by field_simp; ring,
      Real.sqrt_sq (by positivity)]
  calc (1 / (2 * Real.pi)) * (∫ θ, stableCF α θ * (((Real.sqrt (Real.pi / b) : ℝ) : ℂ) *
        ((Real.exp (-θ ^ 2 / (4 * b)) : ℝ) : ℂ))).re
      ≤ (1 / (2 * Real.pi)) * ∫ θ : ℝ, Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)) := by
        gcongr
        refine (Complex.re_le_norm _).trans ((norm_integral_le_integral_norm _).trans ?_)
        apply integral_mono_of_nonneg (Eventually.of_forall fun θ => norm_nonneg _)
        · exact (integrable_exp_neg_mul_sq (b := 1 / (4 * b)) (by positivity)).const_mul _
            |>.congr (Eventually.of_forall fun θ => by simp only; congr 2; field_simp)
        · refine Eventually.of_forall fun θ => ?_
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _)]
          have := norm_stableCF_le_one hα θ
          calc ‖stableCF α θ‖ * (Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b)))
              ≤ 1 * (Real.sqrt (Real.pi / b) * Real.exp (-θ ^ 2 / (4 * b))) := by gcongr
            _ = _ := one_mul _
    _ = 1 := by rw [hgauss]; field_simp


/-- `d_α` is integrable (with `∫ d_α ≤ 1` from the Gaussian bound and monotone convergence). -/
theorem integrable_stableDensity (h : StableDomain μ α a) : Integrable (stableDensity α) := by
  have hα := h.alpha_mem
  have hnn := stableDensity_nonneg h
  have hcont := continuous_stableDensity hα
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
  set f : ℕ → ℝ → ENNReal := fun j x =>
    ENNReal.ofReal (stableDensity α x * Real.exp (-(1 / ((j : ℝ) + 1)) * x ^ 2)) with hf
  have hmeas : ∀ j, AEMeasurable (f j) := fun j => by
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    exact (hcont.mul (by fun_prop)).measurable
  have hmono : ∀ᵐ x, Monotone fun j => f j x := by
    refine Eventually.of_forall fun x j k hjk => ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (hnn x)
    apply Real.exp_le_exp.2
    have : 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (j : ℝ) ≤ k := by exact_mod_cast hjk
      linarith
    nlinarith [sq_nonneg x]
  have hlim : ∀ᵐ x, Tendsto (fun j => f j x) atTop
      (𝓝 (ENNReal.ofReal (stableDensity α x))) := by
    refine Eventually.of_forall fun x => ?_
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun j : ℕ => Real.exp (-(1 / ((j : ℝ) + 1)) * x ^ 2)) atTop
        (𝓝 (Real.exp (-0 * x ^ 2))) :=
      ((Real.continuous_exp.tendsto _).comp ((h1.neg).mul_const _))
    rw [neg_zero, zero_mul, Real.exp_zero] at h2
    have := h2.const_mul (stableDensity α x)
    rwa [mul_one] at this
  have hT := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  have hle : ∀ j, ∫⁻ x, f j x ≤ 1 := by
    intro j
    have hint : Integrable (fun x => stableDensity α x * Real.exp (-(1 / ((j : ℝ) + 1)) * x ^ 2))
      := by
      obtain ⟨M, -, hM⟩ := exists_stableDensity_le (α := α)
      exact (integrable_exp_neg_mul_sq (b := 1 / ((j : ℝ) + 1)) (by positivity)).bdd_mul
        hcont.aestronglyMeasurable (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hM x)
    rw [hf, ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => mul_nonneg (hnn x) (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_one.2 (integral_stableDensity_mul_gaussian_le hα (by positivity))
  exact lt_of_le_of_lt (le_of_tendsto' hT hle) ENNReal.one_lt_top

lemma integral_stableCF_mul_cexp_real (hα : 1 < α ∧ α ≤ 2) (x : ℝ) :
    ((∫ θ : ℝ, stableCF α θ * cexp (-(θ * x * I))).re : ℂ) =
      ∫ θ : ℝ, stableCF α θ * cexp (-(θ * x * I)) := by
  rw [← Complex.conj_eq_iff_re, ← integral_conj]
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1; funext θ
  rw [stableCF_neg (by linarith) θ, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- The Fourier transform (mathlib normalization `𝓕 g(x) = ∫ e^{-2πiξx} g(ξ) dξ`) of the
rescaled characteristic function `ξ ↦ exp((-2πiξ)^α)` is `d_α`. -/
theorem fourier_stableCF_scaled (hα : 1 < α ∧ α ≤ 2) :
    𝓕 (fun ξ : ℝ => stableCF α (2 * Real.pi * ξ)) = fun x => (stableDensity α x : ℂ) := by
  funext x
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e1 : ∀ ξ : ℝ, cexp (((-2 * Real.pi * ξ * x : ℝ) : ℂ) * I) • stableCF α (2 * Real.pi * ξ) =
      (fun θ : ℝ => stableCF α θ * cexp (-(θ * x * I))) (2 * Real.pi * ξ) := by
    intro ξ; simp only [smul_eq_mul]; rw [mul_comm]; congr 2; push_cast; ring
  simp_rw [e1]
  have h3 := Measure.integral_comp_mul_left
    (fun θ : ℝ => stableCF α θ * cexp (-(θ * x * I))) (2 * Real.pi)
  rw [h3, ← integral_stableCF_mul_cexp_real hα x, stableDensity,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), Complex.real_smul]
  push_cast; ring

/-- `charFun` of the measure `d_α(x) dx` is `exp((-iθ)^α)`. -/
theorem charFun_withDensity_stableDensity (h : StableDomain μ α a) (t : ℝ) :
    charFun (volume.withDensity fun x => ENNReal.ofReal (stableDensity α x)) t =
      stableCF α t := by
  have hα := h.alpha_mem
  have hnn := stableDensity_nonneg h
  set f : ℝ → ℂ := fun ξ => stableCF α (2 * Real.pi * ξ) with hf
  have hfc : Continuous f := (continuous_stableCF (by linarith)).comp (by fun_prop)
  have hfi : Integrable f := (integrable_stableCF hα).comp_mul_left' (by positivity)
  have hFf : 𝓕 f = fun x => (stableDensity α x : ℂ) := fourier_stableCF_scaled hα
  have hFi : Integrable (𝓕 f) := by rw [hFf]; exact (integrable_stableDensity h).ofReal
  have hinv := hfc.fourierInv_fourier_eq hfi hFi
  rw [hFf] at hinv
  have h2 := congrFun hinv (t / (2 * Real.pi))
  rw [Real.fourierInv_eq'] at h2
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (stableDensity α x))
    (ENNReal.measurable_ofReal.comp (continuous_stableDensity hα).measurable)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [hf] at h2
  rw [show 2 * Real.pi * (t / (2 * Real.pi)) = t by field_simp] at h2
  rw [← h2]
  congr 1; funext v
  rw [ENNReal.toReal_ofReal (hnn v), Complex.real_smul, smul_eq_mul, mul_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast; field_simp

/-- **`d_α` is the density of `Y_α`** (source line 864): under `(H_α)`, the limit law `ν` (any
probability measure with `∫ e^{-λy} dν = e^{λ^α}`) is `d_α(x) dx`. -/
theorem limitLaw_eq_withDensity (h : StableDomain μ α a) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α)) :
    ν = volume.withDensity fun x => ENNReal.ofReal (stableDensity α x) := by
  have hα := h.alpha_mem
  have : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (stableDensity α x)) :=
    isFiniteMeasure_withDensity_ofReal (integrable_stableDensity h).hasFiniteIntegral
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_eq_stableCF (by linarith) hL, charFun_withDensity_stableDensity h]

/-- `∫ d_α = 1`. -/
theorem integral_stableDensity (h : StableDomain μ α a) : ∫ x, stableDensity α x = 1 := by
  obtain ⟨ν, hν, hL, -⟩ := h.converges
  have h1 := limitLaw_eq_withDensity h hL
  have h2 : (volume.withDensity fun x => ENNReal.ofReal (stableDensity α x)) Set.univ = 1 := by
    rw [← h1]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h2
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (stableDensity_nonneg h))
    (continuous_stableDensity h.alpha_mem).aestronglyMeasurable, h2, ENNReal.toReal_one]

end PoissonDeclumping.Stable

/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.LimitLaw

/-!
# The stable density `d_α` (Stage 1, continued)

Source lines 862–864 and the uses of `d_α` at lines 1029–1041, 1640–1647, 1987–1994.
The density of `Y_α` is defined by Fourier inversion of the (integrable) characteristic
function `exp((-iθ)^α)` from `PoissonDeclumping.Stable.LimitLaw`:

  `d_α(x) = (1/2π) Re ∫ exp((-iθ)^α) e^{-iθx} dθ`.

We prove that `d_α` is bounded and Lipschitz (hence continuous and uniformly continuous),
and compute its value at zero, `d_α(0) = Γ(1 + 1/α) sin(π/α) / π > 0`, using the complex
Gamma integral of `PoissonDeclumping.Stable.Analytic` (this replaces the contour rotation).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology NNReal

namespace PoissonDeclumping.Stable

/-- The density `d_α` of the limit law `Y_α`, defined by Fourier inversion of its
characteristic function `exp((-iθ)^α)`. -/
noncomputable def stableDensity (α x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ θ : ℝ, stableCF α θ * cexp (-(θ * x * I))).re

variable {α : ℝ}

lemma norm_cexp_neg_mul_I (θ x : ℝ) : ‖cexp (-((θ : ℂ) * x * I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma integrable_stableCF_mul_cexp (hα : 1 < α ∧ α ≤ 2) (x : ℝ) :
    Integrable (fun θ : ℝ => stableCF α θ * cexp (-(θ * x * I))) := by
  refine (integrable_stableCF hα).mul_bdd (c := 1) (by fun_prop) ?_
  exact Eventually.of_forall fun θ => (norm_cexp_neg_mul_I θ x).le

/-- `d_α` is bounded. -/
theorem abs_stableDensity_le (x : ℝ) :
    |stableDensity α x| ≤ (1 / (2 * Real.pi)) * ∫ θ : ℝ, ‖stableCF α θ‖ := by
  rw [stableDensity, abs_mul, abs_of_pos (by positivity)]
  gcongr
  calc |(∫ θ : ℝ, stableCF α θ * cexp (-(θ * x * I))).re|
      ≤ ‖∫ θ : ℝ, stableCF α θ * cexp (-(θ * x * I))‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ θ : ℝ, ‖stableCF α θ * cexp (-(θ * x * I))‖ := norm_integral_le_integral_norm _
    _ = ∫ θ : ℝ, ‖stableCF α θ‖ := by
        congr 1; funext θ; rw [norm_mul, norm_cexp_neg_mul_I, mul_one]

lemma norm_cexp_sub_cexp_le (θ x y : ℝ) :
    ‖cexp (-((θ : ℂ) * x * I)) - cexp (-((θ : ℂ) * y * I))‖ ≤ |θ| * |x - y| := by
  have h : cexp (-((θ : ℂ) * x * I)) - cexp (-((θ : ℂ) * y * I)) =
      cexp (-((θ : ℂ) * y * I)) * (cexp (I * ((-(θ * (x - y)) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast; ring
  rw [h, norm_mul, norm_cexp_neg_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul]

/-- `d_α` is Lipschitz, with constant `(1/2π) ∫ |θ| |exp((-iθ)^α)| dθ`. -/
theorem abs_stableDensity_sub_le (hα : 1 < α ∧ α ≤ 2) (x y : ℝ) :
    |stableDensity α x - stableDensity α y| ≤
      ((1 / (2 * Real.pi)) * ∫ θ : ℝ, |θ| * ‖stableCF α θ‖) * |x - y| := by
  rw [stableDensity, stableDensity, ← mul_sub, ← Complex.sub_re,
    ← integral_sub (integrable_stableCF_mul_cexp hα x) (integrable_stableCF_mul_cexp hα y),
    abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)), mul_assoc]
  gcongr
  calc |(∫ θ : ℝ, (stableCF α θ * cexp (-(θ * x * I)) - stableCF α θ * cexp (-(θ * y * I)))).re|
      ≤ ‖∫ θ : ℝ, (stableCF α θ * cexp (-(θ * x * I)) - stableCF α θ * cexp (-(θ * y * I)))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∫ θ : ℝ, ‖stableCF α θ * cexp (-(θ * x * I)) - stableCF α θ * cexp (-(θ * y * I))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ θ : ℝ, |θ| * ‖stableCF α θ‖ * |x - y| := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun θ => norm_nonneg _)
          ((integrable_abs_mul_norm_stableCF hα).mul_const _)
        refine Eventually.of_forall fun θ => ?_
        simp only
        rw [← mul_sub, norm_mul]
        calc ‖stableCF α θ‖ * ‖cexp (-(θ * x * I)) - cexp (-(θ * y * I))‖
            ≤ ‖stableCF α θ‖ * (|θ| * |x - y|) := by
              gcongr; exact norm_cexp_sub_cexp_le θ x y
          _ = |θ| * ‖stableCF α θ‖ * |x - y| := by ring
    _ = (∫ θ : ℝ, |θ| * ‖stableCF α θ‖) * |x - y| := integral_mul_const _ _

theorem lipschitzWith_stableDensity (hα : 1 < α ∧ α ≤ 2) :
    LipschitzWith ((1 / (2 * Real.pi)) * ∫ θ : ℝ, |θ| * ‖stableCF α θ‖).toNNReal
      (stableDensity α) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  exact abs_stableDensity_sub_le hα x y

/-- `d_α` is uniformly continuous. -/
theorem uniformContinuous_stableDensity (hα : 1 < α ∧ α ≤ 2) :
    UniformContinuous (stableDensity α) :=
  (lipschitzWith_stableDensity hα).uniformContinuous

/-- `d_α` is continuous. -/
theorem continuous_stableDensity (hα : 1 < α ∧ α ≤ 2) : Continuous (stableDensity α) :=
  (lipschitzWith_stableDensity hα).continuous

/-- `d_α` is bounded. -/
theorem exists_stableDensity_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |stableDensity α x| ≤ M :=
  ⟨_, (abs_nonneg _).trans (abs_stableDensity_le 0), abs_stableDensity_le⟩

/-- The value of `d_α` at zero: `d_α(0) = Γ(1 + 1/α) sin(π/α) / π`. -/
theorem stableDensity_zero (hα : 1 < α ∧ α ≤ 2) :
    stableDensity α 0 = Real.Gamma (1 / α + 1) * Real.sin (Real.pi / α) / Real.pi := by
  have hα0 : 0 < α := by linarith
  have hint := integrable_stableCF hα
  -- the half-line integral
  set r : ℂ := -cexp (((-(Real.pi * α / 2)) : ℝ) * I) with hr
  have hrre : 0 < r.re := by
    rw [hr, neg_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    linarith [cos_pi_mul_div_two_neg hα]
  have hJ : ∫ θ in Ioi (0 : ℝ), stableCF α θ =
      (Real.Gamma (1 / α + 1) : ℂ) * r ^ (-(1 / α : ℝ) : ℂ) := by
    rw [← integral_cexp_neg_mul_rpow hα0 hrre]
    refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
    simp only [stableCF]
    rw [neg_mul_I_cpow_of_pos hθ, hr]
    ring_nf
  -- `r = exp(i φ)` with `φ = π - πα/2 ∈ [0, π/2)`
  set φ : ℝ := Real.pi - Real.pi * α / 2 with hφ
  have hr' : r = cexp ((φ : ℂ) * I) := by
    rw [hr, hφ]
    rw [show -cexp (((-(Real.pi * α / 2)) : ℝ) * I) =
        cexp ((Real.pi : ℂ) * I) * cexp (((-(Real.pi * α / 2)) : ℝ) * I) by
      rw [Complex.exp_pi_mul_I]; ring, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hφ1 : -Real.pi < φ := by nlinarith [Real.pi_pos]
  have hφ2 : φ ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hpow : (r ^ (-(1 / α : ℝ) : ℂ)).re = Real.cos (φ / α) := by
    rw [hr', cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp (by simpa using hφ1)
      (by simpa using hφ2)]
    rw [show (φ : ℂ) * I * (-(1 / α : ℝ) : ℂ) = ((-(φ / α)) : ℝ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  -- the whole-line integral
  have hfull : (∫ θ : ℝ, stableCF α θ).re = 2 * Real.Gamma (1 / α + 1) * Real.cos (φ / α) := by
    have hneg : ∫ θ in Iic (0 : ℝ), stableCF α θ =
        (starRingEnd ℂ) (∫ θ in Ioi (0 : ℝ), stableCF α θ) := by
      have h := integral_comp_neg_Ioi (0 : ℝ) (stableCF α)
      rw [neg_zero] at h
      rw [← integral_conj, ← h]
      refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
      exact stableCF_neg hα0.ne' θ
    rw [← integral_add_compl measurableSet_Ioi hint, compl_Ioi]
    rw [hneg, add_re, conj_re, hJ, re_ofReal_mul, hpow]
    ring
  have hsin : Real.cos (φ / α) = Real.sin (Real.pi / α) := by
    rw [hφ, show (Real.pi - Real.pi * α / 2) / α = Real.pi / α - Real.pi / 2 by
      field_simp, Real.cos_sub_pi_div_two]
  rw [stableDensity]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [hfull, hsin]
  field_simp

/-- **Positivity of the stable density at zero**, `d_α(0) > 0`. -/
theorem stableDensity_zero_pos (hα : 1 < α ∧ α ≤ 2) : 0 < stableDensity α 0 := by
  rw [stableDensity_zero hα]
  have hα0 : 0 < α := by linarith
  apply div_pos _ Real.pi_pos
  apply mul_pos (Real.Gamma_pos_of_pos (by positivity))
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  rw [div_lt_iff₀ hα0]
  nlinarith [Real.pi_pos]

end PoissonDeclumping.Stable

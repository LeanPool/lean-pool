/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Walk
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Characteristic function of the walk and Fourier inversion on `ℤ`

For the step law `X = K - 1` (`PoissonDeclumping.stepLaw`) and the walk law
`PoissonDeclumping.walkLaw μ n` (an `n`-fold convolution, source lines 174–181, 842–845):

* `PoissonDeclumping.Stable.walkCF_eq_pow`: `E e^{iθ S_n} = φ(θ)^n` with `φ = stepCF μ`;
* `PoissonDeclumping.Stable.charFun_walkLaw_map_div`: the characteristic function of `S_n / c`
  is `φ(t/c)^n`;
* `PoissonDeclumping.Stable.walkLaw_real_singleton`: Fourier inversion on `ℤ`,
  `P(S_n = k) = (1/2π) ∫_{-π}^{π} φ(θ)^n e^{-ikθ} dθ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace PoissonDeclumping.Stable

variable (μ : PMF ℕ)

instance isProbabilityMeasure_stepLaw : IsProbabilityMeasure (stepLaw μ) := by
  unfold stepLaw
  constructor
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

instance isProbabilityMeasure_walkLaw (n : ℕ) : IsProbabilityMeasure (walkLaw μ n) := by
  induction n with
  | zero => simp only [walkLaw]; infer_instance
  | succ n ih => simp only [walkLaw]; infer_instance

/-- The characteristic function `φ(θ) = E e^{iθX}` of one step. -/
noncomputable def stepCF (θ : ℝ) : ℂ := ∫ z, cexp (θ * z * I) ∂(stepLaw μ)

/-- The characteristic function `E e^{iθ S_n}` of the walk at time `n`. -/
noncomputable def walkCF (n : ℕ) (θ : ℝ) : ℂ := ∫ z, cexp (θ * z * I) ∂(walkLaw μ n)

lemma integral_conv_int {W P : Measure ℤ} [IsFiniteMeasure W] [IsFiniteMeasure P] (F : ℤ → ℂ) :
    ∫ z, F z ∂(W ∗ P) = ∫ p, F (p.1 + p.2) ∂(W.prod P) := by
  rw [Measure.conv, integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]

theorem walkCF_eq_pow (n : ℕ) (θ : ℝ) : walkCF μ n θ = stepCF μ θ ^ n := by
  induction n with
  | zero =>
    change ∫ z, _ ∂(Measure.dirac 0) = _
    rw [integral_dirac]; simp
  | succ n ih =>
    rw [pow_succ, ← ih, walkCF, walkLaw, integral_conv_int]
    have : ∀ p : ℤ × ℤ, cexp (θ * ((p.1 + p.2 : ℤ) : ℂ) * I) =
        cexp (θ * (p.1 : ℂ) * I) * cexp (θ * (p.2 : ℂ) * I) := by
      intro p; rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [this]
    rw [integral_prod_mul (fun x : ℤ => cexp (θ * (x : ℂ) * I))
      (fun y : ℤ => cexp (θ * (y : ℂ) * I))]
    rfl

lemma norm_walkCF_le (n : ℕ) (θ : ℝ) : ‖walkCF μ n θ‖ ≤ 1 := by
  refine (norm_integral_le_integral_norm _).trans ?_
  simp [Complex.norm_exp]

lemma norm_stepCF_le (θ : ℝ) : ‖stepCF μ θ‖ ≤ 1 := by
  refine (norm_integral_le_integral_norm _).trans ?_
  simp [Complex.norm_exp]

lemma continuous_stepCF : Continuous (stepCF μ) := by
  apply continuous_of_dominated (bound := fun _ => 1)
  · exact fun θ => (measurable_of_countable _).aestronglyMeasurable
  · exact fun θ => Eventually.of_forall fun z => by simp [Complex.norm_exp]
  · exact integrable_const 1
  · exact Eventually.of_forall fun z => by fun_prop

/-- The characteristic function of `S_n / c` is `φ(θ/c)^n`. -/
theorem charFun_walkLaw_map_div (n : ℕ) (c t : ℝ) :
    charFun ((walkLaw μ n).map (fun z : ℤ => (z : ℝ) / c)) t = stepCF μ (t / c) ^ n := by
  rw [← walkCF_eq_pow, charFun_apply, integral_map (measurable_of_countable _).aemeasurable
    (by fun_prop), walkCF]
  congr 1; funext z
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · field_simp

lemma intervalIntegral_cexp_int_mul_I (m : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, cexp (θ * m * I) = if m = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 :=
      by
  split_ifs with hm
  · subst hm; simp; ring
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) I_ne_zero
    have : (fun θ : ℝ => cexp (θ * m * I)) = fun θ : ℝ => cexp ((m * I) * θ) := by
      funext θ; ring_nf
    rw [this, integral_exp_mul_complex hc]
    have h1 : cexp (m * I * (Real.pi : ℂ)) = cexp (m * I * ((-Real.pi : ℝ) : ℂ)) := by
      have h2 : m * I * (Real.pi : ℂ) = m * I * ((-Real.pi : ℝ) : ℂ) + (m : ℂ) * (2 * Real.pi * I)
        := by
        push_cast; ring
      rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h1, sub_self, zero_div]

/-- **Fourier inversion on `ℤ`**: `P(S_n = k) = (1/2π) ∫_{-π}^{π} φ(θ)^n e^{-ikθ} dθ`. -/
theorem walkLaw_real_singleton (n : ℕ) (k : ℤ) :
    (((walkLaw μ n).real {k} : ℝ) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, stepCF μ θ ^ n * cexp (-(θ * k * I)) := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hswap : ∫ θ in Ioc (-Real.pi) Real.pi, stepCF μ θ ^ n * cexp (-(θ * k * I)) =
      ∫ z, ∫ θ in Ioc (-Real.pi) Real.pi, cexp (θ * ((z - k : ℤ) : ℝ) * I) ∂volume
        ∂(walkLaw μ n) := by
    have h1 : ∀ θ : ℝ, stepCF μ θ ^ n * cexp (-(θ * k * I)) =
        ∫ z, cexp (θ * ((z - k : ℤ) : ℝ) * I) ∂(walkLaw μ n) := by
      intro θ
      rw [← walkCF_eq_pow, walkCF, ← integral_mul_const]
      congr 1; funext z
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [h1]
    apply integral_integral_swap
    apply Integrable.of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_left
      intro z
      fun_prop
    · refine Eventually.of_forall fun p => ?_
      obtain ⟨x, y⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [show ((x : ℂ) * (((y - k : ℤ) : ℝ) : ℂ) * I) = ((x * ((y - k : ℤ) : ℝ) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [hswap]
  have h2 : ∀ z : ℤ, ∫ θ in Ioc (-Real.pi) Real.pi, cexp (θ * ((z - k : ℤ) : ℝ) * I) =
      ({k} : Set ℤ).indicator (fun _ => ((2 * Real.pi : ℝ) : ℂ)) z := by
    intro z
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    have := intervalIntegral_cexp_int_mul_I (z - k)
    push_cast at this ⊢
    rw [this]
    by_cases hz : z = k
    · simp [hz]
    · simp [hz, sub_eq_zero]
  simp_rw [h2]
  rw [integral_indicator_const _ (measurableSet_singleton k)]
  rw [Complex.real_smul]
  push_cast
  field_simp

end PoissonDeclumping.Stable

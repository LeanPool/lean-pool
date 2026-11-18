/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Multilinear
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Norm moments and polynomial integrability from exponential moments

A finite measure with one positive norm exponential moment has every norm
moment. All norm exponential moments make polynomially bounded measurable
functions integrable. Rank-one moment products use the shared multilinear
norm bound; finite dimension is not required. Conversely, for an additive Haar
measure on a finite-dimensional real normed space, `‖x‖^k e^{-a‖x‖}` is
integrable for every `a > 0` (`integrable_norm_pow_mul_exp_neg_mul_norm`), by polar
coordinates and the one-dimensional integral `∫_{(0, ∞)} r^s e^{-a r}`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FunctionalInequalities.Probability

section NormMoments

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Decreasing the radius preserves norm-exponential integrability. -/
theorem integrable_exp_mul_norm_of_le {μ : Measure E} {r s : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (hs : s ≤ r) :
    Integrable (fun x => Real.exp (s * ‖x‖)) μ := by
  refine hexp.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs (norm_nonneg x))

/-- Norm moments of every order from one positive exponential moment of a finite measure. -/
theorem integrable_norm_pow_of_exp (μ : Measure E) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ d) μ := by
  have hneg : Integrable (fun x : E => Real.exp (-r * ‖x‖)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact
      Real.exp_le_one_iff.2
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hr.le) (norm_nonneg x))
  simpa only [abs_norm] using
    ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul hr.ne' hexp hneg d

end NormMoments

section PolynomialGrowth
universe u
variable {E : Type u} [NormedAddCommGroup E] [MeasurableSpace E]

/-- Polynomially bounded measurable functions are integrable under all norm exponential moments. -/
theorem integrable_of_norm_le_pow {F : Type*} [NormedAddCommGroup F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable g μ := by
    have hpow : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ,
        (1 + t) ^ n ≤ Real.exp ((n : ℝ) * t) := by
      intro t ht n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            (1 + t) ^ n.succ = (1 + t) ^ n * (1 + t) := by
              rw [pow_succ]
            _ ≤ Real.exp ((n : ℝ) * t) * Real.exp t := by
              exact
                mul_le_mul ih (by simpa [add_comm] using Real.add_one_le_exp t)
                  (by linarith) (by positivity)
            _ = Real.exp ((n.succ : ℕ) * t) := by
              rw [← Real.exp_add]
              congr 1
              push_cast
              ring
    have hdom : ∀ x : E, ‖g x‖ ≤ max C 0 * Real.exp ((k : ℝ) * ‖x‖) := by
      intro x
      have hp : (1 + ‖x‖) ^ k ≤ Real.exp ((k : ℝ) * ‖x‖) :=
        hpow ‖x‖ (norm_nonneg x) k
      calc
        ‖g x‖ ≤ C * (1 + ‖x‖) ^ k := hgb x
        _ ≤ max C 0 * (1 + ‖x‖) ^ k := by
          exact
            mul_le_mul_of_nonneg_right (le_max_left C 0)
              (pow_nonneg (by positivity) k)
        _ ≤ max C 0 * Real.exp ((k : ℝ) * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left hp (le_max_right C 0)
    refine ((hexp (k : ℝ)).const_mul (max C 0)).mono' hg
      (ae_of_all _ (fun x => ?_))
    simpa [smul_eq_mul] using hdom x

end PolynomialGrowth

section InnerMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open scoped RealInnerProductSpace

/-- Scalar moment products are integrable under one positive norm exponential moment. -/
theorem integrable_prod_inner_of_exp (μ : Measure E) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ)
    (h : Fin d → E) : Integrable (fun x : E => ∏ j, ⟪x, h j⟫) μ :=
  ((integrable_norm_pow_of_exp μ hr hexp d).mul_const (∏ j, ‖h j‖)).mono' (by fun_prop)
    (ae_of_all _ fun x => Analysis.Tensor.norm_prod_inner_le d h x)

end InnerMoments

section HaarExponentialDecay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `‖x‖^k e^{-a‖x‖}` is integrable for an additive Haar measure and `a > 0`. -/
theorem integrable_norm_pow_mul_exp_neg_mul_norm (m : Measure E) [m.IsAddHaarMeasure] {a : ℝ}
    (ha : 0 < a) (k : ℕ) :
    Integrable (fun x => ‖x‖ ^ k * Real.exp (-(a * ‖x‖))) m := by
  rcases subsingleton_or_nontrivial E with _ | _
  · exact (by fun_prop : Continuous fun x : E => ‖x‖ ^ k * Real.exp (-(a * ‖x‖)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · rw [integrable_fun_norm_addHaar m (f := fun y : ℝ => y ^ k * Real.exp (-(a * y)))]
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (b := a)
      (s := ((Module.finrank ℝ E - 1 + k : ℕ) : ℝ))
      (by linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E - 1 + k)]) one_pos ha).congr_fun
      (fun y _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, Real.rpow_natCast, smul_eq_mul, pow_add, neg_mul]
    ring

end HaarExponentialDecay

end FunctionalInequalities.Probability

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.CurvatureMonotonicity
public import LeanPool.CutoffRigidity.GibbsIntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gaussian tail control and moments of uniformly convex Gibbs measures

The actual C² Hessian lower bound supplies a quadratic supporting bound for
the potential. Gaussian domination then proves integrability of the Gibbs
weight and its squared-norm moment, rather than assuming coercivity or
finite second moments.
-/

public section

namespace CutoffRigidity

open MeasureTheory

/-- Integrating the actual Hessian curvature bound yields the quadratic
supporting bound for a C² potential. -/
theorem potential_quadratic_support_of_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    V 0 + fderiv ℝ V 0 x + ρ / 2 * ‖x‖ ^ 2 ≤ V x := by
  let F : ℝ → ℝ := fun s => V (s • x) - s * fderiv ℝ V 0 x - ρ / 2 * s ^ 2 * ‖x‖ ^ 2
  have hdiff := hV.differentiable (by norm_num)
  have hd (s : ℝ) : HasDerivAt F
      (fderiv ℝ V (s • x) x - fderiv ℝ V 0 x - ρ * s * ‖x‖ ^ 2) s := by
    have hline : HasDerivAt (fun u : ℝ => u • x) x s := by
      simpa using (hasDerivAt_id s).smul_const x
    have hv := (hdiff (s • x)).hasFDerivAt.comp_hasDerivAt s hline
    have hlin := (hasDerivAt_id s).mul_const (fderiv ℝ V 0 x)
    have hquad := (((hasDerivAt_id s).pow 2).const_mul (ρ / 2)).mul_const (‖x‖ ^ 2)
    convert (hv.sub hlin).sub hquad using 1
    · rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
  have hn (s : ℝ) (hs : s ∈ interior (Set.Ici (0 : ℝ))) :
      0 ≤ fderiv ℝ V (s • x) x - fderiv ℝ V 0 x - ρ * s * ‖x‖ ^ 2 := by
    have hsp : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
    have hm := gradient_strongly_monotone_of_hessian_bound hV ρ hHess (s • x) 0
    simp only [sub_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      inner_smul_right, inner_sub_left] at hm
    rw [inner_gradient_left, inner_gradient_left] at hm
    have hh : 0 ≤ s * (fderiv ℝ V (s • x) x - fderiv ℝ V 0 x - ρ * s * ‖x‖ ^ 2) := by
      nlinarith [hm]
    exact (mul_nonneg_iff_of_pos_left hsp).mp hh
  have hmono : MonotoneOn F (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      ((continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn)
      (fun s hs => (hd s).hasDerivWithinAt) hn
  have h := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) (by simp : (1 : ℝ) ∈ Set.Ici 0)
    (by norm_num : (0 : ℝ) ≤ 1)
  simp only [F, zero_smul, one_smul, zero_mul, sub_zero, one_pow, mul_one] at h
  linarith

/-- Absorbing the supporting linear term yields a centered Gaussian tail
bound with an explicit additive constant. -/
theorem potential_gaussian_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    ρ / 4 * ‖x‖ ^ 2 - (‖gradient V 0‖ ^ 2 / ρ - V 0) ≤ V x := by
  have hs := potential_quadratic_support_of_hessian_bound hV ρ hHess x
  have hi : -‖gradient V 0‖ * ‖x‖ ≤ fderiv ℝ V 0 x := by
    rw [← inner_gradient_left]
    have h := real_inner_le_norm (-gradient V 0) x
    simp only [inner_neg_left, norm_neg] at h
    linarith
  have hy : ‖gradient V 0‖ * ‖x‖ ≤ ρ / 4 * ‖x‖ ^ 2 + ‖gradient V 0‖ ^ 2 / ρ := by
    apply (mul_le_mul_iff_left₀ hρ).mp
    field_simp
    nlinarith [sq_nonneg (ρ * ‖x‖ - 2 * ‖gradient V 0‖)]
  linarith

/-- The actual Gibbs density is bounded by an integrable Gaussian profile. -/
theorem gibbs_density_gaussian_domination
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    Real.exp (-V x) ≤ Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0) *
      Real.exp (-(ρ / 4) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := potential_gaussian_lower_bound hV ρ hρ hHess x
  linarith

/-- A radial Gaussian is integrable for the actual Euclidean volume. -/
theorem integrable_exp_neg_mul_norm_sq {ι : Type*} [Fintype ι]
    (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (-c * ‖x‖ ^ 2)) volume := by
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  have hp : Integrable (fun x : ι → ℝ => ∏ i, Real.exp (-c * x i ^ 2)) volume :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hc)
  convert hp using 1
  funext x
  simp only [Function.comp_apply, EuclideanSpace.real_norm_sq_eq,
    Finset.mul_sum, Real.exp_sum]

/-- A quadratic polynomial times a radial Gaussian is integrable. -/
theorem integrable_norm_sq_mul_exp_neg_mul_norm_sq {ι : Type*} [Fintype ι]
    (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2)) volume := by
  have hg := (integrable_exp_neg_mul_norm_sq (ι := ι) (c / 2) (by linarith)).const_mul (2 / c)
  apply hg.mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := Real.mul_exp_neg_le_exp_neg_one (c / 2 * ‖x‖ ^ 2)
  have he : Real.exp (-1 : ℝ) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  have hbound : (c / 2 * ‖x‖ ^ 2) * Real.exp (-(c / 2 * ‖x‖ ^ 2)) ≤ 1 := le_trans h he
  have hmul := mul_le_mul_of_nonneg_right hbound
    (show 0 ≤ (2 / c) * Real.exp (-(c / 2) * ‖x‖ ^ 2) by positivity)
  have heq : (c / 2 * ‖x‖ ^ 2) * Real.exp (-(c / 2 * ‖x‖ ^ 2)) *
      ((2 / c) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) =
      ‖x‖ ^ 2 * Real.exp (-c * ‖x‖ ^ 2) := by
    rw [mul_assoc, mul_left_comm (Real.exp _), ← mul_assoc, ← Real.exp_add]
    have hexp : -(c / 2 * ‖x‖ ^ 2) + -(c / 2) * ‖x‖ ^ 2 = -c * ‖x‖ ^ 2 := by ring
    rw [hexp]
    field_simp
  simpa only [heq, one_mul] using hmul

/-- Uniform convexity proves integrability of the actual Gibbs weight. -/
theorem integrable_gibbs_density_of_hessian_bound {ι : Type*} [Fintype ι]
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Integrable (fun x => Real.exp (-V x)) volume := by
  have hmV : Measurable V := hV.continuous.measurable
  have hg := (integrable_exp_neg_mul_norm_sq (ι := ι) (ρ / 4) (by linarith)).const_mul
    (Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0))
  apply hg.mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact gibbs_density_gaussian_domination hV ρ hρ hHess x

/-- The actual partition integral is finite and strictly positive. -/
theorem gibbs_partition_finite_positive {ι : Type*} [Fintype ι]
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Integrable (fun x => Real.exp (-V x)) volume ∧
      0 < ∫ x, Real.exp (-V x) := by
  have hi := integrable_gibbs_density_of_hessian_bound hV ρ hρ hHess
  exact ⟨hi, integral_exp_pos hi⟩

/-- Uniform convexity also proves the weighted second moment is finite. -/
theorem integrable_gibbs_weighted_second_moment {ι : Type*} [Fintype ι]
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Integrable (fun x => ‖x‖ ^ 2 * Real.exp (-V x)) volume := by
  have hmV : Measurable V := hV.continuous.measurable
  have hg := (integrable_norm_sq_mul_exp_neg_mul_norm_sq (ι := ι) (ρ / 4) (by linarith)).const_mul
    (Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0))
  apply hg.mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ‖x‖ ^ 2 * (Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0) *
        Real.exp (-(ρ / 4) * ‖x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (gibbs_density_gaussian_domination hV ρ hρ hHess x) (sq_nonneg _)
    _ = _ := by ring

/-- The actual Gibbs measure has a square-integrable identity map; no second
moment or normalization assumption is added to the curvature hypotheses. -/
theorem gibbs_memLp_two_id_of_hessian_bound {ι : Type*} [Fintype ι]
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    MemLp (fun x : EuclideanSpace ℝ ι => x) 2 (gibbsMeasure volume V) := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
  rw [integrable_gibbsMeasure_iff volume hV.continuous.measurable]
  simpa only [smul_eq_mul, mul_comm] using integrable_gibbs_weighted_second_moment hV ρ hρ hHess

/-- The additive normalization in the paper produces an actual probability
measure with finite second moment, all from the C² curvature assumption. -/
theorem normalized_gibbs_probability_memLp_two {ι : Type*} [Fintype ι]
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    let Z := ∫ x, Real.exp (-V x)
    IsProbabilityMeasure (gibbsMeasure volume (fun x => V x + Real.log Z)) ∧
      MemLp (fun x : EuclideanSpace ℝ ι => x) 2
        (gibbsMeasure volume (fun x => V x + Real.log Z)) := by
  intro Z
  obtain ⟨hint, hpos⟩ := gibbs_partition_finite_positive hV ρ hρ hHess
  have hZpos : 0 < Z := hpos
  refine ⟨gibbsMeasure_normalize_potential volume V hint hpos, ?_⟩
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
  have hmV : Measurable (fun x => V x + Real.log Z) := hV.continuous.measurable.add_const _
  rw [integrable_gibbsMeasure_iff volume hmV]
  have heq (x : EuclideanSpace ℝ ι) :
      Real.exp (-(V x + Real.log Z)) • ‖x‖ ^ 2 =
        (‖x‖ ^ 2 * Real.exp (-V x)) / Z := by
    rw [smul_eq_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log Z), Real.exp_log hZpos]
    ring
  simp_rw [heq]
  exact (integrable_gibbs_weighted_second_moment hV ρ hρ hHess).div_const Z

end CutoffRigidity

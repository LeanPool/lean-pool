/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSpectralGap
public import LeanPool.CutoffRigidity.GibbsSobolevClassical
public import LeanPool.CutoffRigidity.SmoothPoincare

/-! # The actual Gibbs spectral gap and the source Poincaré inequality

The canonical rate is obtained from the norm of the actual compact
resolvent on mean-zero L². The smooth functional inequality follows from
the closed Sobolev inequality through the proved classical-domain lift.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual canonical Gibbs spectral gap. Its positivity, attainment,
and minimality are proved below from the source curvature assumptions. -/
@[expose] noncomputable def gibbsSpectralGap {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) : ℝ :=
  ‖gibbsMeanZeroResolvent hV hprob‖⁻¹ - 1

theorem gibbsSpectralGap_pos {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    0 < gibbsSpectralGap hV hprob := by
  obtain ⟨_, _, _, _, hpos⟩ := exists_positive_gibbsOperator_eigenvalue hV hprob hd ρ hρ hHess
  exact hpos

/-- Attainment occurs at the precise canonical spectral value. -/
theorem gibbsSpectralGap_hasEigenvector {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ u : gibbsOperatorEigenspace hV hprob (gibbsSpectralGap hV hprob), u ≠ 0 := by
  obtain ⟨_, u, hu, he, _⟩ := exists_positive_gibbsOperator_eigenvalue hV hprob hd ρ hρ hHess
  refine ⟨⟨u, he⟩, ?_⟩
  intro hz
  exact hu (congrArg Subtype.val hz)

/-- The actual L² mean-zero condition is precisely the actual integral
condition, for a real L² function represented in the source measure. -/
theorem toLp_mem_gibbsMeanZeroSpace_iff {V f : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : MemLp f 2 (gibbsMeasure volume V)) :
    hf.toLp f ∈ gibbsMeanZeroSpace hprob ↔ (∫ x, f x ∂gibbsMeasure volume V) = 0 := by
  let := hprob
  rw [gibbsMeanZeroSpace, Submodule.mem_orthogonal_singleton_iff_inner_left, L2.inner_def]
  have heq : (∫ x, inner ℝ (hf.toLp f x) (gibbsConstantLp hprob 1 x)
      ∂gibbsMeasure volume V) = ∫ x, f x ∂gibbsMeasure volume V := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, (memLp_const (1 : ℝ)).coeFn_toLp] with x hx hc
    change (gibbsConstantLp hprob 1 : E → ℝ) x = 1 at hc
    rw [hx, hc, Real.inner_apply, mul_one]
  rw [heq]

/-- The paper's genuine smooth Poincaré inequality at the canonical
attained spectral gap, derived without a Poincaré premise. -/
theorem hasSmoothPoincare_gibbsSpectralGap {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    HasSmoothPoincare (gibbsMeasure volume V) (gibbsSpectralGap hV hprob) := by
  intro f hf hfLp hg hm
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V) :=
    (memLp_two_iff_integrable_sq_norm
      (continuous_gradient_of_c1 (hf2.of_le (by norm_num))).aestronglyMeasurable).mpr hg
  let u := c2GibbsSobolevLift hV hprob hf2 hfLp hgLp
  have hJ : gibbsSobolevInclusion hV hprob u = hfLp.toLp f := rfl
  have hmean : gibbsSobolevInclusion hV hprob u ∈ gibbsMeanZeroSpace hprob := by
    rw [hJ, toLp_mem_gibbsMeanZeroSpace_iff hprob hfLp]
    exact hm
  have h := gibbsSharpPoincare hV hprob hd ρ hρ hHess u hmean
  have hfnorm : ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 =
      ∫ x, f x ^ 2 ∂gibbsMeasure volume V := by
    rw [hJ, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfLp.coeFn_toLp] with x hx
    rw [hx, Real.inner_apply, pow_two]
  have henergy : gibbsDirichletEnergy hV hprob u u =
      ∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V := by
    change inner ℝ (hgLp.toLp (gradient f)) (hgLp.toLp (gradient f)) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgLp.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  rw [hfnorm, henergy] at h
  apply (le_div_iff₀ (gibbsSpectralGap_pos hV hprob hd ρ hρ hHess)).mpr
  exact (mul_comm _ _).trans_le h

/-- The centered second-moment estimate used by the source cutoff proof,
now with its actual canonical spectral gap and a derived Poincaré bound. -/
theorem gibbs_second_moment_le_dim_div_spectralGap {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0) :
    (∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume V) ≤ d / gibbsSpectralGap hV hprob := by
  let := hprob
  exact second_moment_le_of_smoothPoincare _ _
    (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess) hcenter
    (hasSmoothPoincare_gibbsSpectralGap hV hprob hd ρ hρ hHess)

end CutoffRigidity

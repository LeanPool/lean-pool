/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorBochnerInequality
public import LeanPool.CutoffRigidity.OperatorEigenCutoffLimits
public import LeanPool.CutoffRigidity.GibbsSpectralPoincare

/-! # Curvature lower bound for the actual positive operator spectrum

The localized weak Bochner estimate is exhausted by actual compact C³
cutoffs. This proves the curvature bound on every positive eigenvalue,
and hence on the attained canonical first gap. Constants at eigenvalue zero
are excluded by the explicit positive-eigenvalue hypothesis.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Every positive eigenvalue of the actual Gibbs form operator is at
least the lower Hessian curvature, without a smooth representative premise. -/
theorem gibbsOperatorEigen_positive_rate_ge_curvature {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (hrate : 0 < rate) (u : gibbsOperatorEigenspace hV hp rate)
    (hu : (u : E →₂[gibbsMeasure volume V] ℝ) ≠ 0) : ρ ≤ rate := by
  let μ := gibbsMeasure volume V
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u)
  obtain ⟨C, hC, η, hη, hηc, hbounds, hone, hgrad⟩ := exists_smooth_C3_cutoff_exhaustion (d := d)
  have hineq (n : ℕ) : (ρ - rate) * (∫ x, η n x ^ 2 * ‖G x‖ ^ 2 ∂μ) ≤
      2 * (C / ((n : ℝ) + 1)) ^ 2 * ‖G‖ ^ 2 := by
    obtain ⟨χ, hχ, hχc, hlocal⟩ := exists_compact_C3_cutoff_one_jet (tsupport (η n)) (hηc n)
    have hb := gibbsOperatorEigen_localized_bochner_inequality hV hp ρ hρ hHess rate u
      hχ hχc (hη n) (hηc n) hlocal
    have hHnonneg : 0 ≤ (∫ x, η n x ^ 2 * (∑ i : Fin d, ∑ j : Fin d,
        (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2) ∂μ) := by
      apply integral_nonneg
      intro x
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => sq_nonneg _)))
    have hboundary := (L2_vector_cutoff_boundary_bound G
      ((hη n).of_le (by norm_num)) (C / ((n : ℝ) + 1)) (by positivity) (hgrad n)).2
    change (1 / 2 : ℝ) * _ + (ρ - rate) * (∫ x, η n x ^ 2 * ‖G x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖gradient (η n) x‖ ^ 2 * ‖G x‖ ^ 2 ∂μ) at hb
    nlinarith
  have hleft := (L2_vector_cutoff_square_tendsto G η
    (fun n => (hη n).continuous.measurable) hbounds hone).const_mul (ρ - rate)
  have hright : Tendsto (fun n : ℕ => 2 * (C / ((n : ℝ) + 1)) ^ 2 * ‖G‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [differenceStep, div_eq_mul_inv, mul_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul] using
      (((differenceStep_tendsto_zero.const_mul C).pow 2).const_mul 2).mul_const (‖G‖ ^ 2)
  have hlim : (ρ - rate) * ‖G‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hineq)
  have henergy := gibbsOperatorEigen_energy hV hp rate u
  have hnorm : 0 < ‖G‖ ^ 2 := by
    change 0 < ‖gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u)‖ ^ 2
    rw [henergy]
    exact mul_pos hrate (sq_pos_of_pos (norm_pos_iff.mpr hu))
  nlinarith

/-- The actual canonical attained spectral gap has the paper's curvature
lower bound, derived from the weak Bochner proof. -/
theorem gibbsSpectralGap_ge_curvature {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ρ ≤ gibbsSpectralGap hV hp := by
  obtain ⟨u, hu⟩ := gibbsSpectralGap_hasEigenvector hV hp hd ρ hρ hHess
  apply gibbsOperatorEigen_positive_rate_ge_curvature hV hp ρ hρ hHess _
    (gibbsSpectralGap_pos hV hp hd ρ hρ hHess) u
  intro hz
  exact hu (Subtype.ext hz)

/-- The curvature Poincare inequality on the full actual closed form domain. -/
theorem gibbsCurvaturePoincare {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsSobolevGraph hV hp)
    (hu : gibbsSobolevInclusion hV hp u ∈ gibbsMeanZeroSpace hp) :
    ρ * ‖gibbsSobolevInclusion hV hp u‖ ^ 2 ≤ gibbsDirichletEnergy hV hp u u := by
  have hc := gibbsSpectralGap_ge_curvature hV hp hd ρ hρ hHess
  have hs := gibbsSharpPoincare hV hp hd ρ hρ hHess u hu
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans hs

end CutoffRigidity

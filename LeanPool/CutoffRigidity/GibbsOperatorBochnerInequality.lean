/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorIntegratedBochner

/-! # Actual localized curvature estimate on the operator eigenspace

Young's inequality absorbs the boundary cross term in the genuine weak
Bochner identity. All terms are integrable by the proved local regularity;
no classical eigenfunction representative is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual weak Hessian and gradient satisfy the localized curvature
estimate used before cutoff exhaustion in the paper's rigidity proof. -/
theorem gibbsOperatorEigen_localized_bochner_inequality {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hlocal : ∀ x ∈ tsupport η, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0) :
    (1 / 2 : ℝ) * (∫ x, η x ^ 2 * (∑ i : Fin d, ∑ j : Fin d,
      (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2) ∂gibbsMeasure volume V) +
      (ρ - rate) * (∫ x, η x ^ 2 *
        ‖gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x‖ ^ 2
        ∂gibbsMeasure volume V) ≤
      2 * (∫ x, ‖gradient η x‖ ^ 2 *
        ‖gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x‖ ^ 2
        ∂gibbsMeasure volume V) := by
  let μ := gibbsMeasure volume V
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u)
  let H (i j : Fin d) (x : E) := gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x
  let A (x : E) := η x ^ 2 * (∑ i : Fin d, ∑ j : Fin d, H i j x ^ 2)
  let B (x : E) := ∑ i : Fin d, ∑ j : Fin d, 2 * η x * coordinateDerivative j η x * (G x) i * H i j
    x
  let P (x : E) := η x ^ 2 * fderiv ℝ (fderiv ℝ V) x (G x) (G x)
  let F (x : E) := η x ^ 2 * ‖G x‖ ^ 2
  let D (x : E) := ‖gradient η x‖ ^ 2 * ‖G x‖ ^ 2
  have hA : Integrable A μ := by
    have hh := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        operatorEigen_local_hessian_energy_integrable hV hp ρ hρ hHess rate u hχ hχc hη.continuous
          hηc i j))
    simpa only [A, H, Finset.mul_sum] using hh
  have hB : Integrable B μ := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      operatorEigen_local_bochner_cross_integrable hV hp ρ hρ hHess rate u hχ hχc
        (hη.of_le (by norm_num)) hηc i j))
  have hP : Integrable P μ := by
    have hh := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        operatorEigen_local_gradient_potential_integrable hV hp rate u hη.continuous hηc i j))
    have he (x : E) : P x = ∑ i : Fin d, ∑ j : Fin d,
        η x ^ 2 * (G x) i * (coordinateDerivative i (coordinateDerivative j V) x * (G x) j) := by
      dsimp only [P]
      rw [← hessian_vector_coordinate_contraction hV]
      simp only [Finset.mul_sum, mul_assoc]
    apply hh.congr
    filter_upwards with x
    exact (he x).symm
  have hF : Integrable F μ := by
    have hh := integrable_finsetSum Finset.univ (fun i _ =>
      operatorEigen_local_gradient_energy_integrable hV hp rate u hη.continuous hηc i)
    simpa only [F, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum] using hh
  have hgrad : Continuous (gradient η) := continuous_gradient_of_c1 (hη.of_le (by norm_num))
  have hgradc : HasCompactSupport (gradient η) :=
    (hηc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  have hc : Continuous (fun x => ‖gradient η x‖ ^ 2) := hgrad.norm.pow 2
  have hcc : HasCompactSupport (fun x => ‖gradient η x‖ ^ 2) :=
    hgradc.comp_left (g := fun z : E => ‖z‖ ^ 2) (by simp)
  have hD : Integrable D μ := by
    simpa only [D, pow_two, mul_assoc] using integrable_compact_coefficient_L2_product hp
      hc hcc (Lp.memLp G).norm (Lp.memLp G).norm
  have hcurv : ρ * (∫ x, F x ∂μ) ≤ ∫ x, P x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono (hF.const_mul ρ) hP
    intro x
    dsimp only [F, P]
    nlinarith [mul_le_mul_of_nonneg_left (hHess x (G x)) (sq_nonneg (η x))]
  have hy : -(∫ x, B x ∂μ) ≤ (1 / 2 : ℝ) * (∫ x, A x ∂μ) + 2 * (∫ x, D x ∂μ) := by
    rw [← integral_neg, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hA.const_mul (1 / 2 : ℝ)) (hD.const_mul 2)]
    apply integral_mono hB.neg ((hA.const_mul (1 / 2 : ℝ)).add (hD.const_mul 2))
    intro x
    have hh := weak_bochner_boundary_young (η x) (G x) (gradient η x) (fun i j => H i j x)
    simpa only [A, B, D, Pi.neg_apply, Pi.add_apply, Pi.mul_apply, coordinateDerivative,
      fderiv_single_eq_gradient_coordinate, mul_assoc] using hh
  have he := gibbsOperatorEigen_localized_bochner_identity hV hp ρ hρ hHess rate u
    hχ hχc hη hηc hlocal
  change (∫ x, A x ∂μ) + (∫ x, B x ∂μ) + (∫ x, P x ∂μ) = rate * (∫ x, F x ∂μ) at he
  change (1 / 2 : ℝ) * (∫ x, A x ∂μ) + (ρ - rate) * (∫ x, F x ∂μ) ≤ 2 * (∫ x, D x ∂μ)
  nlinarith

end CutoffRigidity

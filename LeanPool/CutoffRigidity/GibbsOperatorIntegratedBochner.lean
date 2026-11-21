/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.OperatorEigenLocalizationTools
public import LeanPool.CutoffRigidity.OperatorBochnerAlgebra

/-! # Actual integrated localized Bochner identity for operator eigenvectors -/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A weak Euclidean localization of the global Bochner calculation in Chafaï–Fathi,
arXiv:2412.15969v5, Section 1.5, equations (1.31)–(1.33). The compact cutoff
produces a gradient cross term, as in the weighted integration by parts in
Cheng–Zhou, arXiv:1305.4116v2, Section 3, proof of Theorem 2. Here the operator
equation and compact localization give the product integrability for the weak Hessian. -/
theorem gibbsOperatorEigen_localized_bochner_identity {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hlocal : ∀ x ∈ tsupport η, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0) :
    (∫ x, η x ^ 2 * (∑ i : Fin d, ∑ j : Fin d,
      (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2) ∂gibbsMeasure volume V) +
    (∫ x, ∑ i : Fin d, ∑ j : Fin d, 2 * η x * coordinateDerivative j η x *
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x) i *
      gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x ∂gibbsMeasure volume V) +
    (∫ x, η x ^ 2 * fderiv ℝ (fderiv ℝ V) x
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x)
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x)
      ∂gibbsMeasure volume V) =
    rate * (∫ x, η x ^ 2 *
      ‖gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u) x‖ ^ 2
      ∂gibbsMeasure volume V) := by
  let μ := gibbsMeasure volume V
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp rate u)
  let A (i j : Fin d) (x : E) := η x ^ 2 *
    (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2
  let B (i j : Fin d) (x : E) := 2 * η x * coordinateDerivative j η x * (G x) i *
    gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x
  let P (i j : Fin d) (x : E) := η x ^ 2 * (G x) i *
    (coordinateDerivative i (coordinateDerivative j V) x * (G x) j)
  let F (i : Fin d) (x : E) := η x ^ 2 * ((G x) i) ^ 2
  have hA (i j : Fin d) : Integrable (A i j) μ :=
    operatorEigen_local_hessian_energy_integrable hV hp ρ hρ hHess rate u hχ hχc hη.continuous hηc
      i j
  have hB (i j : Fin d) : Integrable (B i j) μ :=
    operatorEigen_local_bochner_cross_integrable hV hp ρ hρ hHess rate u hχ hχc
      (hη.of_le (by norm_num)) hηc i j
  have hP (i j : Fin d) : Integrable (P i j) μ :=
    operatorEigen_local_gradient_potential_integrable hV hp rate u hη.continuous hηc i j
  have hF (i : Fin d) : Integrable (F i) μ :=
    operatorEigen_local_gradient_energy_integrable hV hp rate u hη.continuous hηc i
  have hrow (i : Fin d) :
      (∑ j : Fin d, ∫ x, A i j x ∂μ) + (∑ j : Fin d, ∫ x, B i j x ∂μ) =
      rate * (∫ x, F i x ∂μ) - (∑ j : Fin d, ∫ x, P i j x ∂μ) := by
    have he := gibbsOperatorEigen_localized_row_bochner hV hp ρ hρ hHess rate u
      hχ hχc hη hηc hlocal i
    have hpnt (x : E) : η x ^ 2 * (G x) i *
        (rate * (G x) i - ∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * (G x)
          j) =
        rate * F i x - ∑ j : Fin d, P i j x := by
      dsimp only [F, P]
      simp only [mul_sub, Finset.mul_sum]
      congr 1
      ring
    change (∑ j : Fin d, ∫ x, A i j x ∂μ) + (∑ j : Fin d, ∫ x, B i j x ∂μ) = _ at he
    change _ = rate * (∫ x, F i x ∂μ) - _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpnt),
      integral_sub ((hF i).const_mul rate) (integrable_finsetSum _ (fun j _ => hP i j)),
      integral_const_mul, integral_finsetSum _ (fun j _ => hP i j)] at he
    exact he
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hrow i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hAeq : (∫ x, η x ^ 2 * (∑ i : Fin d, ∑ j : Fin d,
      (gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x) ^ 2) ∂μ) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, A i j x ∂μ := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hA i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hA i j)
  have hBeq : (∫ x, ∑ i : Fin d, ∑ j : Fin d, B i j x ∂μ) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, B i j x ∂μ := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hB i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hB i j)
  have hPpoint (x : E) : η x ^ 2 * fderiv ℝ (fderiv ℝ V) x (G x) (G x) =
      ∑ i : Fin d, ∑ j : Fin d, P i j x := by
    rw [← hessian_vector_coordinate_contraction hV]
    simp only [Finset.mul_sum, P, mul_assoc]
  have hPeq : (∫ x, η x ^ 2 * fderiv ℝ (fderiv ℝ V) x (G x) (G x) ∂μ) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, P i j x ∂μ := by
    simp_rw [hPpoint]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hP i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hP i j)
  have hFeq : (∫ x, η x ^ 2 * ‖G x‖ ^ 2 ∂μ) = ∑ i : Fin d, ∫ x, F i x ∂μ := by
    simp_rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => hF i)
  change _ + (∫ x, ∑ i : Fin d, ∑ j : Fin d, B i j x ∂μ) + _ = _
  rw [hAeq, hBeq, hPeq, hFeq]
  linarith only [hs]

end CutoffRigidity

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorBochnerInequality
public import LeanPool.CutoffRigidity.OperatorEigenCutoffLimits

/-! # Actual equality-case weak Hessian decay under cutoff exhaustion -/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem operatorEigen_cutoff_hessian_memLp {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (u : gibbsOperatorEigenspace hV hp rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : Continuous η) (hηc : HasCompactSupport η) (i j : Fin d) :
    MemLp (fun x => η x * gibbsOperatorLocalizedHessian hV hp rate u hχ hχc i j x)
      2 (gibbsMeasure volume V) := by
  let := hp
  have hηm : MemLp η ⊤ (gibbsMeasure volume V) := hη.memLp_of_hasCompactSupport hηc
  exact hηm.fun_mul (gibbsOperatorLocalizedHessian_memLp_gibbs hV hp ρ hρ hHess rate u hχ hχc i j)

/-- At equality of eigenvalue and curvature, each actual localized weak
Hessian coordinate has the precise inverse-radius L² cutoff bound. -/
theorem gibbsOperatorEigen_equalRate_local_hessian_norm_bound {V χ η : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hlocal : ∀ x ∈ tsupport η, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (M : ℝ) (hM : 0 ≤ M) (hgrad : ∀ x, ‖gradient η x‖ ≤ M) (i j : Fin d) :
    ‖(operatorEigen_cutoff_hessian_memLp hV hp ρ hρ hHess ρ u hχ hχc hη.continuous hηc i j).toLp
      (fun x => η x * gibbsOperatorLocalizedHessian hV hp ρ u hχ hχc i j x)‖ ≤
      2 * M * ‖gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u)‖ := by
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u)
  let H (a b : Fin d) (x : E) := gibbsOperatorLocalizedHessian hV hp ρ u hχ hχc a b x
  have hcoord := operatorEigen_local_hessian_energy_integrable hV hp ρ hρ hHess ρ u
    hχ hχc hη.continuous hηc i j
  have htotal : Integrable (fun x => η x ^ 2 * (∑ a : Fin d, ∑ b : Fin d, (H a b x) ^ 2))
      (gibbsMeasure volume V) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
      operatorEigen_local_hessian_energy_integrable hV hp ρ hρ hHess ρ u
        hχ hχc hη.continuous hηc a b))
  have hpoint (x : E) : η x ^ 2 * (H i j x) ^ 2 ≤
      η x ^ 2 * (∑ a : Fin d, ∑ b : Fin d, (H a b x) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (Finset.single_le_sum (fun b _ => sq_nonneg (H i b x)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (H a b x)))
        (Finset.mem_univ i))
  have hcoord_le := integral_mono hcoord htotal hpoint
  have he := gibbsOperatorEigen_localized_bochner_inequality hV hp ρ hρ hHess ρ u
    hχ hχc hη hηc hlocal
  have hb := (L2_vector_cutoff_boundary_bound G (hη.of_le (by norm_num)) M hM hgrad).2
  simp only [sub_self, zero_mul, add_zero] at he
  have hcoord_bound : (∫ x, η x ^ 2 * (H i j x) ^ 2 ∂gibbsMeasure volume V) ≤
      (2 * M * ‖G‖) ^ 2 := by
    change _ ≤ M ^ 2 * ‖G‖ ^ 2 at hb
    dsimp only [H, G] at hcoord_le ⊢
    nlinarith [he, hb]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hM) (norm_nonneg G))).mp
  rw [norm_toLp_sq]
  simpa only [mul_pow] using hcoord_bound

end CutoffRigidity

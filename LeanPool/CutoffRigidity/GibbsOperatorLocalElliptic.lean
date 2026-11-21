/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorWeakEigenfunction
public import LeanPool.CutoffRigidity.EuclideanHessianEnergy

/-! # Actual distributional Laplacian for operator eigenvectors

The actual closed weak gradient and compact test identities identify the
ordinary distributional Laplacian with a genuinely locally L² function.
Weak second-derivative construction is a further step, not a premise.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual vector-coordinate products with continuous compact coefficients
are Lebesgue integrable under the positive Gibbs density. -/
theorem integrable_compact_test_gibbsVector_coordinate_volume {V χ : E → ℝ}
    (hV : Continuous V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (w : E →₂[gibbsMeasure volume V] E) (i : Fin d) :
    Integrable (fun x => χ x * (w x) i) volume := by
  have hi : MemLp (fun x => (w x) i) 2 (gibbsMeasure volume V) := by
    apply (Lp.memLp w).of_le_mul (c := 1) (by fun_prop)
    filter_upwards with x
    simpa only [one_mul] using (PiLp.norm_apply_le (w x) i)
  have hh := integrable_compact_test_mul_gibbsLp_volume hV hprob hχ hχc (hi.toLp (fun x => (w x) i))
  have hae := (gibbsMeasure_ae_eq_iff volume hV.measurable).mp hi.coeFn_toLp
  apply hh.congr
  filter_upwards [hae] with x hx
  rw [hx]

/-- Actual closed weak gradients give the ordinary distributional Laplacian
pairing, with no classical differentiability of the Sobolev element. -/
theorem gibbsSobolev_laplacian_test_volume {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : gibbsSobolevGraph hV hprob)
    (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    (∫ x, gibbsSobolevInclusion hV hprob u x * euclideanLaplacian φ x) =
      -(∫ x, inner ℝ (gibbsSobolevDerivative hV hprob u x) (gradient φ x)) := by
  let U := gibbsSobolevInclusion hV hprob u
  let G := gibbsSobolevDerivative hV hprob u
  have hd (i : Fin d) : ContDiff ℝ 2 (coordinateDerivative i φ) := by
    apply contDiff_coordinateDerivative
    convert hφ using 1
    norm_num
  have hdc (i : Fin d) : HasCompactSupport (coordinateDerivative i φ) :=
    hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hrow (i : Fin d) := gibbsSobolev_coordinate_weak_derivative_volume hV hprob (hd i) (hdc i) i
    u
  have hInt (i : Fin d) := gibbsSobolev_coordinate_pairings_integrable_volume hV hprob (hd i) (hdc
    i) i u
  have hGp (x : E) : inner ℝ (G x) (gradient φ x) =
      ∑ i : Fin d, coordinateDerivative i φ x * (G x) i := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
    ring
  have hLp (x : E) : U x * euclideanLaplacian φ x =
      ∑ i : Fin d, coordinateDerivative i (coordinateDerivative i φ) x * U x := by
    change U x * (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i φ) x) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change (∫ x, U x * euclideanLaplacian φ x) = -(∫ x, inner ℝ (G x) (gradient φ x))
  simp_rw [hLp, hGp]
  rw [integral_finsetSum _ (fun i _ => (hInt i).2), integral_finsetSum _ (fun i _ => (hInt i).1)]
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hrow i)
  simp only [Finset.sum_neg_distrib] at hs
  linarith

/-- The actual distributional elliptic equation for operator eigenvectors,
with the actual locally L² right-hand side supplied by the preceding module. -/
theorem gibbsOperatorEigen_distributional_laplacian {V φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * euclideanLaplacian φ x) =
      ∫ x, φ x * (inner ℝ (gradient V x)
        (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) -
          rate * (u : E →₂[gibbsMeasure volume V] ℝ) x) := by
  let v := gibbsOperatorEigenSobolevLift hV hprob rate u
  let G := gibbsSobolevDerivative hV hprob v
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hgradInt : Integrable (fun x => inner ℝ (G x) (gradient φ x)) volume := by
    have hi (i : Fin d) : Integrable (fun x => coordinateDerivative i φ x * (G x) i) volume :=
      integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob
        (c1_coordinateDerivative_of_c2 hφ2 i).continuous
        (hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)) G i
    have hh := integrable_finsetSum Finset.univ (fun i _ => hi i)
    convert hh using 1
    funext x
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
    ring
  have hGV : Continuous (gradient V) := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hDriftInt : Integrable (fun x => φ x * inner ℝ (gradient V x) (G x)) volume := by
    have hi (i : Fin d) : Integrable (fun x => (φ x * (gradient V x) i) * (G x) i) volume := by
      have hc : Continuous (fun x => φ x * (gradient V x) i) :=
        hφ.continuous.mul ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp hGV)
      have hs : HasCompactSupport (fun x => φ x * (gradient V x) i) := by
        simpa only [Pi.mul_def] using hφc.mul_right (f' := fun x => (gradient V x) i)
      exact integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob hc hs G i
    have hh := integrable_finsetSum Finset.univ (fun i _ => hi i)
    convert hh using 1
    funext x
    rw [PiLp.inner_apply, Finset.mul_sum]
    simp only [Real.inner_apply, mul_assoc]
  have hSourceInt : Integrable (fun x => (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x) volume := by
    have hh := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob hφ.continuous hφc
      (u : E →₂[gibbsMeasure volume V] ℝ)
    simpa only [mul_comm] using hh
  have he := gibbsOperatorEigen_volume_test_equation hV hprob rate u hφ2 hφc
  have hp (x : E) : inner ℝ (G x) (gradient φ x + φ x • gradient V x) =
      inner ℝ (G x) (gradient φ x) + φ x * inner ℝ (gradient V x) (G x) := by
    rw [inner_add_right, inner_smul_right, real_inner_comm (G x) (gradient V x)]
  change (∫ x, inner ℝ (G x) (gradient φ x + φ x • gradient V x)) = _ at he
  simp_rw [hp] at he
  rw [integral_add hgradInt hDriftInt] at he
  have hlap := gibbsSobolev_laplacian_test_volume hV hprob v hφ hφc
  rw [gibbsOperatorEigenSobolevLift_inclusion] at hlap
  have hr : (∫ x, φ x * (inner ℝ (gradient V x) (G x) - rate * (u : E →₂[gibbsMeasure volume V] ℝ)
    x)) =
      (∫ x, φ x * inner ℝ (gradient V x) (G x)) -
        rate * (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * φ x) := by
    rw [← integral_const_mul, ← integral_sub hDriftInt (hSourceInt.const_mul rate)]
    apply integral_congr_ae
    filter_upwards with x
    ring
  change (∫ x, (u : E →₂[gibbsMeasure volume V] ℝ) x * euclideanLaplacian φ x) = _
  rw [hr]
  linarith

end CutoffRigidity

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.HessianDistributionRepresentation

/-! # Actual local weak Hessians of operator eigenvectors

The operator eigenvector's compact localization satisfies an actual L²
Laplace equation and an independently derived translation bound. The bounded
distribution construction therefore supplies actual local L² Hessians.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual operator eigenvectors have genuine L² second-derivative
representatives after every compact C³ localization. No representative
regularity or weak H² membership is assumed. -/
theorem exists_gibbsOperatorEigen_local_weak_hessian {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) :
    ∃ H : E →₂[volume] ℝ,
      ‖H‖ ≤ ‖(localizedOperatorEigenLaplacian_memLp hV hprob rate u hχ hχc).toLp
        (localizedOperatorEigenLaplacian hV hprob rate u χ)‖ ∧
      ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
        (∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) *
          coordinateDerivative j (coordinateDerivative i ψ) x) = ∫ x, H x * ψ x := by
  let v := gibbsOperatorEigenSobolevLift hV hprob rate u
  let w (x : E) := χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x
  let F := localizedOperatorEigenLaplacian hV hprob rate u χ
  have hwm : Measurable w := hχ.continuous.measurable.mul
    (Lp.stronglyMeasurable (u : E →₂[gibbsMeasure volume V] ℝ)).measurable
  have hw : MemLp w 2 volume := compact_cutoff_gibbsLp_memLp_volume hV.continuous
    hχ.continuous hχc (u : E →₂[gibbsMeasure volume V] ℝ)
  have hwc : HasCompactSupport w := by
    simpa only [w, Pi.mul_def] using hχc.mul_right (f' := fun x => (u : E →₂[gibbsMeasure volume V]
      ℝ) x)
  have hFm : Measurable F := by
    have huM := (Lp.stronglyMeasurable (u : E →₂[gibbsMeasure volume V] ℝ)).measurable
    have hGM := (Lp.stronglyMeasurable (gibbsSobolevDerivative hV hprob v)).measurable
    have hGV := continuous_gradient_of_c1 (hV.of_le (by norm_num))
    have hGχ := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
    have hLap := (euclideanLaplacian_contDiff_one hχ).continuous
    have hχm := hχ.continuous.measurable
    dsimp only [F]
    unfold localizedOperatorEigenLaplacian
    fun_prop
  have hF : MemLp F 2 volume := localizedOperatorEigenLaplacian_memLp hV hprob rate u hχ hχc
  obtain ⟨K, hK, hKt⟩ := exists_gibbsSobolev_cutoff_translation_integral_bound hV hprob
    (hχ.of_le (by norm_num)) hχc
  let C := Real.sqrt K * ‖v‖
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have htrans (h : E) : (∫ x, (w (x + h) - w x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2 := by
    have ht := hKt v h
    rw [gibbsOperatorEigenSobolevLift_inclusion] at ht
    have hc : C ^ 2 = K * ‖v‖ ^ 2 := by dsimp [C]; rw [mul_pow, Real.sq_sqrt hK.le]
    rw [hc]
    simpa only [w, mul_assoc, mul_left_comm, mul_comm] using ht
  apply exists_L2_second_derivative_of_distributional_laplacian hwm hw hwc hFm hF C hC htrans
  intro ψ hψ hψc
  exact gibbsOperatorEigen_localized_distributional_laplacian hV hprob rate u hχ hχc hψ hψc

/-- The actual localized first-gradient coordinate (the genuine product rule
for the weak gradient, expressed as a pointwise measurable representative). -/
@[expose] noncomputable def localizedOperatorEigenGradient {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (χ : E → ℝ) (i : Fin d) (x : E) : ℝ :=
  χ x * (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) i +
    (u : E →₂[gibbsMeasure volume V] ℝ) x * coordinateDerivative i χ x

/-- The localized weak first-gradient coordinate genuinely belongs to L². -/
theorem localizedOperatorEigenGradient_memLp {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i : Fin d) : MemLp (localizedOperatorEigenGradient hV hprob rate u χ i) 2 volume := by
  have ha := compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hχ.continuous
    hχc
    (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u)) i
  have hb := compact_cutoff_gibbsLp_memLp_volume hV.continuous
    (c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i).continuous
    (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)) (u : E →₂[gibbsMeasure volume V] ℝ)
  convert ha.add hb using 1
  funext x
  simp only [localizedOperatorEigenGradient, Pi.add_apply]
  ring

/-- The actual first weak derivative of the compact localization, tested
against one derivative of a compact C³ function. -/
theorem localizedOperatorEigenGradient_second_test {V χ ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 3 ψ) (i j : Fin d) :
    (∫ x, localizedOperatorEigenGradient hV hprob rate u χ i x * coordinateDerivative j ψ x) =
      -(∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) *
        coordinateDerivative j (coordinateDerivative i ψ) x) := by
  let v := gibbsOperatorEigenSobolevLift hV hprob rate u
  let G := gibbsSobolevDerivative hV hprob v
  let U (x : E) := (u : E →₂[gibbsMeasure volume V] ℝ) x
  have hDψ : ContDiff ℝ 2 (coordinateDerivative j ψ) := by
    apply contDiff_coordinateDerivative
    convert hψ using 1
    norm_num
  have hDχ := c1_coordinateDerivative_of_c2 (hχ.of_le (by norm_num)) i
  have hDDψ := (c1_coordinateDerivative_of_c2 hDψ i).continuous
  have ht : ContDiff ℝ 2 (fun x => χ x * coordinateDerivative j ψ x) :=
    (hχ.of_le (by norm_num)).mul hDψ
  have htc : HasCompactSupport (fun x => χ x * coordinateDerivative j ψ x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative j ψ)
  let A (x : E) := (χ x * coordinateDerivative j ψ x) * (G x) i
  let B (x : E) := (coordinateDerivative i χ x * coordinateDerivative j ψ x) * U x
  let D (x : E) := (χ x * coordinateDerivative i (coordinateDerivative j ψ) x) * U x
  have hA : Integrable A volume := integrable_compact_test_gibbsVector_coordinate_volume
    hV.continuous hprob (hχ.continuous.mul hDψ.continuous) htc G i
  have hB : Integrable B volume := by
    have hc : HasCompactSupport (fun x => coordinateDerivative i χ x * coordinateDerivative j ψ x)
      := by
      simpa only [Pi.mul_def, coordinateDerivative] using (hχc.fderiv_apply ℝ
        (EuclideanSpace.single i 1)).mul_right
        (f' := coordinateDerivative j ψ)
    exact integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hDχ.continuous.mul hDψ.continuous) hc (u : E →₂[gibbsMeasure volume V] ℝ)
  have hD : Integrable D volume := by
    have hc : HasCompactSupport (fun x => χ x * coordinateDerivative i (coordinateDerivative j ψ)
      x) := by
      simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative i
        (coordinateDerivative j ψ))
    exact integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hχ.continuous.mul hDDψ) hc (u : E →₂[gibbsMeasure volume V] ℝ)
  have he := gibbsSobolev_coordinate_weak_derivative_volume hV hprob ht htc i v
  rw [gibbsOperatorEigenSobolevLift_inclusion] at he
  have hp (x : E) : coordinateDerivative i (fun y => χ y * coordinateDerivative j ψ y) x * U x = D
    x + B x := by
    rw [coordinateDerivative_mul_actual (hχ.differentiable (by norm_num)) (hDψ.differentiable
      (by norm_num))]
    dsimp [D, B]
    ring
  change (∫ x, A x) = -(∫ x, coordinateDerivative i (fun y => χ y * coordinateDerivative j ψ y) x *
    U x) at he
  simp_rw [hp] at he
  rw [integral_add hD hB] at he
  have hleft : (∫ x, localizedOperatorEigenGradient hV hprob rate u χ i x * coordinateDerivative j
    ψ x) =
      (∫ x, A x) + (∫ x, B x) := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [localizedOperatorEigenGradient, A, B, G, U, v]
    ring
  have hright : (∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) *
      coordinateDerivative j (coordinateDerivative i ψ) x) = ∫ x, D x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [coordinateDerivative_commute (hψ.of_le (by norm_num)) j i]
    dsimp [D, U]
    ring
  rw [hleft, hright]
  linarith

/-- The constructed L² Hessian is the genuine weak derivative of the actual
localized first weak gradient, not merely a bounded scalar candidate. -/
theorem exists_gibbsOperatorEigen_local_gradient_weak_derivative {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (i j : Fin d) :
    ∃ H : E →₂[volume] ℝ,
      ‖H‖ ≤ ‖(localizedOperatorEigenLaplacian_memLp hV hprob rate u hχ hχc).toLp
        (localizedOperatorEigenLaplacian hV hprob rate u χ)‖ ∧
      ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
        (∫ x, localizedOperatorEigenGradient hV hprob rate u χ i x * coordinateDerivative j ψ x) =
          -(∫ x, H x * ψ x) := by
  obtain ⟨H, hH, hpair⟩ := exists_gibbsOperatorEigen_local_weak_hessian hV hprob rate u hχ hχc i j
  refine ⟨H, hH, ?_⟩
  intro ψ hψ hψc
  rw [localizedOperatorEigenGradient_second_test hV hprob rate u hχ hχc hψ i j,
    hpair ψ hψ hψc]

end CutoffRigidity

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightNearComparison
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalKernelBallScaling

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.FractionalBoundaryWeightedNearKernel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Near-field fractional boundary-weight kernel
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Inside half the center boundary distance, Lipschitz comparability of the
weight and the radius-sharp Riesz integral give homogeneous order `s-p`. -/
theorem exists_bound_lintegral_near_fractionalBoundaryKernel
    (hd : 1 ≤ d) {s p : ℝ} (hs : 0 < s) (hp : 0 ≤ p)
    (hsp : s < p) (hp1 : p < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U → ∀ x ∈ U,
        (∫⁻ y in U ∩ euclideanBallAt x
            (euclideanBoundaryDistance U x / 2),
          ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U p y ∂volume) ≤
          C * ENNReal.ofReal
            (euclideanBoundaryDistance U x ^ (s - p)) := by
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hedim : -(d : ℝ) < s - (d : ℝ) := by linarith only [hs]
  have he0 : s - (d : ℝ) < 0 := by linarith only [hdreal, hp1, hsp]
  obtain ⟨B, hBtop, hB⟩ :=
    exists_bound_lintegral_ball_rpow_scaled d hedim he0
  let A : ℝ := (2 : ℝ) ^ (p - s)
  let C : ℝ≥0∞ := B * ENNReal.ofReal A
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨C, ENNReal.mul_ne_top hBtop ENNReal.ofReal_ne_top, ?_⟩
  intro U hU x hx
  let delta : ℝ := euclideanBoundaryDistance U x
  let r0 : ℝ := delta / 2
  have hdelta : 0 < delta := euclideanBoundaryDistance_pos hd hU hx
  have hr0 : 0 < r0 := by dsimp only [r0]; positivity
  let W : ℝ≥0∞ := ENNReal.ofReal (r0 ^ (-p))
  have hkernelMeas : Measurable (fun y : Vec d =>
      ENNReal.ofReal (‖x - y‖ ^ (s - (d : ℝ)))) := by
    exact ((continuous_const.sub continuous_id).norm.measurable.pow
      measurable_const).ennreal_ofReal
  have hpoint : ∀ y ∈ U ∩ euclideanBallAt x r0,
      ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
          euclideanBoundaryWeight U p y ≤
        ENNReal.ofReal (‖x - y‖ ^ (s - (d : ℝ))) * W := by
    intro y hy
    have hweight : euclideanBoundaryWeight U p y ≤ W := by
      dsimp only [W, r0, delta]
      exact euclideanBoundaryWeight_le_of_mem_half_ball U hp hdelta hy.2
    have hkernel : ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) ≤
        ENNReal.ofReal (‖x - y‖ ^ (s - (d : ℝ))) := by
      by_cases hxy : x = y
      · subst y
        simp [Real.zero_rpow (ne_of_lt he0)]
      · apply ENNReal.ofReal_le_ofReal
        have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
        have hle : ‖x - y‖ ≤ euclideanDist x y := by
          simpa only [euclideanDist] using! norm_le_sqrt_vecNormSq (x - y)
        exact Real.rpow_le_rpow_of_nonpos hnorm hle he0.le
    exact mul_le_mul' hkernel hweight
  calc
    (∫⁻ y in U ∩ euclideanBallAt x
        (euclideanBoundaryDistance U x / 2),
      ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
        euclideanBoundaryWeight U p y ∂volume) ≤
        ∫⁻ y in U ∩ euclideanBallAt x r0,
          ENNReal.ofReal (‖x - y‖ ^ (s - (d : ℝ))) * W ∂volume := by
      dsimp only [r0, delta]
      exact setLIntegral_mono'
        (hU.isOpen.measurableSet.inter
          (isOpen_euclideanBallAt x _).measurableSet) hpoint
    _ = (∫⁻ y in U ∩ euclideanBallAt x r0,
          ENNReal.ofReal (‖x - y‖ ^ (s - (d : ℝ))) ∂volume) * W := by
      rw [lintegral_mul_const _ hkernelMeas]
    _ ≤ (∫⁻ y in Metric.ball x r0,
          ENNReal.ofReal (‖x - y‖ ^ (s - (d : ℝ))) ∂volume) * W := by
      apply mul_le_mul_left
      exact lintegral_mono_set fun y hy =>
        euclideanBallAt_subset_metricBall x hr0 hy.2
    _ ≤ (B * ENNReal.ofReal (r0 ^ s)) * W := by
      apply mul_le_mul_left
      simpa only [show s - (d : ℝ) + (d : ℝ) = s by ring] using hB x hr0
    _ = C * ENNReal.ofReal (delta ^ (s - p)) := by
      have hreal : r0 ^ s * r0 ^ (-p) = A * delta ^ (s - p) := by
        have hhalf : r0 = (2 : ℝ)⁻¹ * delta := by
          dsimp only [r0]
          ring
        rw [← Real.rpow_add hr0]
        rw [hhalf, Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
          hdelta.le]
        have hinv : ((2 : ℝ)⁻¹) ^ (s + -p) = 2 ^ (p - s) := by
          rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
        rw [hinv]
        dsimp only [A]
        congr 2
      dsimp only [W, C]
      calc
        B * ENNReal.ofReal (r0 ^ s) * ENNReal.ofReal (r0 ^ (-p)) =
            B * (ENNReal.ofReal (r0 ^ s) *
              ENNReal.ofReal (r0 ^ (-p))) := by ring
        _ = B * ENNReal.ofReal (r0 ^ s * r0 ^ (-p)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le s)]
        _ = B * ENNReal.ofReal (A * delta ^ (s - p)) := by rw [hreal]
        _ = B * (ENNReal.ofReal A *
              ENNReal.ofReal (delta ^ (s - p))) := by
          rw [ENNReal.ofReal_mul hA0]
        _ = B * ENNReal.ofReal A *
              ENNReal.ofReal (delta ^ (s - p)) := by ring

end

end HighContrast
end HCPolySupport

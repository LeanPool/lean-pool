/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreSpatialCutoffs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient
public import LeanPool.GinibrePoincare.Analysis.SobolevTruncation

/-! # Smooth symmetric radial spatial cutoffs

Cutoffs of the total squared radius are smooth in the original configuration
coordinates. Their squared gradient is uniformly O(1/(m+1)).
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section


/-- Smooth compact spatial cutoff expanding through the total squared configuration radius. -/
def ginibreSpatialCutoff (n m : ℕ) (z : Configuration n) : ℝ :=
  sobolevCutoff m (configurationNormSq z)

theorem ginibreSpatialCutoff_smooth (n m : ℕ) : ContDiff ℝ ∞ (ginibreSpatialCutoff n m) :=
  (sobolevCutoff_smooth m).comp contDiff_configurationNormSq

theorem ginibreSpatialCutoff_symmetric (n m : ℕ) : IsSymmetric (ginibreSpatialCutoff n m) := by
  intro σ z
  simp only [ginibreSpatialCutoff, configurationNormSq_permute]

theorem ginibreSpatialCutoff_radial (n m : ℕ) :
    ∃ F : (Fin n → ℝ) → ℝ,
      ∀ z, ginibreSpatialCutoff n m z = F (fun i => Complex.normSq (z i)) :=
  ⟨fun r => sobolevCutoff m (∑ i, r i), fun _ => rfl⟩

theorem ginibreSpatialCutoff_mem_unit (n m : ℕ) (z : Configuration n) :
    0 ≤ ginibreSpatialCutoff n m z ∧ ginibreSpatialCutoff n m z ≤ 1 :=
  sobolevCutoff_mem_unit m (configurationNormSq z)

theorem ginibreSpatialCutoff_support_bound (n m : ℕ) :
    tsupport (ginibreSpatialCutoff n m) ⊆
      {z | configurationNormSq z ≤ 2 * ((m : ℝ) + 1)} := by
  intro z hz
  have ht : configurationNormSq z / ((m : ℝ) + 1) ∈ tsupport sobolevCutoffBump :=
    tsupport_comp_subset_preimage sobolevCutoffBump
      (show Continuous (fun z : Configuration n => configurationNormSq z / ((m : ℝ) + 1))
        from contDiff_configurationNormSq.continuous.div_const _) hz
  rw [sobolevCutoffBump.tsupport_eq] at ht
  have hd : |configurationNormSq z / ((m : ℝ) + 1)| ≤ 2 := by
    simpa [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump, abs_div] using ht
  exact (div_le_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mp ((le_abs_self _).trans hd)

theorem ginibreSpatialCutoff_compact (n m : ℕ) : HasCompactSupport (ginibreSpatialCutoff n m) := by
  apply (isCompact_closedBall (0 : Configuration n) (2 * ((m : ℝ) + 1) + 1)).of_isClosed_subset
    (isClosed_tsupport _)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * ((m : ℝ) + 1) + 1)).mpr
  intro i
  have hq : configurationNormSq z ≤ 2 * ((m : ℝ) + 1) :=
    ginibreSpatialCutoff_support_bound n m hz
  have hi : Complex.normSq (z i) ≤ configurationNormSq z :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at hi
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hz0 := norm_nonneg (z i)
  nlinarith [sq_nonneg (2 * ((m : ℝ) + 1))]

theorem ginibreSpatialCutoff_core (n m : ℕ) : IsRadialSobolevCore (ginibreSpatialCutoff n m) :=
  ⟨⟨ginibreSpatialCutoff_smooth n m, ginibreSpatialCutoff_compact n m,
    ginibreSpatialCutoff_symmetric n m⟩, ginibreSpatialCutoff_radial n m⟩

theorem ginibreSpatialCutoff_tendsto (n : ℕ) (z : Configuration n) :
    Tendsto (fun m => ginibreSpatialCutoff n m z) atTop (𝓝 1) :=
  (sobolevCutoff_tendsto (configurationNormSq z)).1

theorem ginibreSpatialCutoff_gradient_coordinate (n m : ℕ) (z : Configuration n)
    (k : Fin n × Fin 2) :
    ginibreEuclideanGradient (ginibreSpatialCutoff n m) z k =
      deriv (sobolevCutoff m) (configurationNormSq z) *
        fderiv ℝ configurationNormSq z (ginibreCoordinateDirection k) := by
  rw [ginibreEuclideanGradient_coordinate]
  have he := ((sobolevCutoff_smooth m).differentiable (by simp) (configurationNormSq z)).hasDerivAt
    |>.comp_hasFDerivAt z (contDiff_configurationNormSq.differentiable (by
      simp)).differentiableAt.hasFDerivAt
  rw [show ginibreSpatialCutoff n m = sobolevCutoff m ∘ configurationNormSq from rfl, he.fderiv]
  rfl

theorem configurationNormSq_gradient_norm_sq {n : ℕ} (z : Configuration n) :
    ‖ginibreEuclideanGradient configurationNormSq z‖ ^ 2 = 4 * configurationNormSq z := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [ginibreEuclideanGradient_coordinate, Fintype.sum_prod_type, Fin.sum_univ_two,
    ]
  change (∑ i, (‖fderiv ℝ configurationNormSq z (realCoordinateDirection i)‖ ^ 2 +
    ‖fderiv ℝ configurationNormSq z (imaginaryCoordinateDirection i)‖ ^ 2)) = _
  have hr (i : Fin n) : fderiv ℝ configurationNormSq z (realCoordinateDirection i) =
      2 * (z i).re := by
    rw [fderiv_configurationNormSq_apply]
    simp only [realCoordinateDirection, coordinateDirection]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi; simp [hbi]
    · simp
  have hi (i : Fin n) : fderiv ℝ configurationNormSq z (imaginaryCoordinateDirection i) =
      2 * (z i).im := by
    rw [fderiv_configurationNormSq_apply]
    simp only [imaginaryCoordinateDirection, coordinateDirection]
    rw [Finset.sum_eq_single i]
    · simp [Complex.mul_re]
    · intro b hb hbi; simp [hbi]
    · simp
  simp_rw [hr, hi, Real.norm_eq_abs, sq_abs]
  unfold configurationNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_apply]
  ring

theorem ginibreSpatialCutoff_gradient_norm_sq (n m : ℕ) (z : Configuration n) :
    ‖ginibreEuclideanGradient (ginibreSpatialCutoff n m) z‖ ^ 2 =
      (deriv (sobolevCutoff m) (configurationNormSq z)) ^ 2 * (4 * configurationNormSq z) := by
  have he : ginibreEuclideanGradient (ginibreSpatialCutoff n m) z =
      deriv (sobolevCutoff m) (configurationNormSq z) •
        ginibreEuclideanGradient configurationNormSq z := by
    apply PiLp.ext
    intro k
    rw [ginibreSpatialCutoff_gradient_coordinate, PiLp.smul_apply,
      ginibreEuclideanGradient_coordinate]
    rfl
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, configurationNormSq_gradient_norm_sq]

theorem ginibreSpatialCutoff_gradient_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m (z : Configuration n),
      ‖ginibreEuclideanGradient (ginibreSpatialCutoff n m) z‖ ^ 2 ≤ C / ((m : ℝ) + 1) := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  refine ⟨8 * M ^ 2, by positivity, ?_⟩
  intro n m z
  by_cases hz : z ∈ tsupport (ginibreSpatialCutoff n m)
  · have hq : configurationNormSq z ≤ 2 * ((m : ℝ) + 1) :=
    ginibreSpatialCutoff_support_bound n m hz
    have hq0 := configurationNormSq_nonneg z
    have hd := hM m (configurationNormSq z)
    have hm : 0 < (m : ℝ) + 1 := by positivity
    have hb : (deriv (sobolevCutoff m) (configurationNormSq z)) ^ 2 ≤
        (M / ((m : ℝ) + 1)) ^ 2 := by
      nlinarith [sq_abs (deriv (sobolevCutoff m) (configurationNormSq z)),
        abs_nonneg (deriv (sobolevCutoff m) (configurationNormSq z))]
    rw [ginibreSpatialCutoff_gradient_norm_sq]
    calc
      _ ≤ (M / ((m : ℝ) + 1)) ^ 2 * (4 * configurationNormSq z) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ (M / ((m : ℝ) + 1)) ^ 2 * (4 * (2 * ((m : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = 8 * M ^ 2 / ((m : ℝ) + 1) := by field_simp; ring
  · have hd := fderiv_of_notMem_tsupport hz (𝕜 := ℝ)
    have he : ginibreEuclideanGradient (ginibreSpatialCutoff n m) z = 0 := by
      apply PiLp.ext
      intro k
      rw [ginibreEuclideanGradient_coordinate, hd]
      rfl
    rw [he]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

theorem ginibreSpatialCutoff_gradient_tendsto (n : ℕ) (z : Configuration n) :
    Tendsto (fun m => ginibreEuclideanGradient (ginibreSpatialCutoff n m) z) atTop (𝓝 0) := by
  have he : (fun m => ginibreEuclideanGradient (ginibreSpatialCutoff n m) z) =
      (fun m => deriv (sobolevCutoff m) (configurationNormSq z) •
        ginibreEuclideanGradient configurationNormSq z) := by
    funext m
    apply PiLp.ext
    intro k
    rw [ginibreSpatialCutoff_gradient_coordinate, PiLp.smul_apply,
      ginibreEuclideanGradient_coordinate]
    rfl
  rw [he]
  simpa using (sobolevCutoff_tendsto (configurationNormSq z)).2.smul_const
    (ginibreEuclideanGradient configurationNormSq z)

end
end GinibrePoincare

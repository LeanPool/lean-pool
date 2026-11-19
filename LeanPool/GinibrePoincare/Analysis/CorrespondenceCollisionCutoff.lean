/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCollisionCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCollisionMass

/-!
# Correspondence collision cutoff

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `correspondenceCollisionCutoff_mem_unit`, `correspondenceCollisionCutoff_zero`,
`correspondenceCollisionCutoff_one_gradient_zero`, `correspondenceCollisionCutoff_gradient_bound`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff ENNReal

private theorem pairNormSq_smooth {n : ℕ} (j k : Fin n) :
    ContDiff ℝ ∞ (fun w : Configuration n => Complex.normSq (w j-w k)) := by
  have h : ContDiff ℝ ∞ (fun w : Configuration n => w j-w k) :=
    ContDiff.sub (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).contDiff
      (ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ).contDiff
  have hr : ContDiff ℝ ∞ (fun w : Configuration n => (w j-w k).re) :=
    Complex.reCLM.contDiff.comp h
  have hi : ContDiff ℝ ∞ (fun w : Configuration n => (w j-w k).im) :=
    Complex.imCLM.contDiff.comp h
  simpa only [Complex.normSq_apply] using ContDiff.add (ContDiff.mul hr hr) (ContDiff.mul hi hi)

/-- The single-hyperplane smooth cutoff used in Appendix A, at actual width `ε`. -/
def correspondenceCollisionCutoff {n : ℕ} (j k : Fin n) (ε : ℝ)
    (z : Configuration n) : ℝ :=
  1 - sobolevCutoffBump (Complex.normSq (z j - z k) / ε ^ 2)

theorem correspondenceCollisionCutoff_smooth {n : ℕ} (j k : Fin n) (ε : ℝ) :
    ContDiff ℝ ∞ (correspondenceCollisionCutoff j k ε) := by
  unfold correspondenceCollisionCutoff
  apply contDiff_const.sub
  apply sobolevCutoffBump.contDiff.comp
  exact (pairNormSq_smooth j k).div_const _

theorem correspondenceCollisionCutoff_mem_unit {n : ℕ} (j k : Fin n) (ε : ℝ)
    (z : Configuration n) :
    0 ≤ correspondenceCollisionCutoff j k ε z ∧
      correspondenceCollisionCutoff j k ε z ≤ 1 := by
  have h0 := sobolevCutoffBump.nonneg (x := Complex.normSq (z j-z k)/ε^2)
  have h1 := sobolevCutoffBump.le_one (x := Complex.normSq (z j-z k)/ε^2)
  unfold correspondenceCollisionCutoff
  constructor <;> linarith

theorem correspondenceCollisionCutoff_zero {n : ℕ} (j k : Fin n) {ε : ℝ}
    (hε : 0 < ε) (z : Configuration n) (hz : ‖z j - z k‖ ≤ ε) :
    correspondenceCollisionCutoff j k ε z = 0 := by
  have hb : sobolevCutoffBump (Complex.normSq (z j-z k)/ε^2) = 1 := by
    apply sobolevCutoffBump.one_of_mem_closedBall
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, sobolevCutoffBump]
    rw [abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))]
    rw [Complex.normSq_eq_norm_sq]
    exact (div_le_one (by positivity)).mpr ((sq_le_sq₀ (norm_nonneg _) hε.le).mpr hz)
  simp [correspondenceCollisionCutoff, hb]

theorem correspondenceCollisionCutoff_gradient {n : ℕ} (j k : Fin n) (ε : ℝ)
    (z : Configuration n) :
    ginibreEuclideanGradient (correspondenceCollisionCutoff j k ε) z =
      (-deriv (sobolevCutoffBump : ℝ → ℝ) (Complex.normSq (z j-z k)/ε^2) / ε^2) •
        ginibreEuclideanGradient (fun w : Configuration n => Complex.normSq (w j-w k)) z := by
  have hf : ContDiff ℝ ∞ (fun w : Configuration n => Complex.normSq (w j-w k)) :=
    pairNormSq_smooth j k
  have harg : HasFDerivAt (fun w : Configuration n => Complex.normSq (w j-w k)/ε^2)
      ((ε^2)⁻¹ • fderiv ℝ (fun w : Configuration n => Complex.normSq (w j-w k)) z) z := by
    have heq : (fun w : Configuration n => Complex.normSq (w j-w k)/ε^2) =
        fun w => (ε^2)⁻¹ * Complex.normSq (w j-w k) := by
      funext w; simp [div_eq_mul_inv, mul_comm]
    rw [heq]
    exact ((hf.differentiable (by simp) z).hasFDerivAt).const_smul ((ε^2)⁻¹)
  have h := ((sobolevCutoffBump.contDiff (n := ⊤)).differentiable (by simp)
    (Complex.normSq (z j-z k)/ε^2)).hasDerivAt.comp_hasFDerivAt z harg
  have hd := (hasFDerivAt_const (1 : ℝ) z).sub h
  change HasFDerivAt (correspondenceCollisionCutoff j k ε) _ z at hd
  ext q
  rw [ginibreEuclideanGradient_coordinate, hd.fderiv]
  simp [ginibreEuclideanGradient_coordinate]
  ring

private theorem pair_directional_energy_bound {n : ℕ} (j k : Fin n)
    (z : Configuration n) :
    complexDirectionalEnergy (fun w : Configuration n => w j-w k) z ≤ 8 * n := by
  have hd (q : Fin n × Fin 2) (i : Fin n) : ‖ginibreCoordinateDirection q i‖ ≤ 1 := by
    unfold ginibreCoordinateDirection realCoordinateDirection imaginaryCoordinateDirection
      coordinateDirection
    split_ifs <;> simp only []
    all_goals split_ifs <;> simp
  unfold complexDirectionalEnergy
  have hf : HasFDerivAt (fun w : Configuration n => w j-w k)
      ((ContinuousLinearMap.proj j)-(ContinuousLinearMap.proj k)) z :=
    ((ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).hasFDerivAt).sub
      ((ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ).hasFDerivAt)
  rw [hf.fderiv]
  calc
    _ ≤ ∑ _q : Fin n × Fin 2, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      simp only [sub_apply, ContinuousLinearMap.proj_apply,
        Complex.normSq_eq_norm_sq]
      have h := (norm_sub_le (ginibreCoordinateDirection q j)
        (ginibreCoordinateDirection q k)).trans (add_le_add (hd q j) (hd q k))
      nlinarith [norm_nonneg (ginibreCoordinateDirection q j-ginibreCoordinateDirection q k)]
    _ = _ := by simp; ring

theorem correspondenceCollisionCutoff_one_gradient_zero {n : ℕ} (j k : Fin n)
    {ε : ℝ} (hε : 0 < ε) (z : Configuration n) (hz : 2 * ε ≤ ‖z j - z k‖) :
    correspondenceCollisionCutoff j k ε z = 1 ∧
      ginibreEuclideanGradient (correspondenceCollisionCutoff j k ε) z = 0 := by
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hsq : 4 * ε^2 ≤ Complex.normSq (z j-z k) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [(sq_le_sq₀ (by positivity : 0 ≤ 2*ε) (norm_nonneg _)).mpr hz]
  have ht : Complex.normSq (z j-z k)/ε^2 ∉ tsupport (sobolevCutoffBump : ℝ → ℝ) := by
    rw [sobolevCutoffBump.tsupport_eq]
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, sobolevCutoffBump]
    rw [abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) he2.le)]
    have hdiv := (le_div_iff₀ he2).mpr hsq
    linarith
  constructor
  · simp [correspondenceCollisionCutoff, image_eq_zero_of_notMem_tsupport ht]
  · rw [correspondenceCollisionCutoff_gradient, deriv_of_notMem_tsupport ht]
    simp

/-- Uniform inverse-width bound for the genuine ordinary gradient. -/
theorem correspondenceCollisionCutoff_gradient_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j k : Fin n) (ε : ℝ), 0 < ε →
      ∀ z, ‖ginibreEuclideanGradient (correspondenceCollisionCutoff j k ε) z‖^2 ≤ C/ε^2 := by
  obtain ⟨M, hM0, hM⟩ := sobolevCutoff_deriv_bound
  refine ⟨64 * n * M^2, by positivity, ?_⟩
  intro j k ε hε z
  have he : ε ≠ 0 := hε.ne'
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  let a := Complex.normSq (z j-z k)/ε^2
  by_cases ht : a ∈ tsupport (sobolevCutoffBump : ℝ → ℝ)
  · have ha : Complex.normSq (z j-z k) ≤ 2*ε^2 := by
      rw [sobolevCutoffBump.tsupport_eq] at ht
      have hab : |a| ≤ 2 := by
        simpa [Metric.mem_closedBall, Real.dist_eq, sobolevCutoffBump] using ht
      exact (div_le_iff₀ he2).mp ((le_abs_self a).trans hab)
    have hdf : deriv (sobolevCutoffBump : ℝ → ℝ) a ^ 2 ≤ M^2 := by
      have hb : |deriv (sobolevCutoffBump : ℝ → ℝ) a| ≤ M := by
        simpa [sobolevCutoff_deriv] using hM 0 a
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM0).mpr hb
    have hf : ContDiff ℝ ∞ (fun w : Configuration n => w j-w k) :=
      ContDiff.sub (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).contDiff
        (ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ).contDiff
    have hG : ‖ginibreEuclideanGradient
        (fun w : Configuration n => Complex.normSq (w j-w k)) z‖^2 ≤ 64*n*ε^2 := by
      calc
        _ ≤ 4*Complex.normSq (z j-z k)*complexDirectionalEnergy (fun w => w j-w k) z :=
          ginibreEuclideanGradient_complex_normSq_bound _ hf z
        _ ≤ 4*Complex.normSq (z j-z k)*(8*n) :=
          mul_le_mul_of_nonneg_left (pair_directional_energy_bound j k z)
            (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
        _ ≤ 4*(2*ε^2)*(8*n) := by gcongr
        _ = _ := by ring
    rw [correspondenceCollisionCutoff_gradient, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, div_pow, neg_sq]
    change deriv (sobolevCutoffBump : ℝ → ℝ) a ^ 2 / (ε^2)^2 * _ ≤ _
    calc
      _ ≤ M^2/(ε^2)^2 * (64*n*ε^2) := by gcongr
      _ = _ := by field_simp
  · rw [correspondenceCollisionCutoff_gradient]
    change ‖(-deriv (sobolevCutoffBump : ℝ → ℝ) a / ε^2) • _‖^2 ≤ _
    rw [deriv_of_notMem_tsupport ht]
    simp only [neg_zero, zero_div, zero_smul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    positivity

end
end GinibrePoincare


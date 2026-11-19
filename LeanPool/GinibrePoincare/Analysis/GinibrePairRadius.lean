/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePairRadius.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreSpatialCutoffs
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Actual derivatives of the combined squared radius of two coordinates -/

@[expose] public section

open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

/-- Squared distance to the set where both selected coordinates vanish. -/
def ginibrePairRadiusSq {n : ℕ} (i j : Fin n) (z : Configuration n) : ℝ :=
  Complex.normSq (z i) + Complex.normSq (z j)

/-- The actual real-linear derivative of one coordinate's squared radius. -/
def coordinateRadiusDerivative {n : ℕ} (z : Configuration n) (i : Fin n) :
    Configuration n →L[ℝ] ℝ :=
  (2 * (z i).re) • (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    (2 * (z i).im) • (Complex.imCLM.comp (ContinuousLinearMap.proj i))

theorem hasFDerivAt_coordinateNormSq {n : ℕ} (z : Configuration n) (i : Fin n) :
    HasFDerivAt (fun w : Configuration n => Complex.normSq (w i))
      (coordinateRadiusDerivative z i) z := by
  have hr := Complex.reCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  convert! (hr.mul hr).add (hi.mul hi) using 1
  ext v
  simp [coordinateRadiusDerivative]
  ring

theorem contDiff_coordinateNormSq (n : ℕ) (i : Fin n) :
    ContDiff ℝ ∞ (fun z : Configuration n => Complex.normSq (z i)) := by
  have hr : ContDiff ℝ ∞ (fun z : Configuration n => (z i).re) := Complex.reCLM.contDiff.comp
    (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
  have hi : ContDiff ℝ ∞ (fun z : Configuration n => (z i).im) := Complex.imCLM.contDiff.comp
    (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
  simpa only [Complex.normSq_apply] using (hr.mul hr).add (hi.mul hi)

theorem contDiff_ginibrePairRadiusSq {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (ginibrePairRadiusSq i j) :=
  (contDiff_coordinateNormSq n i).add (contDiff_coordinateNormSq n j)

theorem ginibrePairRadiusSq_nonneg {n : ℕ} (i j : Fin n) (z : Configuration n) :
    0 ≤ ginibrePairRadiusSq i j z :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem ginibrePairRadiusSq_eq_zero_iff {n : ℕ} (i j : Fin n) (z : Configuration n) :
    ginibrePairRadiusSq i j z = 0 ↔ z i = 0 ∧ z j = 0 := by
  rw [ginibrePairRadiusSq, add_eq_zero_iff_of_nonneg (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _), Complex.normSq_eq_zero, Complex.normSq_eq_zero]

theorem ginibrePairRadiusSq_gradient_real {n : ℕ} (i j k : Fin n) (z : Configuration n) :
    ginibreEuclideanGradient (ginibrePairRadiusSq i j) z (k, 0) =
      (if k = i then 2 * (z i).re else 0) + (if k = j then 2 * (z j).re else 0) := by
  rw [ginibreEuclideanGradient_coordinate,
    show ginibrePairRadiusSq i j = (fun w : Configuration n => Complex.normSq (w i)) +
      (fun w : Configuration n => Complex.normSq (w j)) from rfl,
    ((hasFDerivAt_coordinateNormSq z i).add (hasFDerivAt_coordinateNormSq z j)).fderiv]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [coordinateRadiusDerivative, ginibreCoordinateDirection, realCoordinateDirection,
      coordinateDirection, eq_comm, hi, hj]

theorem ginibrePairRadiusSq_gradient_imag {n : ℕ} (i j k : Fin n) (z : Configuration n) :
    ginibreEuclideanGradient (ginibrePairRadiusSq i j) z (k, 1) =
      (if k = i then 2 * (z i).im else 0) + (if k = j then 2 * (z j).im else 0) := by
  rw [ginibreEuclideanGradient_coordinate,
    show ginibrePairRadiusSq i j = (fun w : Configuration n => Complex.normSq (w i)) +
      (fun w : Configuration n => Complex.normSq (w j)) from rfl,
    ((hasFDerivAt_coordinateNormSq z i).add (hasFDerivAt_coordinateNormSq z j)).fderiv]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [coordinateRadiusDerivative, ginibreCoordinateDirection, imaginaryCoordinateDirection,
      coordinateDirection, eq_comm, hi, hj]

/-- Distinct coordinate blocks are orthogonal in the actual Euclidean gradient. -/
theorem ginibrePairRadiusSq_gradient_norm_sq {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (z : Configuration n) :
    ‖ginibreEuclideanGradient (ginibrePairRadiusSq i j) z‖ ^ 2 =
      4 * ginibrePairRadiusSq i j z := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    ginibrePairRadiusSq_gradient_real, ginibrePairRadiusSq_gradient_imag,
    Real.norm_eq_abs, sq_abs]
  have he (k : Fin n) :
      ((if k = i then 2 * (z i).re else 0) + (if k = j then 2 * (z j).re else 0)) ^ 2 +
      ((if k = i then 2 * (z i).im else 0) + (if k = j then 2 * (z j).im else 0)) ^ 2 =
      (if k = i then 4 * Complex.normSq (z i) else 0) +
        (if k = j then 4 * Complex.normSq (z j) else 0) := by
    by_cases hi : k = i
    · subst k; simp [hij, Complex.normSq_apply]; ring
    · by_cases hj : k = j
      · subst k; simp [hij.symm, Complex.normSq_apply]; ring
      · simp [hi, hj]
  simp_rw [he]
  simp [Finset.sum_add_distrib, ginibrePairRadiusSq]
  ring

end
end GinibrePoincare

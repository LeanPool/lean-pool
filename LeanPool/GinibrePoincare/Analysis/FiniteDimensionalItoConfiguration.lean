/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoConfiguration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoCoordinates
public import LeanPool.GinibrePoincare.Analysis.GaussianFourierCoordinates
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Finite dimensional Ito configuration

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoConfigurationHessian_coordinate_sum`,
`itoConfiguration_norm_sq_le_coordinate_sum`, `itoConfigurationHessian_trace`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section

/-- Actual real-coordinate expansion of a complex configuration increment. -/
theorem itoConfigurationIncrement_expansion {n : ℕ} (h : Configuration n) :
    h = ∑ i : Fin n × Fin 2,
      configurationEuclideanLinearEquiv n h i • ginibreCoordinateDirection i := by
  ext k
  rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single k]
  · apply Complex.ext <;> simp [Fin.sum_univ_two, configurationEuclideanLinearEquiv,
      ginibreCoordinateDirection, realCoordinateDirection, imaginaryCoordinateDirection,
      coordinateDirection]
  · intro j _ hjk
    simp [Fin.sum_univ_two, ginibreCoordinateDirection, realCoordinateDirection,
      imaginaryCoordinateDirection, coordinateDirection, Ne.symm hjk]
  · simp

/-- The actual Hessian coordinate coefficient in the paper's configuration directions. -/
def itoConfigurationHessianEntry {n : ℕ} (f : Configuration n → ℝ)
    (x : Configuration n) (i j : Fin n × Fin 2) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x (ginibreCoordinateDirection i) (ginibreCoordinateDirection j)

theorem itoConfigurationHessian_coordinate_sum {n : ℕ} (f : Configuration n → ℝ)
    (x h : Configuration n) :
    itoDirectionalHessian f x h = ∑ i : Fin n × Fin 2, ∑ j : Fin n × Fin 2,
      configurationEuclideanLinearEquiv n h i * configurationEuclideanLinearEquiv n h j *
        itoConfigurationHessianEntry f x i j := by
  unfold itoDirectionalHessian
  rw [iteratedFDeriv_two_apply]
  conv_lhs => rw [itoConfigurationIncrement_expansion h]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    itoConfigurationHessianEntry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual configuration norm is controlled by all actual real coordinates. -/
theorem itoConfiguration_norm_sq_le_coordinate_sum {n : ℕ} (h : Configuration n) :
    ‖h‖^2 ≤ ∑ i : Fin n × Fin 2, (configurationEuclideanLinearEquiv n h i)^2 := by
  let S : ℝ := ∑ i : Fin n, ‖h i‖^2
  have hs : 0 ≤ S := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hb : ‖h‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j : Fin n => ‖h j‖^2)
      (fun j hj => sq_nonneg _) (Finset.mem_univ i)
  have hsq : ‖h‖^2 ≤ S := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (Real.sq_sqrt hs)
  convert hsq using 1
  unfold S
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, configurationEuclideanLinearEquiv,
    Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]

/-- The Hessian trace is exactly the concrete configuration Laplacian. -/
theorem itoConfigurationHessian_trace {n : ℕ} (f : Configuration n → ℝ)
    (x : Configuration n) (hf : ContDiffAt ℝ 2 f x) :
    ∑ i : Fin n × Fin 2, itoConfigurationHessianEntry f x i i =
      configurationLaplacian f x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (v : Configuration n) : secondDirectionalDerivative f v x =
      fderiv ℝ (fderiv ℝ f) x v v := by
    unfold secondDirectionalDerivative
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, itoConfigurationHessianEntry,
    configurationLaplacian, he, ginibreCoordinateDirection, ite_true]
  simp

end
end GinibrePoincare

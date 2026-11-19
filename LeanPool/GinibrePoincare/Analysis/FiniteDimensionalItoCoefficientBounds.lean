/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoCoefficientBounds.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoConfiguration
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Coordinate derivative bounds under compact localization

Each real or imaginary configuration coordinate direction has norm one.
The gradient coefficients and Hessian entries are evaluations of the first
and second Fréchet derivatives on these directions, so C² regularity on
an open domain gives their continuity there.

Compactness bounds the operator norms of both derivatives. Evaluating on
unit directions converts those bounds into one nonnegative constant valid
for every coordinate and every point in the compact set. The diagonal
Hessian sum identifies the configuration Laplacian, yielding its continuity
and a compact bound as well. No extension of the test across the complement
of the open domain is required. -/

@[expose] public section

open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Actual coordinate directions have unit norm. -/
theorem itoConfigurationDirection_norm {n : ℕ} (i : Fin n × Fin 2) :
    ‖ginibreCoordinateDirection i‖ = 1 := by
  have hn (w : ℂ) : ‖GinibrePoincare.coordinateDirection i.1 w‖ = ‖w‖ := by
    have he : GinibrePoincare.coordinateDirection i.1 w = Pi.single i.1 w := by
      ext j
      simp [GinibrePoincare.coordinateDirection, Pi.single_apply]
    rw [he, Pi.norm_single]
  unfold ginibreCoordinateDirection
  split_ifs
  · change ‖GinibrePoincare.coordinateDirection i.1 1‖ = 1
    rw [hn]
    exact norm_one
  · change ‖GinibrePoincare.coordinateDirection i.1 Complex.I‖ = 1
    rw [hn]
    exact Complex.norm_I

/-- Actual local C² Hessian entries are continuous on their original open domain. -/
theorem itoConfigurationHessianEntry_continuousOn {n : ℕ} (f : Configuration n → ℝ)
    (U : Set (Configuration n)) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (i j : Fin n × Fin 2) : ContinuousOn (fun x => itoConfigurationHessianEntry f x i j) U := by
  have hc := (continuous_eval_const ![ginibreCoordinateDirection i, ginibreCoordinateDirection
      j]).comp_continuousOn
    (ContinuousOn.continuousOn_iteratedFDeriv (k := 2) hf hU (by norm_num))
  simpa only [Function.comp_def, itoConfigurationHessianEntry, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hc

/-- Actual local C² gradient coordinate coefficients are continuous. -/
theorem itoConfigurationGradientEntry_continuousOn {n : ℕ} (f : Configuration n → ℝ)
    (U : Set (Configuration n)) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (i : Fin n × Fin 2) : ContinuousOn (fun x => fderiv ℝ f x (ginibreCoordinateDirection i)) U :=
        by
  exact (continuous_eval_const (ginibreCoordinateDirection i)).comp_continuousOn
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num))

/-- Genuine compact localization bounds every gradient and Hessian coordinate
of the actual test, uniformly over all coordinates. -/
theorem itoConfigurationCoefficients_exists_bound {n : ℕ} (f : Configuration n → ℝ)
    (U K : Set (Configuration n)) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K,
      (∀ i : Fin n × Fin 2, ‖fderiv ℝ f x (ginibreCoordinateDirection i)‖ ≤ C) ∧
      (∀ i j : Fin n × Fin 2, ‖itoConfigurationHessianEntry f x i j‖ ≤ C) := by
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
    ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := 2) hf hU (by norm_num)).mono hKU)
  refine ⟨max (max A B) 0, le_max_right _ _, fun x hx => ⟨?_,?_⟩⟩
  · intro i
    have he := (fderiv ℝ f x).le_opNorm (ginibreCoordinateDirection i)
    rw [itoConfigurationDirection_norm, mul_one] at he
    exact he.trans ((hA x hx).trans ((le_max_left A B).trans (le_max_left _ _)))
  · intro i j
    have he := (iteratedFDeriv ℝ 2 f x).le_opNorm
      ![ginibreCoordinateDirection i, ginibreCoordinateDirection j]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      itoConfigurationDirection_norm, mul_one, iteratedFDeriv_two_apply] at he
    exact he.trans ((hB x hx).trans ((le_max_right A B).trans (le_max_left _ _)))

/-- The actual local configuration Laplacian is continuous, without requiring
a smooth extension across the collision set. -/
theorem itoConfigurationLaplacian_continuousOn {n : ℕ} (f : Configuration n → ℝ)
    (U : Set (Configuration n)) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (configurationLaplacian f) U := by
  have hc : ContinuousOn (fun x => ∑ i : Fin n × Fin 2, itoConfigurationHessianEntry f x i i) U :=
    continuousOn_finsetSum _ (fun i hi => itoConfigurationHessianEntry_continuousOn f U hU hf i i)
  apply hc.congr
  intro x hx
  exact (itoConfigurationHessian_trace f x (hf.contDiffAt (hU.mem_nhds hx))).symm

/-- The actual Laplacian is uniformly bounded on any compact subset of its C² domain. -/
theorem itoConfigurationLaplacian_exists_bound {n : ℕ} (f : Configuration n → ℝ)
    (U K : Set (Configuration n)) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, ∀ x ∈ K, ‖configurationLaplacian f x‖ ≤ C :=
  hK.exists_bound_of_continuousOn ((itoConfigurationLaplacian_continuousOn f U hU hf).mono hKU)

end
end GinibrePoincare

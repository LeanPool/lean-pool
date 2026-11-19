/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevMultiplierL2.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Genuine L² Leibniz pairs under arbitrary weighted laws -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace GinibrePoincare
noncomputable section

theorem configuration_weak_multiplier_memLp (n : ℕ)
    (μ : Measure (Configuration n)) (u : Configuration n → ℝ)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    MemLp (fun z => χ z * u z) 2 μ ∧
    MemLp (fun z => χ z • g z + u z • ginibreEuclideanGradient χ z)
      2 μ := by
  obtain ⟨A, hA⟩ := hχ.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (continuous_ginibreEuclideanGradient χ hχ).bounded_above_of_compact_support
    (compactSupport_ginibreEuclideanGradient χ hc)
  have hA0 : 0 ≤ A := (norm_nonneg (χ 0)).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg (ginibreEuclideanGradient χ 0)).trans (hB 0)
  have hv : MemLp (fun z => χ z * u z) 2 μ := by
    apply (hu.const_mul A).of_le
      (hχ.continuous.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖χ z * u z‖ ≤ ‖A * u z‖
      rw [norm_mul, norm_mul, Real.norm_eq_abs A, abs_of_nonneg hA0]
      exact mul_le_mul_of_nonneg_right (hA z) (norm_nonneg (u z)))
  have hvG : MemLp (fun z => χ z • g z) 2 μ := by
    apply (hg.const_smul A).of_le
      (hχ.continuous.aestronglyMeasurable.smul hg.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖χ z • g z‖ ≤ ‖A • g z‖
      rw [norm_smul, norm_smul, Real.norm_eq_abs A, abs_of_nonneg hA0]
      exact mul_le_mul_of_nonneg_right (hA z) (norm_nonneg (g z)))
  have hdG : MemLp (fun z => u z • ginibreEuclideanGradient χ z) 2 μ := by
    apply (hu.const_mul B).of_le
      (hu.aestronglyMeasurable.smul (continuous_ginibreEuclideanGradient χ hχ).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖u z • ginibreEuclideanGradient χ z‖ ≤ ‖B * u z‖
      rw [norm_smul, norm_mul, Real.norm_eq_abs B, abs_of_nonneg hB0]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB z) (norm_nonneg (u z)))
  exact ⟨hv, hvG.add hdG⟩

end
end GinibrePoincare

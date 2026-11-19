/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevSpatialTruncation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevTruncation
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # Actual simultaneous spatial truncation under arbitrary weighted laws -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem configurationSpatialCutoff_L2_errors_tendsto (n : ℕ)
    (μ : Measure (Configuration n))
    (u : Configuration n → ℝ)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) :
    Tendsto (fun m => ∫ z, (ginibreSpatialCutoff n m z * u z - u z) ^ 2
      ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun m => ∫ z,
      ‖ginibreSpatialCutoff n m z • g z +
        u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z - g z‖ ^ 2
      ∂μ) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := ginibreSpatialCutoff_gradient_bound
  have hdb (m : ℕ) (z : Configuration n) :
      ‖ginibreEuclideanGradient (ginibreSpatialCutoff n m) z‖ ^ 2 ≤ C :=
    (hC n m z).trans (div_le_self hC0 (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
  have hb (m : ℕ) (z : Configuration n) : (ginibreSpatialCutoff n m z - 1) ^ 2 ≤ 1 := by
    obtain ⟨h0, h1⟩ := ginibreSpatialCutoff_mem_unit n m z
    nlinarith
  constructor
  · have ht := tendsto_integral_of_dominated_convergence (fun z => u z ^ 2)
      (fun m => (((ginibreSpatialCutoff_smooth n m).continuous.aestronglyMeasurable.mul
          hu.aestronglyMeasurable).sub
        hu.aestronglyMeasurable).pow 2)
      hu.integrable_sq
      (fun m => ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (ginibreSpatialCutoff n m z * u z - u z) ^ 2 ≤ u z ^ 2
        have he : (ginibreSpatialCutoff n m z * u z - u z) ^ 2 =
            (ginibreSpatialCutoff n m z - 1) ^ 2 * u z ^ 2 := by ring
        rw [he]
        simpa using mul_le_mul_of_nonneg_right (hb m z) (sq_nonneg (u z))))
      (ae_of_all _ (fun z => by
        simpa using (((ginibreSpatialCutoff_tendsto n z).mul_const (u z)).sub_const (u z)).pow 2))
    simpa using ht
  · have hbound (m : ℕ) (z : Configuration n) :
        ‖ginibreSpatialCutoff n m z • g z +
          u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z - g z‖ ^ 2 ≤
          2 * ‖g z‖ ^ 2 + 2 * C * u z ^ 2 := by
      let a := (ginibreSpatialCutoff n m z - 1) • g z
      let b := u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z
      have he : ginibreSpatialCutoff n m z • g z +
          u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z - g z = a + b := by
        dsimp [a, b]
        rw [sub_smul, one_smul]
        abel
      have ha : ‖a‖ ^ 2 ≤ ‖g z‖ ^ 2 := by
        dsimp [a]
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        simpa using mul_le_mul_of_nonneg_right (hb m z) (sq_nonneg ‖g z‖)
      have hb' : ‖b‖ ^ 2 ≤ C * u z ^ 2 := by
        dsimp [b]
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hdb m z) (sq_nonneg (u z))
      rw [he]
      have hadd := norm_add_le a b
      have hsum : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
        nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    have hmeas (m : ℕ) : AEStronglyMeasurable (fun z =>
        ‖ginibreSpatialCutoff n m z • g z +
          u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z - g z‖ ^ 2)
        μ :=
      ((((ginibreSpatialCutoff_smooth n m).continuous.aestronglyMeasurable.smul
          hg.aestronglyMeasurable).add
        (hu.aestronglyMeasurable.smul (continuous_ginibreEuclideanGradient _
          (ginibreSpatialCutoff_smooth n m)).aestronglyMeasurable)).sub
              hg.aestronglyMeasurable).norm.pow 2
    have hlim (z : Configuration n) : Tendsto (fun m =>
        ‖ginibreSpatialCutoff n m z • g z +
          u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z - g z‖ ^ 2)
        atTop (𝓝 0) := by
      have ht := (((ginibreSpatialCutoff_tendsto n z).smul_const (g z)).add
        ((ginibreSpatialCutoff_gradient_tendsto n z).const_smul (u z))).sub_const (g z)
      simpa using ht.norm.pow 2
    have hgint : Integrable (fun z => ‖g z‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
    have hdom : Integrable (fun z => 2 * ‖g z‖ ^ 2 + 2 * C * u z ^ 2) μ :=
      (hgint.const_mul (2 : ℝ)).add (hu.integrable_sq.const_mul (2 * C))
    have ht := tendsto_integral_of_dominated_convergence
      (fun z => 2 * ‖g z‖ ^ 2 + 2 * C * u z ^ 2) hmeas hdom
      (fun m => ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound m z))
      (ae_of_all _ hlim)
    simpa using ht

end
end GinibrePoincare

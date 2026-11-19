/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevSpatialPairs.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevMultiplierL2
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevSpatialTruncation

/-! # Concrete weighted spatial graph truncations and their strong convergence -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The product rule for a weak value–gradient pair `(u, g)` and a smooth compactly supported
multiplier `χ`: the pair `(χ u, χ g + u ∇χ)` in `L²(μ)`. -/
def configurationWeakMultiplierPair (n : ℕ) (μ : Measure (Configuration n))
    (u : Lp ℝ 2 μ) (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 μ)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    Lp ℝ 2 μ × Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 μ :=
  (((configuration_weak_multiplier_memLp n μ u g (Lp.memLp u) (Lp.memLp g) χ hχ hc).1).toLp
    (fun z => χ z * u z),
   ((configuration_weak_multiplier_memLp n μ u g (Lp.memLp u) (Lp.memLp g) χ hχ hc).2).toLp
    (fun z => χ z • g z + u z • ginibreEuclideanGradient χ z))

/-- The weak value–gradient pair `(u, g)` multiplied by the `m`-th spatial cutoff
`ginibreSpatialCutoff n m`. -/
def configurationWeakSpatialTruncation (n : ℕ) (μ : Measure (Configuration n))
    (u : Lp ℝ 2 μ)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 μ) (m : ℕ) :
    Lp ℝ 2 μ ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 μ :=
  configurationWeakMultiplierPair n μ u g (ginibreSpatialCutoff n m)
    (ginibreSpatialCutoff_smooth n m) (ginibreSpatialCutoff_compact n m)

theorem configurationWeakSpatialTruncation_value_ae (n : ℕ) (μ : Measure (Configuration n))
    (u : Lp ℝ 2 μ)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 μ) (m : ℕ) :
    ((configurationWeakSpatialTruncation n μ u g m).1 : Configuration n → ℝ)
      =ᵐ[μ] fun z => ginibreSpatialCutoff n m z * u z :=
  (configuration_weak_multiplier_memLp n μ u g (Lp.memLp u) (Lp.memLp g) _
      (ginibreSpatialCutoff_smooth n m)
    (ginibreSpatialCutoff_compact n m)).1.coeFn_toLp

theorem configurationWeakSpatialTruncation_gradient_ae (n : ℕ) (μ : Measure (Configuration n))
    (u : Lp ℝ 2 μ)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 μ) (m : ℕ) :
    ((configurationWeakSpatialTruncation n μ u g m).2 :
      Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[μ]
      fun z => ginibreSpatialCutoff n m z • g z +
        u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z :=
  (configuration_weak_multiplier_memLp n μ u g (Lp.memLp u) (Lp.memLp g) _
      (ginibreSpatialCutoff_smooth n m)
    (ginibreSpatialCutoff_compact n m)).2.coeFn_toLp

theorem configurationWeakSpatialTruncation_tendsto (n : ℕ) (μ : Measure (Configuration n))
    (u : Lp ℝ 2 μ)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 μ) :
    Tendsto (configurationWeakSpatialTruncation n μ u g) atTop (𝓝 (u, g)) := by
  have ht := configurationSpatialCutoff_L2_errors_tendsto n μ u g (Lp.memLp u) (Lp.memLp g)
  have hv : Tendsto (fun m => (configurationWeakSpatialTruncation n μ u g m).1) atTop (𝓝 u) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have he (m : ℕ) : dist (configurationWeakSpatialTruncation n μ u g m).1 u =
        Real.sqrt (∫ z, (ginibreSpatialCutoff n m z * u z - u z) ^ 2 ∂μ) := by
      rw [L2_dist_eq_sqrt_integral_norm_error]
      congr 1
      apply integral_congr_ae
      filter_upwards [configurationWeakSpatialTruncation_value_ae n μ u g m] with z hz
      rw [hz, Real.norm_eq_abs, sq_abs]
    simp_rw [he]
    simpa using ht.1.sqrt
  have hg : Tendsto (fun m => (configurationWeakSpatialTruncation n μ u g m).2) atTop (𝓝 g) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have he (m : ℕ) : dist (configurationWeakSpatialTruncation n μ u g m).2 g =
        Real.sqrt (∫ z, ‖ginibreSpatialCutoff n m z • g z +
          u z • ginibreEuclideanGradient (ginibreSpatialCutoff n m) z - g z‖ ^ 2
          ∂μ) := by
      rw [L2_dist_eq_sqrt_integral_norm_error]
      congr 1
      apply integral_congr_ae
      filter_upwards [configurationWeakSpatialTruncation_gradient_ae n μ u g m] with z hz
      rw [hz]
    simp_rw [he]
    simpa using ht.2.sqrt
  exact hv.prodMk_nhds hg

end
end GinibrePoincare

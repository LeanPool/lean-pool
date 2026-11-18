/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupConstants.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakPermutation

/-! # Constant Ginibre values have zero weak gradients -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped BigOperators ContDiff

/-- The constant function `c`, represented in actual Ginibre `L²`. -/
def ginibreRealConstantL2 (n : ℕ) (hn : 0 < n) (c : ℝ) :
    Lp ℝ 2 (ginibreMeasure n) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  exact (memLp_const c : MemLp (fun _ : Configuration n => c)
    2 (ginibreMeasure n)).toLp (fun _ => c)

theorem ginibreRealConstantL2_ae (n : ℕ) (hn : 0 < n) (c : ℝ) :
    (ginibreRealConstantL2 n hn c : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun _ => c := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (memLp_const c : MemLp (fun _ : Configuration n => c)
    2 (ginibreMeasure n)).coeFn_toLp

/-- Mean of an actual Ginibre `L²` class. -/
def ginibreL2Mean (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n)) : ℝ :=
  ∫ z, u z ∂ginibreMeasure n

theorem ginibreL2Mean_continuous (n : ℕ) (hn : 0 < n) :
    Continuous (ginibreL2Mean n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have h1 : MemLp (fun _ : Configuration n => (1 : ℝ)) 2 (ginibreMeasure n) :=
    memLp_const 1
  have h := continuous_L2_integral_mul (ginibreMeasure n)
    (fun _ : Configuration n => (1 : ℝ)) h1
  have heq : ginibreL2Mean n = fun u => ∫ z, u z * 1 ∂ginibreMeasure n := by
    funext u
    unfold ginibreL2Mean
    congr 1
    funext z
    ring
  rw [heq]
  exact h

/-- Every actual real constant has the ordinary zero weak gradient. -/
theorem ginibreRealConstantL2_weak (n : ℕ) (hn : 0 < n) (c : ℝ) :
    IsGinibreDistributionalGradient n (ginibreRealConstantL2 n hn c) 0 := by
  apply ginibre_smooth_distributional_gradient n hn _ _ (fun _ => c) contDiff_const
    (ginibreRealConstantL2_ae n hn c)
  filter_upwards [Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin n × Fin 2))
    (p := (2 : ENNReal)) (μ := ginibreMeasure n)] with z hz
  rw [hz]
  ext k
  simp [ginibreEuclideanGradient]

/-- The constant weak pair is genuinely permutation invariant. -/
theorem ginibreRealConstantL2_symmetric_pair (n : ℕ) (hn : 0 < n) (c : ℝ) :
    IsGinibreSymmetricWeakPair (ginibreRealConstantL2 n hn c, 0) := by
  intro σ
  constructor
  · apply Lp.ext
    have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
      (ginibreRealConstantL2_ae n hn c)
    filter_upwards [ginibreRealPermutationL2_ae σ (ginibreRealConstantL2 n hn c),
      hcomp, ginibreRealConstantL2_ae n hn c] with z hp hc hu
    simp only [Function.comp_apply] at hc
    rw [hp, hc, hu]
  · exact map_zero _

end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCurvatureNegativeTest.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCurvatureLinear
/-!
# Correspondence curvature negative test

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondence_pointwise_deficit_negative_compact_test`.
-/

@[expose] public section
open Set Filter Metric
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section

/-- A literal smooth compact collision-free test witnesses failure of
pointwise positivity of the deficit in (1.43), in every n≥2. -/
theorem correspondence_pointwise_deficit_negative_compact_test {n : ℕ} (hn : 2 ≤ n) :
    ∃ (f : Configuration n → ℝ) (z : Configuration n),
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z} ∧
        CollisionFree z ∧ ginibrePointwiseGammaTwo n f z - 2*ginibrePointwiseGamma n f f z < 0 := by
  obtain ⟨z, hz, j, _, hneg⟩ := ginibreHamiltonian_pointwise_curvature_unbounded_below hn 0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_collisionFree n) z hz
  let φ : ContDiffBump z := ⟨r/4, r/2, by positivity, by linarith⟩
  let L := correspondenceImaginaryCoordinate j
  let f : Configuration n → ℝ := fun x => φ x*L x
  have hf : ContDiff ℝ ∞ f := φ.contDiff.mul L.contDiff
  have hfc : HasCompactSupport f := φ.hasCompactSupport.mul_right
  have hfs : tsupport f ⊆ {z | CollisionFree z} := by
    apply tsupport_mul_subset_left.trans
    rw [φ.tsupport_eq]
    intro x hx
    apply hball
    apply mem_ball.mpr
    have hx' := mem_closedBall.mp hx
    change dist x z ≤ r/2 at hx'
    linarith
  have he : f =ᶠ[𝓝 z] L := by
    filter_upwards [Metric.ball_mem_nhds z (by positivity : 0<r/4)] with x hx
    change φ x*L x = L x
    rw [φ.one_of_mem_closedBall (mem_closedBall.mpr (le_of_lt (mem_ball.mp hx))), one_mul]
  have hg : ginibreBochnerGradient f z = imaginaryCoordinateDirection j := by
    rw [← correspondenceImaginaryCoordinate_gradient j z]
    unfold ginibreBochnerGradient bochnerDirectionalDerivative
    rw [he.fderiv_eq]
  have hh : ginibreBochnerHessianSquare f z = 0 := by
    unfold ginibreBochnerHessianSquare
    rw [(he.fderiv (𝕜 := ℝ)).fderiv_eq]
    simp [L, correspondenceImaginaryCoordinate_hessian]
  have hn0 : 0<n := by omega
  have hB := ginibrePointwiseGammaTwo_bochner_bilinear hn0 f hf z hz
  rw [hg, hh, zero_add] at hB
  have hN : fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z
      (imaginaryCoordinateDirection j) (imaginaryCoordinateDirection j) < 0 := by
    rw [← bochnerDirectionalDerivative_iterated _ _ _ _ (ginibreHamiltonian_contDiffAt n z hz)]
    exact hneg
  have hpos : 0 < (n : ℝ)^2 := by positivity
  have hGN : 0 ≤ ginibrePointwiseGamma n f f z := by
    rw [ginibrePointwiseGamma_eq hn0 f f hf hf z hz]
    simp only [← pow_two]
    positivity
  refine ⟨f, z, hf, hfc, hfs, hz,?_⟩
  have htwo : ginibrePointwiseGammaTwo n f z < 0 := by nlinarith [hB, hN]
  linarith

end
end GinibrePoincare

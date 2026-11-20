/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCurvatureGradient.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseBochner
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential
/-!
# Correspondence curvature gradient

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceGamma_gradient_normSq`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section

theorem correspondenceBochnerGradient_coordinate {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) (j : Fin n) :
    ginibreBochnerGradient f z j =
      (bochnerDirectionalDerivative (realCoordinateDirection j) f z : ℂ) +
        Complex.I * (bochnerDirectionalDerivative (imaginaryCoordinateDirection j) f z : ℂ) := by
  simp [Finset.sum_add_distrib, eq_comm, mul_comm, ginibreBochnerGradient, Fintype.sum_prod_type,
      Fin.sum_univ_two,
    ginibreBochnerDirection, realCoordinateDirection, imaginaryCoordinateDirection,
    coordinateDirection, Complex.real_smul]

theorem correspondenceBochnerGradient_normSq {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) :
    configurationNormSq (ginibreBochnerGradient f z) =
      ∑ i : Fin n × Fin 2, (bochnerDirectionalDerivative (ginibreBochnerDirection i) f z)^2 := by
  simp only [configurationNormSq, correspondenceBochnerGradient_coordinate,
    Fintype.sum_prod_type, Fin.sum_univ_two, ginibreBochnerDirection]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]

theorem correspondenceGamma_gradient_normSq {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) (hz : CollisionFree z) :
    (n : ℝ)*ginibrePointwiseGamma n f f z = configurationNormSq (ginibreBochnerGradient f z) := by
  rw [ginibrePointwiseGamma_eq hn f f hf hf z hz, correspondenceBochnerGradient_normSq]
  simp only [← pow_two]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

end
end GinibrePoincare

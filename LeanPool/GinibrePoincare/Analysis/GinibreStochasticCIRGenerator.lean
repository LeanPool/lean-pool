/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCIRGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalTestIto
public import LeanPool.GinibrePoincare.Analysis.GinibreDynamicsGenerator

/-! # Smooth radius tests and CIR drift coefficients

The radius is a quadratic polynomial in configuration coordinates, so it is
smooth on the whole configuration space. Its generator identities are
needed only on the collision-free set, where the singular Ginibre generator
is defined by the concrete drift formula.

The linear-radius identity is obtained by taking real parts of the complex
polynomial generator calculation. For the squared radius, the polynomial
carré-du-champ identity supplies the additional `8 * α / n * radius` term.
Together these formulas identify the drift and squared diffusion amplitude
used in the stochastic CIR realization. -/

@[expose] public section
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibre_contDiff_center_normSq (n : ℕ) :
    ContDiff ℝ ∞ (fun z : Configuration n => Complex.normSq (coordinateSum z)) := by
  have hc : ContDiff ℝ ∞ (coordinateSum : Configuration n → ℂ) := by
    simpa only [coordinateSumCLM_apply] using
      (show ContDiff ℝ ∞ (fun z => coordinateSumCLM n z) from (coordinateSumCLM n).contDiff)
  have hr : ContDiff ℝ ∞ (fun z : Configuration n => (coordinateSum z).re) :=
      Complex.reCLM.contDiff.comp hc
  have hi : ContDiff ℝ ∞ (fun z : Configuration n => (coordinateSum z).im) :=
      Complex.imCLM.contDiff.comp hc
  convert! (hr.mul hr).add (hi.mul hi) using 1

theorem ginibre_contDiff_pairwiseRadius (n : ℕ) :
    ContDiff ℝ ∞ (pairwiseRadius : Configuration n → ℝ) := by
  have h := ((contDiff_const : ContDiff ℝ ∞ (fun _ : Configuration n => (n : ℝ))).mul
      (contDiff_configurationNormSq (n := n))).sub
    (ginibre_contDiff_center_normSq n)
  convert! h using 1
  funext z
  exact pairwiseRadius_eq_normSq z

theorem ginibreRealPaperSpeedGenerator_pairwiseRadius {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α pairwiseRadius z =
      (4*α/(n : ℝ))*((recenteredGammaShape n : ℝ)-pairwiseRadius z) := by
  have h := congrArg Complex.re (ginibrePaperSpeedGenerator_radius n hn α z hz)
  simpa [ginibrePaperSpeedGenerator, ginibreRealPaperSpeedGenerator, complexGinibrePregenerator,
    sumRadiusPolynomial, observablePolynomial, sumRadiusCoordinate, complexRadius] using h
theorem ginibreRealPaperSpeedGenerator_pairwiseRadius_square {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (fun w => pairwiseRadius w^2) z =
      2*pairwiseRadius z*((4*α/(n : ℝ))*((recenteredGammaShape n : ℝ)-pairwiseRadius z))+
        (8*α/(n : ℝ))*pairwiseRadius z := by
  have hop : sumRadiusOperator n ((MvPolynomial.X 2)^2) =
      2*MvPolynomial.X 2*(4*MvPolynomial.C (recenteredGammaShape n : ℂ)-4*MvPolynomial.X 2)+
        8*MvPolynomial.X 2 := by
    have h := sumRadiusOperator_radius_carreDuChamp n
    rw [sumRadiusOperator_radius] at h
    linear_combination h
  have h := complexGinibrePregenerator_sumRadiusPolynomial n hn ((MvPolynomial.X 2)^2) z hz
  rw [hop] at h
  have hr := congrArg Complex.re h
  have hb : ginibrePregenerator n (fun w => pairwiseRadius w^2) z =
      2*pairwiseRadius z*(4*(recenteredGammaShape n : ℝ)-4*pairwiseRadius z)+8*pairwiseRadius z :=
          by
    simpa [complexGinibrePregenerator, sumRadiusPolynomial, observablePolynomial,
        sumRadiusCoordinate,
      complexRadius, ← Complex.ofReal_pow] using hr
  rw [ginibreRealPaperSpeedGenerator, hb]
  ring

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialVandermondeGauge.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondePhase
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiSeparatedDerivatives
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar

/-!
# General potential Vandermonde gauge

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermondeCoefficient_weighted`,
`piComplexDbar_potentialVandermondeCoefficient`, `potentialVandermondeCoefficient_contDiff`,
`potentialVandermondeCoefficient_hasCompactSupport`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The function `g` multiplied by `Z^(-1/2) * Δ(z)`, where `Δ` is the Vandermonde determinant
and `Z` the partition function `potentialPartition n V`. -/
def potentialVandermondeCoefficient (n : ℕ) (V : Potential)
    (g : Configuration n → ℂ) (z : Configuration n) : ℂ :=
  ((Real.sqrt (potentialPartition n V).toReal : ℂ)⁻¹) * vandermonde z * g z

theorem potentialPiHalfWeight_eq (n d : ℕ) (V : Potential) (z : Configuration d) :
    (∏ i, planarPotentialHalfWeight n V (z i)) =
      (Real.exp (-(n : ℝ) * (∑ i, V (z i)) / 2) : ℂ) := by
  unfold planarPotentialHalfWeight
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum]

theorem potentialVandermondeCoefficient_weighted (n : ℕ) (V : Potential)
    (g : Configuration n → ℂ) (z : Configuration n) :
    potentialVandermondeCoefficient n V g z * (∏ i, planarPotentialHalfWeight n V (z i)) =
      potentialVandermondeMultiplier n V z * g z := by
  rw [potentialPiHalfWeight_eq]
  unfold potentialVandermondeCoefficient potentialVandermondeMultiplier
  ring

theorem piComplexDbar_eq_dbarComponent {d : ℕ} (i : Fin d)
    (f : Configuration d → ℂ) (z : Configuration d) :
    piComplexDbar i f z = dbarComponent f i z := by
  have he (a : ℂ) : Pi.single i a = coordinateDirection i a := by
    funext j
    simp [Pi.single_apply, coordinateDirection, eq_comm]
  simp only [piComplexDbar, finiteComplexDbar, dbarComponent,
    realCoordinateDirection, imaginaryCoordinateDirection, he]

theorem piComplexDbar_potentialVandermondeCoefficient {n : ℕ} (V : Potential)
    (g : Configuration n → ℂ) (hg : Differentiable ℝ g) (i : Fin n) (z : Configuration n) :
    piComplexDbar i (potentialVandermondeCoefficient n V g) z =
      ((Real.sqrt (potentialPartition n V).toReal : ℂ)⁻¹) * vandermonde z * piComplexDbar i g z :=
          by
  simp only [piComplexDbar_eq_dbarComponent]
  apply dbarComponent_holomorphic_mul
    ((differentiable_vandermonde n).const_mul _) hg

theorem potentialVandermondeCoefficient_contDiff {n : ℕ} (V : Potential)
    (g : Configuration n → ℂ) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (potentialVandermondeCoefficient n V g) :=
  (contDiff_const.mul ((contDiff_vandermonde n).of_le (by norm_num))).mul hg

theorem potentialVandermondeCoefficient_hasCompactSupport {n : ℕ} (V : Potential)
    (g : Configuration n → ℂ) (hg : HasCompactSupport g) :
    HasCompactSupport (potentialVandermondeCoefficient n V g) :=
  hg.mul_left

end
end GinibrePoincare

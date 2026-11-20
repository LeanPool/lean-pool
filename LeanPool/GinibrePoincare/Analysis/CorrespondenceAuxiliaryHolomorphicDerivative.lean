/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryHolomorphicDerivative.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesHolomorphicLowering
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Correspondence auxiliary holomorphic derivative

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `fderiv_holomorphicHermite_coordinate`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem dholComponent_eq_complex_fderiv {n : ℕ} {f : Configuration n → ℂ}
    {z : Configuration n} (hf : DifferentiableAt ℂ f z) (j : Fin n) :
    ComplexHermite.dholComponent f j z = fderiv ℂ f z (realCoordinateDirection j) := by
  have hi : imaginaryCoordinateDirection j = Complex.I • realCoordinateDirection j := by
    funext k
    simp [imaginaryCoordinateDirection, realCoordinateDirection, coordinateDirection, Pi.smul_apply]
  unfold ComplexHermite.dholComponent
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1/2 : ℂ)*((fderiv ℂ f z) (realCoordinateDirection j) -
    Complex.I * (fderiv ℂ f z) (imaginaryCoordinateDirection j)) = _
  rw [hi, map_smul]
  simp only [smul_eq_mul,← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

theorem fderiv_holomorphicHermite_coordinate (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    fderiv ℂ (ComplexHermite.multivariateNormalized n hn p 0) z
        (realCoordinateDirection j) =
      (Real.sqrt (n*p j : ℕ) : ℂ) *
        ComplexHermite.multivariateNormalized n hn (ComplexHermite.lowerAt p j) 0 z := by
  have hd : DifferentiableAt ℂ (ComplexHermite.multivariateNormalized n hn p 0) z := by
    change DifferentiableAt ℂ (fun w => ComplexHermite.multivariateNormalized n hn p 0 w) z
    simp only [ComplexHermite.multivariateNormalized_zero_right]
    fun_prop
  rw [← dholComponent_eq_complex_fderiv hd j]
  exact ComplexHermite.dholComponent_multivariateNormalized n hn p 0 j z

end
end GinibrePoincare

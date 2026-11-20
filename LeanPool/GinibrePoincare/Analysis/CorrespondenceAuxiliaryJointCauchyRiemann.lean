/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryJointCauchyRiemann.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryHolomorphicDerivative

/-!
# Correspondence auxiliary joint Cauchy riemann

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `hasFDerivAt_complex_of_coordinate_CR`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem configuration_real_basis_expansion {n : ℕ} (z : Configuration n) :
    z = ∑ j : Fin n, ((z j).re • (realCoordinateDirection j : Configuration n) +
      (z j).im • (imaginaryCoordinateDirection j : Configuration n)) := by
  funext k
  simp [Finset.sum_apply, realCoordinateDirection, imaginaryCoordinateDirection,
    coordinateDirection, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Complex.re_add_im]

/-- The actual joint complex derivative constructed from the real coordinate
partials. -/
def jointComplexDerivative {n : ℕ} (L : Configuration n →L[ℝ] ℂ) :
    Configuration n →L[ℂ] ℂ :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (L (realCoordinateDirection j))

theorem jointComplexDerivative_restrictScalars {n : ℕ}
    (L : Configuration n →L[ℝ] ℂ)
    (hL : ∀ j, L (imaginaryCoordinateDirection j) =
      Complex.I * L (realCoordinateDirection j)) :
    (jointComplexDerivative L).restrictScalars ℝ = L := by
  ext z
  change (jointComplexDerivative L) z = L z
  unfold jointComplexDerivative
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  conv_rhs => rw [configuration_real_basis_expansion z]
  rw [map_sum]
  simp only [map_add, map_smul, hL]
  apply Finset.sum_congr rfl
  intro j hj
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_eq_mul]
  conv_lhs => rw [← Complex.re_add_im (z j)]
  simp only [add_mul]
  ac_rfl

/-- Coordinate Cauchy–Riemann equations for an actual real Fréchet derivative
imply genuine joint complex differentiability in every finite dimension. -/
theorem hasFDerivAt_complex_of_coordinate_CR {n : ℕ} {f : Configuration n → ℂ}
    {z : Configuration n} {L : Configuration n →L[ℝ] ℂ} (hf : HasFDerivAt f L z)
    (hL : ∀ j, L (imaginaryCoordinateDirection j) =
      Complex.I * L (realCoordinateDirection j)) :
    HasFDerivAt f (jointComplexDerivative L) z :=
  hasFDerivAt_of_restrictScalars ℝ hf (jointComplexDerivative_restrictScalars L hL)

end
end GinibrePoincare

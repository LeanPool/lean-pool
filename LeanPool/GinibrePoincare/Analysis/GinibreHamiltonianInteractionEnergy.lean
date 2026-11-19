/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianInteractionEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential

/-! Exact Hamiltonian gradient decomposition for the stationary OU action. -/

@[expose] public section
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

theorem ginibreRealCoordinateDifferential_radial {n : ℕ}
    (L : Configuration n →L[ℝ] ℝ) (z : Configuration n) :
    L z = ∑ j : Fin n, ((z j).re*L (realCoordinateDirection j)+
      (z j).im*L (imaginaryCoordinateDirection j)) := by
  have he : z = ∑ j : Fin n, ((z j).re • realCoordinateDirection j+
      (z j).im • imaginaryCoordinateDirection j) := by
    ext i
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection,
        Complex.real_smul]
    · intro b hb hbi
      simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection, Ne.symm hbi]
    · simp
  conv_lhs => rw [he]
  rw [map_sum]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The squared norm of the gradient of `ginibreInteractionPotential n` at `z`: the sum of the
squared derivatives along all real and imaginary coordinate directions. -/
def ginibreInteractionGradientNormSq (n : ℕ) (z : Configuration n) : ℝ :=
  ∑ j : Fin n, ((fderiv ℝ (ginibreInteractionPotential n) z (realCoordinateDirection j))^2+
    (fderiv ℝ (ginibreInteractionPotential n) z (imaginaryCoordinateDirection j))^2)

theorem ginibreHamiltonianGradientNormSq_interaction {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) :
    ginibreHamiltonianGradientNormSq n z = 4*(n : ℝ)^2*configurationNormSq z-
      4*(n : ℝ)*(2*vandermondeDegree n : ℕ)+ginibreInteractionGradientNormSq n z := by
  have hd (j : Fin n) (w : ℂ) :
      fderiv ℝ (ginibreHamiltonian n) z (coordinateDirection j w) =
      2*(n : ℝ)*(conj (z j)*w).re+
        fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j w) := by
    rw [fderiv_ginibreHamiltonian_coordinate z hz j w,
      fderiv_configurationNormSq_coordinate, fderiv_ginibreInteractionPotential_coordinate z hz j w]
    ring
  have hEuler := ginibreRealCoordinateDifferential_radial
    (fderiv ℝ (ginibreInteractionPotential n) z) z
  rw [fderiv_ginibreInteractionPotential_radial n z hz] at hEuler
  unfold ginibreHamiltonianGradientNormSq ginibreInteractionGradientNormSq
  simp only [realCoordinateDirection, imaginaryCoordinateDirection, hd, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, zero_sub, neg_neg]
  have he (j : Fin n) :
      (2*(n : ℝ)*(z j).re+fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j 1))^2+
      (2*(n : ℝ)*(z j).im+fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j
          Complex.I))^2 =
      4*(n : ℝ)^2*((z j).re^2+(z j).im^2)+
      4*(n : ℝ)*((z j).re*fderiv ℝ (ginibreInteractionPotential n) z (realCoordinateDirection j)+
        (z j).im*fderiv ℝ (ginibreInteractionPotential n) z (imaginaryCoordinateDirection j))+
      ((fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j 1))^2+
        (fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j Complex.I))^2) := by
    simp only [realCoordinateDirection, imaginaryCoordinateDirection]
    ring
  simp_rw [he, Finset.sum_add_distrib,← Finset.mul_sum]
  rw [← hEuler]
  simp only [configurationNormSq, Complex.normSq_apply]
  ring_nf

end
end GinibrePoincare

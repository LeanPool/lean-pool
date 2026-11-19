/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevSpectralWeak.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialDomain
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevMatrixLines

/-! # Actual ordinary full weak spectral derivatives across every collision -/

@[expose] public section
open MeasureTheory Filter Matrix MvPolynomial
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem matrixFullSpectralLift_coordinate_weak_test (n d : ℕ)
    (e : Fin (d + 1) ≃ Fin n × Fin n) (F : Configuration n → ℝ)
    (hF : Differentiable ℝ F)
    (hsym : ∀ σ : Fin n ≃ Fin n, ∀ z, F (z ∘ σ) = F z)
    (k : Fin (d + 1) × Fin 2)
    (hg : LocallyIntegrable (fun z => fderiv ℝ
      (fun x => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e x)))
      z (ginibreCoordinateDirection k)) volume)
    (θ : Configuration (d + 1) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) :
    (∫ z, fderiv ℝ
      (fun x => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e x)))
      z (ginibreCoordinateDirection k) * θ z) =
      -(∫ z, matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e z)) *
        fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
  let p := MvPolynomial.renameEquiv ℂ e.symm (matrixCharacteristicResultant n)
  have hp : p ≠ 0 := by
    intro h
    exact matrixCharacteristicResultant_ne_zero n
      ((MvPolynomial.renameEquiv ℂ e.symm).injective (by simpa [p] using h))
  let G := fun z => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e z))
  have hG : Continuous G :=
    (continuous_matrixFullSymmetricSpectralLift n F hF.continuous hsym).comp (by fun_prop)
  have hd (z : Configuration (d + 1)) (hz : eval z p ≠ 0) :
      DifferentiableAt ℝ G z := by
    have he : eval z p =
        (Matrix.of (matrixComplexEntryEquiv e z)).charpoly.resultant
          (Matrix.of (matrixComplexEntryEquiv e z)).charpoly.derivative := by
      rw [← matrixCharacteristicResultant_eval]
      simp [p, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
        matrixComplexEntryEquiv, Function.comp_def]
    have hs : (Matrix.of (matrixComplexEntryEquiv e z)).charpoly.Separable := by
      rw [he] at hz
      by_contra h
      exact hz (Polynomial.resultant_eq_zero_iff.mpr
        ⟨Or.inl (Matrix.charpoly_monic _).ne_zero, h⟩)
    exact (matrixFullSymmetricSpectralLift_differentiableAt n _ hs F hF hsym).comp z
      (by fun_prop)
  exact polynomial_collision_coordinate_weak_test d p hp G hG hd
    hG.locallyIntegrable k hg θ hθ hc

end
end GinibrePoincare

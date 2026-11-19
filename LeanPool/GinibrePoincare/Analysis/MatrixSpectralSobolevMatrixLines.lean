/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevMatrixLines.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLineRemovability
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLift

/-! # Ordinary weak spectral derivatives through actual matrix collisions -/

@[expose] public section
open MeasureTheory Filter Matrix MvPolynomial
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The matrix whose `(i, j)` entry is `z (e.symm (i, j))`. -/
def matrixFromEntryLabels {n d : ℕ} (e : Fin (d + 1) ≃ Fin n × Fin n)
    (z : Fin (d + 1) → ℂ) : GinibreMatrixCoordinates n :=
  fun i j => z (e.symm (i, j))

/-- The true matrix lift satisfies weak derivative identities across collisions
on almost every real entry line. The sole derivative regularity requirement is
actual local integrability; exceptional sets are derived from the discriminant. -/
theorem matrixFullSpectralLift_line_weak_identity_ae (n d : ℕ)
    (e : Fin (d + 1) ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ)
    (hF : Differentiable ℝ F)
    (hsym : ∀ σ : Fin n ≃ Fin n, ∀ z, F (z ∘ σ) = F z) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)),
      ∀ c v : ℂ, v ≠ 0 →
      let f := fun t : ℝ => matrixFullSymmetricSpectralLift n F
        (Matrix.of (matrixFromEntryLabels e (Fin.cons (c + (t : ℂ) * v) y)))
      LocallyIntegrable (deriv f) volume →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ∀ a b : ℝ, a ≤ b →
        tsupport ψ ⊆ Set.Ioo a b →
        (∫ t : ℝ, deriv f t * ψ t) = -(∫ t : ℝ, f t * deriv ψ t) := by
  let p := MvPolynomial.renameEquiv ℂ e.symm (matrixCharacteristicResultant n)
  have hp : p ≠ 0 := by
    intro h
    exact matrixCharacteristicResultant_ne_zero n
      ((MvPolynomial.renameEquiv ℂ e.symm).injective (by simpa [p] using h))
  let G := fun z => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixFromEntryLabels e z))
  have hG : Continuous G := by
    exact (continuous_matrixFullSymmetricSpectralLift n F hF.continuous hsym).comp (by
      unfold matrixFromEntryLabels
      fun_prop)
  have hd (z : Fin (d + 1) → ℂ) (hz : MvPolynomial.eval z p ≠ 0) :
      DifferentiableAt ℝ G z := by
    have he : MvPolynomial.eval z p =
        (Matrix.of (matrixFromEntryLabels e z)).charpoly.resultant
          (Matrix.of (matrixFromEntryLabels e z)).charpoly.derivative := by
      rw [← matrixCharacteristicResultant_eval]
      simp [p, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
        matrixFromEntryLabels, Function.comp_def]
    have hs : (Matrix.of (matrixFromEntryLabels e z)).charpoly.Separable := by
      rw [he] at hz
      by_contra h
      exact hz (Polynomial.resultant_eq_zero_iff.mpr
        ⟨Or.inl (Matrix.charpoly_monic _).ne_zero, h⟩)
    exact (matrixFullSymmetricSpectralLift_differentiableAt n _ hs F hF hsym).comp z (by
      unfold matrixFromEntryLabels
      fun_prop)
  exact polynomial_collision_line_weak_identity_ae d p hp G hG hd

end
end GinibrePoincare

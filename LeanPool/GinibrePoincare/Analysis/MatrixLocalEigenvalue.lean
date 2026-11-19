/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixLocalEigenvalue.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSimpleSpectrum
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Smooth local eigenvalue branches at simple spectrum

The complex implicit-function theorem applies to the characteristic equation
because a separable characteristic polynomial has a nonzero derivative at
each root. Local eigenvalues are constructed, rather than assumed.
-/

@[expose] public section
open scoped Topology ContDiff
open Matrix Filter
namespace GinibrePoincare
noncomputable section

/-- `n × n` complex matrices viewed as plain coordinate functions `Fin n → Fin n → ℂ`. -/
abbrev GinibreMatrixCoordinates (n : ℕ) := Fin n → Fin n → ℂ

/-- The characteristic function `(A, λ) ↦ det (λ • 1 - A)`. -/
def matrixCharacteristicEquation (n : ℕ) (p : GinibreMatrixCoordinates n × ℂ) : ℂ :=
  (Matrix.scalar (Fin n) p.2 - Matrix.of p.1).det

theorem matrixCharacteristicEquation_eq_eval (n : ℕ) (G : GinibreMatrixCoordinates n) (z : ℂ) :
    matrixCharacteristicEquation n (G, z) = (Matrix.charpoly (Matrix.of G)).eval z :=
  (Matrix.eval_charpoly (Matrix.of G) z).symm

theorem contDiff_matrixCharacteristicEquation (n : ℕ) :
    ContDiff ℂ ∞ (matrixCharacteristicEquation n) := by
  unfold matrixCharacteristicEquation
  simp only [Matrix.det_apply', Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  by_cases h : σ i = i <;> simp only [h, ite_true, ite_false, Matrix.of_apply] <;> fun_prop

theorem matrixCharacteristicEquation_partial_eigenvalue (n : ℕ)
    (G : GinibreMatrixCoordinates n) (z : ℂ) :
    (fderiv ℂ (matrixCharacteristicEquation n) (G, z)).comp
      (ContinuousLinearMap.inr ℂ (GinibreMatrixCoordinates n) ℂ) =
        ContinuousLinearMap.toSpanSingleton ℂ ((Matrix.charpoly (Matrix.of G)).derivative.eval z) :=
            by
  have h := ((contDiff_matrixCharacteristicEquation n).differentiable (by simp) (G,
      z)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right G z)
  have hp := (Matrix.charpoly (Matrix.of G)).hasDerivAt z
  have hq : HasFDerivAt (fun w : ℂ => matrixCharacteristicEquation n (G, w))
      (ContinuousLinearMap.toSpanSingleton ℂ ((Matrix.charpoly (Matrix.of G)).derivative.eval z)) z
          := by
    simpa only [matrixCharacteristicEquation_eq_eval] using hp.hasFDerivAt
  exact h.unique hq

theorem matrixCharacteristicEquation_partial_invertible (n : ℕ)
    (G : GinibreMatrixCoordinates n) (z : ℂ) (hs : (Matrix.charpoly (Matrix.of G)).Separable)
    (hz : (Matrix.charpoly (Matrix.of G)).eval z = 0) :
    ((fderiv ℂ (matrixCharacteristicEquation n) (G, z)).comp
      (ContinuousLinearMap.inr ℂ (GinibreMatrixCoordinates n) ℂ)).IsInvertible := by
  rw [matrixCharacteristicEquation_partial_eigenvalue]
  have hc : (Matrix.charpoly (Matrix.of G)).derivative.eval z ≠ 0 := by
    simpa only [Polynomial.eval₂_id] using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) hz
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℂ ((Matrix.charpoly (Matrix.of G)).derivative.eval
        z)⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, hc, smul_eq_mul]
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, hc, smul_eq_mul]

/-- Every root at simple spectrum extends to a complex-smooth local root branch. -/
theorem matrixSimpleSpectrum_exists_local_eigenvalue (n : ℕ)
    (G : GinibreMatrixCoordinates n) (z : ℂ) (hs : (Matrix.charpoly (Matrix.of G)).Separable)
    (hz : (Matrix.charpoly (Matrix.of G)).eval z = 0) :
    ∃ eig : GinibreMatrixCoordinates n → ℂ,
      eig G = z ∧ ContDiffAt ℂ ∞ eig G ∧
        ∀ᶠ H in 𝓝 G, (Matrix.charpoly (Matrix.of H)).eval (eig H) = 0 := by
  let cdf := (contDiff_matrixCharacteristicEquation n).contDiffAt (x := (G, z))
  have hinv := matrixCharacteristicEquation_partial_invertible n G z hs hz
  let eig := cdf.implicitFunction (by simp) hinv
  refine ⟨eig, cdf.implicitFunction_apply_self (by simp) hinv,
    cdf.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  have he := cdf.eventually_apply_implicitFunction (by simp) hinv
  simpa only [matrixCharacteristicEquation_eq_eval, hz] using he

end
end GinibrePoincare

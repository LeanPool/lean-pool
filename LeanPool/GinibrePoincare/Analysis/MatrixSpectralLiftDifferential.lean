/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftDifferential.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixLocalSpectrum
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Differentiating a local spectral observable

Each local eigenvalue branch satisfies the characteristic-root equation. The
one-root derivative theorem identifies its differential with the trace pairing
against the canonical eigenvalue projector. Differentiation of the finite tuple
assembles these component derivatives. Restricting scalars to the reals and
applying the chain rule then gives the derivative of a real eigenvalue observable.
The statements are local on simple spectrum and do not differentiate an arbitrary
measurable enumeration of eigenvalues.
-/

@[expose] public section

open Matrix Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The differential of a genuine local eigenvalue labeling, with canonical spectral
projectors. This is derived from the root equations. -/
theorem matrixLocalLabeling_fderiv (n : ℕ) (A H : GinibreMatrixCoordinates n)
    (labels : GinibreMatrixCoordinates n → Fin n → ℂ)
    (hs : (Matrix.of A).charpoly.Separable) (hd : DifferentiableAt ℂ labels A)
    (hr : ∀ᶠ B in 𝓝 A, ∀ i, (Matrix.of B).charpoly.eval (labels B i) = 0) :
    fderiv ℂ labels A H =
      fun i => trace (matrixEigenvalueProjector n A (labels A i) * Matrix.of H) := by
  have hdi (i : Fin n) : DifferentiableAt ℂ (fun B => labels B i) A :=
    (differentiableAt_pi.mp hd) i
  have hri (i : Fin n) : ∀ᶠ B in 𝓝 A, (Matrix.of B).charpoly.eval (labels B i) = 0 :=
    hr.mono fun B hB => hB i
  have hbase (i : Fin n) : (Matrix.of A).charpoly.eval (labels A i) = 0 :=
    (hri i).self_of_nhds
  rw [fderiv_pi hdi]
  funext i
  exact matrixLocalEigenvalue_fderiv n A H (labels A i) hs (hbase i)
    (fun B => labels B i) rfl (hdi i) (hri i)

/-- Real observables composed with genuine eigenvalue branches obey the chain rule
with the actual projector differential, without assuming any spectral derivative formula. -/
theorem matrixLocalSpectralLift_fderiv (n : ℕ) (A H : GinibreMatrixCoordinates n)
    (labels : GinibreMatrixCoordinates n → Fin n → ℂ) (F : (Fin n → ℂ) → ℝ)
    (hs : (Matrix.of A).charpoly.Separable) (hd : DifferentiableAt ℂ labels A)
    (hF : DifferentiableAt ℝ F (labels A))
    (hr : ∀ᶠ B in 𝓝 A, ∀ i, (Matrix.of B).charpoly.eval (labels B i) = 0) :
    fderiv ℝ (F ∘ labels) A H = fderiv ℝ F (labels A)
      (fun i => trace (matrixEigenvalueProjector n A (labels A i) * Matrix.of H)) := by
  rw [fderiv_comp A hF (hd.restrictScalars ℝ), hd.fderiv_restrictScalars ℝ]
  change fderiv ℝ F (labels A) (fderiv ℂ labels A H) = _
  rw [matrixLocalLabeling_fderiv n A H labels hs hd hr]

end
end GinibrePoincare

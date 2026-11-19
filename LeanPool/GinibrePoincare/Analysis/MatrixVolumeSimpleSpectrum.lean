/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixVolumeSimpleSpectrum.lean.
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
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurEntryVolume

/-!
# Matrix volume simple spectrum

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixVolume_charpoly_separable_ae`.
-/

@[expose] public section

open Matrix MeasureTheory Filter
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section

theorem matrixVolume_polynomial_ne_zero_ae {n : ℕ}
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ≠ 0) :
    ∀ᵐ G ∂(volume : Measure (Fin n → Fin n → ℂ)),
      MvPolynomial.eval (fun ij => G ij.1 ij.2) p ≠ 0 :=
  (matrixVolume_uncurry_preserving n).quasiMeasurePreserving.ae
    (complexMvPolynomial_eval_ne_zero_ae (volume : Measure ℂ) p hp)

theorem matrixVolume_charpoly_separable_ae (n : ℕ) :
    ∀ᵐ G ∂(volume : Measure (Fin n → Fin n → ℂ)), (Matrix.of G).charpoly.Separable := by
  filter_upwards [matrixVolume_polynomial_ne_zero_ae
    (matrixCharacteristicResultant n) (matrixCharacteristicResultant_ne_zero n)] with G hG
  replace hG : Polynomial.resultant (Matrix.of G).charpoly
      (Matrix.of G).charpoly.derivative ≠ 0 := by
    rw [← matrixCharacteristicResultant_eval]
    exact hG
  by_contra hs
  apply hG
  exact Polynomial.resultant_eq_zero_iff.mpr
    ⟨Or.inl (Matrix.of G).charpoly_monic.ne_zero, hs⟩

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftLSIFinite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftLSIWeak

/-!
# Matrix spectral lift LSI finite

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSpectralLift_finite_overlap_lsi`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- Finite actual overlap energy implies the exact Ginibre matrix-lift LSI.
Ordinary weak derivatives through all collision matrices, H1 membership, and
entropy integrability are derived, rather than imposed as certificates. -/
theorem matrixSpectralLift_finite_overlap_lsi_of_entries {n d : ℕ} (hn : 0 < n)
    (e : Fin (d + 1) ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) F ≤
        (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  obtain ⟨u, g, hu, hg, hweak⟩ :=
    matrixSpectralLift_finite_overlap_weak_pair hn e F hF hsym hFL2 hE
  exact matrixSpectralLift_ordinary_weak_lsi hn e F hF hsym u g hu hg hweak

/-- Exact finite-energy matrix-overlap logarithmic Sobolev inequality under the
actual normalized Ginibre law, for every positive matrix dimension. -/
theorem matrixSpectralLift_finite_overlap_lsi {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) F ≤
        (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  let d := n*n-1
  have hm : 1 ≤ n*n := Nat.succ_le_of_lt (Nat.mul_pos hn hn)
  let e : Fin (d+1) ≃ Fin n × Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_prod]
    exact Nat.sub_add_cancel hm)
  exact matrixSpectralLift_finite_overlap_lsi_of_entries hn e F hF hsym hFL2 hE

end
end GinibrePoincare

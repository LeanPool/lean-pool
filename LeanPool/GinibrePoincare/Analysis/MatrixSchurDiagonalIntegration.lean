/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurDiagonalIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurUpperGaussian

/-!
# Matrix Schur diagonal integration

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchur_sortedUpper_diagonal_integral`.
-/

@[expose] public section

open Matrix MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

/-- The unnormalized eigenvalue density `vandermondeWeight z * exp (-n ∑ᵢ |zᵢ|²)`. -/
def schurDiagonalSpectralDensity (n : ℕ) (z : Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeWeight z) *
    ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ i, Complex.normSq (z i)))

theorem measurable_schurDiagonalSpectralDensity (n : ℕ) :
    Measurable (schurDiagonalSpectralDensity n) := by
  have hv : Measurable (fun z : Fin n → ℂ => vandermondeWeight z) :=
    Complex.continuous_normSq.measurable.comp continuous_vandermonde.measurable
  unfold schurDiagonalSpectralDensity
  apply Measurable.mul (ENNReal.measurable_ofReal.comp hv)
  fun_prop

/-- The independent strict upper Gaussian integrates to one in the actual Schur
formula, leaving exactly the ordered eigenvalue Vandermonde-Gaussian density. -/
theorem matrixSchur_sortedUpper_diagonal_integral {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y in matrixSchurSortedUpperDomain n,
      ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
        (matrixGaussianDensity n (schurUpperCombination y) * F (fun i => schurUpperCombination y i
            i)) =
      schurUpperGaussianDiagonalFactor n *
        ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z := by
  have hd : ∀ y : SchurUpperIndex n → ℂ,
      (fun i => schurUpperCombination y i i) = (schurUpperSplit n y).1 := by
    intro y
    funext i
    exact schurUpperCombination_entry y ⟨(i, i), le_refl i⟩
  have hm : Measurable (fun u : SchurStrictUpperIndex n → ℂ => schurStrictUpperGaussianDensity n u)
      := by
    unfold schurStrictUpperGaussianDensity
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_complexCoordinateGaussianDensity n).comp (measurable_pi_apply i)
  have hf := (measurable_schurDiagonalSpectralDensity n).mul hF
  have hsplit := schurUpperSplit_sorted_lintegral
    (fun z => schurDiagonalSpectralDensity n z * F z) hf
    (schurStrictUpperGaussianDensity n) hm
  have he : (fun y : SchurUpperIndex n → ℂ =>
      ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
        (matrixGaussianDensity n (schurUpperCombination y) * F (fun i => schurUpperCombination y i
            i))) =
      (fun y => schurUpperGaussianDiagonalFactor n *
        ((schurDiagonalSpectralDensity n (schurUpperSplit n y).1 * F (schurUpperSplit n y).1) *
          schurStrictUpperGaussianDensity n (schurUpperSplit n y).2)) := by
    funext y
    rw [matrixGaussianDensity_schurUpper_normalized_split hn, hd]
    unfold schurDiagonalSpectralDensity
    ac_rfl
  rw [he, lintegral_const_mul _]
  · rw [hsplit, schurStrictUpperGaussianDensity_integral hn, mul_one]
  · exact (hf.comp ((schurUpperSplit_volume_preserving n).measurable.fst)).mul
      (hm.comp ((schurUpperSplit_volume_preserving n).measurable.snd))

end
end GinibrePoincare

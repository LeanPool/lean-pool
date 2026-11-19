/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLaw.lean.
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

/-! # The actual Gaussian matrix spectral pushforward

This constructs the law from the matrix ensemble. Identifying its density with the
Vandermonde density is a separate change-of-variables theorem.
-/

@[expose] public section
open MeasureTheory Matrix
namespace GinibrePoincare
noncomputable section

/-- A chosen measurable labelling of the eigenvalues of a matrix, from
`matrix_exists_measurable_simple_labeling`. -/
def matrixMeasurableEigenvalues (n : ℕ) : GinibreMatrixCoordinates n → Fin n → ℂ :=
  (matrix_exists_measurable_simple_labeling n).choose

theorem matrixMeasurableEigenvalues_measurable (n : ℕ) :
    Measurable (matrixMeasurableEigenvalues n) :=
  (matrix_exists_measurable_simple_labeling n).choose_spec.1

theorem matrixMeasurableEigenvalues_spec (n : ℕ) (A : GinibreMatrixCoordinates n)
    (hA : (Matrix.of A).charpoly.Separable) :
    Function.Injective (matrixMeasurableEigenvalues n A) ∧
      ∀ i, (Matrix.of A).charpoly.eval (matrixMeasurableEigenvalues n A i) = 0 :=
  (matrix_exists_measurable_simple_labeling n).choose_spec.2 A hA

/-- The law of the labelled eigenvalues under the Ginibre matrix Gaussian measure. -/
def matrixSpectralMeasure (n : ℕ) : Measure (Fin n → ℂ) :=
  (matrixGaussianMeasure n).map (matrixMeasurableEigenvalues n)

instance matrixSpectralMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (matrixSpectralMeasure n) := by
  constructor
  rw [matrixSpectralMeasure]
  erw [Measure.map_apply (matrixMeasurableEigenvalues_measurable n) MeasurableSet.univ]
  exact matrixGaussianMeasure_univ n

theorem matrixGaussian_measurable_labels_spec_ae (n : ℕ) :
    ∀ᵐ A ∂matrixGaussianMeasure n, Function.Injective (matrixMeasurableEigenvalues n A) ∧
      ∀ i, (Matrix.of A).charpoly.eval (matrixMeasurableEigenvalues n A i) = 0 := by
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
  exact matrixMeasurableEigenvalues_spec n A hA

theorem matrixSpectralMeasure_distinct_ae (n : ℕ) :
    ∀ᵐ z ∂matrixSpectralMeasure n, Function.Injective z := by
  rw [matrixSpectralMeasure]
  apply (ae_map_iff (matrixMeasurableEigenvalues_measurable n).aemeasurable
    (by
      have he : {x : Fin n → ℂ | Function.Injective x} =
          ⋂ i : Fin n, ⋂ j : Fin n, {x | i = j ∨ x i ≠ x j} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Function.Injective]
        constructor
        · intro h i j
          by_cases hij : i = j
          · exact Or.inl hij
          · exact Or.inr fun heq => hij (h heq)
        · intro h i j heq
          exact (h i j).resolve_right fun hn => hn heq
      rw [he]
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      by_cases hij : i = j
      · simp [hij]
      · have hh : MeasurableSet {x : Fin n → ℂ | x i = x j} := (isClosed_eq
          (show Continuous (fun x : Fin n → ℂ => x i) from continuous_apply i)
          (show Continuous (fun x : Fin n → ℂ => x j) from continuous_apply j)).measurableSet
        simpa only [hij, false_or, Set.compl_ofPred] using hh.compl)).2
  filter_upwards [matrixGaussian_measurable_labels_spec_ae n] with A hA
  exact hA.1

end
end GinibrePoincare

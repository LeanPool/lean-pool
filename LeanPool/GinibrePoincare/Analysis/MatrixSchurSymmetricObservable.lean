/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurSymmetricObservable.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurDiagonalIntegration
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Matrix Schur symmetric observable

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSimpleSymmetricObservable_measurable`,
`matrixSimpleSymmetricObservable_unitary`, `matrixSimpleSymmetricObservable_schurUpper`,
`matrixSimpleSymmetricObservable_ae`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrix_charpoly_separable_iff_resultant_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    A.charpoly.Separable ↔ MvPolynomial.eval (fun ij => A ij.1 ij.2)
      (matrixCharacteristicResultant n) ≠ 0 := by
  rw [matrixCharacteristicResultant_eval]
  constructor
  · intro hs hz
    have hr := Polynomial.resultant_eq_zero_iff.mp hz
    exact hr.2 hs
  · intro h
    by_contra hs
    exact h (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl A.charpoly_monic.ne_zero, hs⟩)

/-- The observable `F` evaluated at the measurably labelled eigenvalues of `A` when the
characteristic polynomial of `A` is separable, and `0` otherwise. -/
def matrixSimpleSymmetricObservable (n : ℕ) (F : (Fin n → ℂ) → ℝ≥0∞)
    (A : Fin n → Fin n → ℂ) : ℝ≥0∞ := by
  classical
  exact if (Matrix.of A).charpoly.Separable then F (matrixMeasurableEigenvalues n A) else 0

theorem measurableSet_matrixSimpleSpectrum (n : ℕ) :
    MeasurableSet {A : Fin n → Fin n → ℂ | (Matrix.of A).charpoly.Separable} := by
  have he : {A : Fin n → Fin n → ℂ | (Matrix.of A).charpoly.Separable} =
      {A | MvPolynomial.eval (Function.uncurry A) (matrixCharacteristicResultant n) ≠ 0} := by
    ext A
    exact matrix_charpoly_separable_iff_resultant_ne_zero (Matrix.of A)
  rw [he]
  have hm : Measurable (fun A : Fin n → Fin n → ℂ =>
      MvPolynomial.eval (Function.uncurry A) (matrixCharacteristicResultant n)) :=
    (MvPolynomial.continuous_eval (matrixCharacteristicResultant n)).measurable.comp (by fun_prop)
  exact (measurableSet_eq_fun hm measurable_const).compl

theorem matrixSimpleSymmetricObservable_measurable {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (matrixSimpleSymmetricObservable n F) := by
  classical
  exact (hF.comp (matrixMeasurableEigenvalues_measurable n)).piecewise
    (measurableSet_matrixSimpleSpectrum n) measurable_const

theorem matrixSimpleSymmetricObservable_unitary {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (U A : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixSimpleSymmetricObservable n F (U * A * Uᴴ) = matrixSimpleSymmetricObservable n F A := by
  classical
  change (if (U * A * Uᴴ).charpoly.Separable then F (matrixMeasurableEigenvalues n (U * A * Uᴴ))
      else 0) =
    (if A.charpoly.Separable then F (matrixMeasurableEigenvalues n A) else 0)
  have hc := matrix_charpoly_unitary_conjugation A U hU
  by_cases hs : A.charpoly.Separable
  · have hsU : (U * A * Uᴴ).charpoly.Separable := hc.symm ▸ hs
    rw [ite_eq_left hsU, ite_eq_left hs]
    have h1 := matrixMeasurableEigenvalues_spec n (U * A * Uᴴ) hsU
    have h2 := matrixMeasurableEigenvalues_spec n A hs
    have hr : ∀ i, A.charpoly.eval (matrixMeasurableEigenvalues n (U * A * Uᴴ) i) = 0 := by
      intro i
      rw [← hc]
      exact h1.2 i
    obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n A hs
      (matrixMeasurableEigenvalues n A) (matrixMeasurableEigenvalues n (U * A * Uᴴ))
      h2.1 h1.1 h2.2 hr
    have hfun : matrixMeasurableEigenvalues n (U * A * Uᴴ) = matrixMeasurableEigenvalues n A ∘ e :=
      funext he
    rw [hfun, hsym]
  · have hsU : ¬(U * A * Uᴴ).charpoly.Separable := by rw [hc]; exact hs
    rw [ite_eq_right hsU, ite_eq_right hs]

theorem matrixSimpleSymmetricObservable_schurUpper {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (y : SchurUpperIndex n → ℂ) (hy : y ∈ matrixSchurSortedUpperDomain n) :
    matrixSimpleSymmetricObservable n F (schurUpperCombination y) =
      F (fun i => schurUpperCombination y i i) := by
  classical
  let A := schurUpperCombination y
  let a := fun i => A i i
  have ha : Function.Injective a := matrixSchurOrderedDiagonal_injective hy
  have hr : ∀ i, A.charpoly.eval (a i) = 0 :=
    schur_diagonal_roots A (fun i j hij => schurUpperCombination_lower_zero y i j hij)
  have hs := matrix_injective_full_roots_separable n A a ha hr
  have hb := matrixMeasurableEigenvalues_spec n A hs
  obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n A hs
    a (matrixMeasurableEigenvalues n A) ha hb.1 hr hb.2
  have hf : matrixMeasurableEigenvalues n A = a ∘ e := funext he
  change (if A.charpoly.Separable then F (matrixMeasurableEigenvalues n A) else 0) = F a
  rw [ite_eq_left hs, hf, hsym]

theorem matrixSimpleSymmetricObservable_ae {n : ℕ} (F : (Fin n → ℂ) → ℝ≥0∞) :
    matrixSimpleSymmetricObservable n F =ᵐ[matrixGaussianMeasure n]
      (fun A => F (matrixMeasurableEigenvalues n A)) := by
  classical
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
  exact ite_eq_left hA

end
end GinibrePoincare

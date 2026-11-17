/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianFourierCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianPolynomialCompleteness

/-! # Euclidean coordinates for complex configurations -/


@[expose] public section


namespace GinibrePoincare

noncomputable section

/-- Real and imaginary coordinates identify a complex configuration with a
real Euclidean vector. -/
def configurationEuclideanLinearEquiv (n : ℕ) :
    Configuration n ≃ₗ[ℝ] ((Fin n × Fin 2) → ℝ) where
  toFun z := fun ij : Fin n × Fin 2 ↦ ![(z ij.1).re, (z ij.1).im] ij.2
  invFun x i := ⟨x (i, 0), x (i, 1)⟩
  left_inv z := by
    ext i; rfl
  right_inv x := by
    ext ⟨i, j⟩
    fin_cases j <;> rfl
  map_add' x y := by
    ext ⟨i, j⟩
    fin_cases j <;> simp
  map_smul' r x := by
    ext ⟨i, j⟩
    fin_cases j <;> simp

/-- The same coordinate identification as a homeomorphic continuous linear
equivalence, hence in particular a measurable equivalence. -/
def configurationEuclideanEquiv (n : ℕ) :
    Configuration n ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) :=
  (configurationEuclideanLinearEquiv n).toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin n × Fin 2) ℝ).symm

@[simp] theorem configurationEuclideanEquiv_apply_zero
    (n : ℕ) (z : Configuration n) (i : Fin n) :
    configurationEuclideanEquiv n z (i, 0) = (z i).re := by
  simp [configurationEuclideanEquiv, configurationEuclideanLinearEquiv]

@[simp] theorem configurationEuclideanEquiv_apply_one
    (n : ℕ) (z : Configuration n) (i : Fin n) :
    configurationEuclideanEquiv n z (i, 1) = (z i).im := by
  simp [configurationEuclideanEquiv, configurationEuclideanLinearEquiv]

@[simp] theorem configurationEuclideanEquiv_symm_apply
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n) :
    (configurationEuclideanEquiv n).symm x i =
      ⟨x (i, 0), x (i, 1)⟩ := by
  simp [configurationEuclideanEquiv, configurationEuclideanLinearEquiv]

theorem measurable_configurationEuclideanEquiv (n : ℕ) :
    Measurable (configurationEuclideanEquiv n) :=
  (configurationEuclideanEquiv n).continuous.measurable

theorem measurable_configurationEuclideanEquiv_symm (n : ℕ) :
    Measurable (configurationEuclideanEquiv n).symm :=
  (configurationEuclideanEquiv n).symm.continuous.measurable

theorem real_inner_configurationEuclideanEquiv
    (n : ℕ) (z : Configuration n)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    inner ℝ (configurationEuclideanEquiv n z) x =
      configurationRealPairing ((configurationEuclideanEquiv n).symm x) z := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct configurationRealPairing
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.sum_univ_two]
  simp only [star_trivial]
  rw [configurationEuclideanEquiv_apply_zero,
    configurationEuclideanEquiv_apply_one]
  simp only [configurationEuclideanEquiv_symm_apply]

end
end GinibrePoincare

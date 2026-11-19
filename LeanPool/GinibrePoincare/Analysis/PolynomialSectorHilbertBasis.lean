/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialSectorHilbertBasis.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialSectorSemigroup
public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorKernel
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Complete normalized Hermite–Laguerre basis of the concrete closed sector -/

@[expose] public section
namespace GinibrePoincare
noncomputable section

/-- No actual equilibrium Hermite–Laguerre vector is zero. -/
theorem polynomialSectorEigenvector_ne_zero (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) : polynomialSectorEigenvector n hn i ≠ 0 := by
  intro h
  have hz : polynomialEigenfunctionL2 n hn i = 0 := congrArg Subtype.val h
  have hi := polynomialEigenfunction_inner_self_ne_zero n hn i
  rw [← inner_polynomialEigenfunctionL2 n hn i i, hz] at hi
  simp at hi

/-- Normalization in the actual equilibrium L² norm. -/
def normalizedPolynomialSectorEigenvector (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) : closedPolynomialSector n hn :=
  (‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialSectorEigenvector n hn i

theorem normalizedPolynomialSectorEigenvector_orthonormal (n : ℕ) (hn : 2 ≤ n) :
    Orthonormal ℂ (normalizedPolynomialSectorEigenvector n hn) := by
  constructor
  · intro i
    exact norm_smul_inv_norm (polynomialSectorEigenvector_ne_zero n hn i)
  · intro i j hij
    change inner ℂ
      ((‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialEigenfunctionL2 n hn i)
      ((‖polynomialSectorEigenvector n hn j‖⁻¹ : ℂ) • polynomialEigenfunctionL2 n hn j) = 0
    rw [inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ)]
    have ho : inner ℂ (polynomialEigenfunctionL2 n hn i)
        (polynomialEigenfunctionL2 n hn j) = 0 := by
      rw [inner_polynomialEigenfunctionL2]
      apply polynomialEigenfunction_equilibrium_orthogonal n hn
      rintro ⟨ha, hb, hm⟩
      apply hij
      cases i
      cases j
      simp_all
    rw [ho, mul_zero, mul_zero]

/-- The normalization does not change the algebraic span. -/
theorem polynomialSectorEigenvector_mem_normalized_span (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    polynomialSectorEigenvector n hn i ∈ Submodule.span ℂ
      (Set.range (normalizedPolynomialSectorEigenvector n hn)) := by
  have hnorm : ‖polynomialSectorEigenvector n hn i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (polynomialSectorEigenvector_ne_zero n hn i)
  have h := (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n hn))).smul_mem
    (‖polynomialSectorEigenvector n hn i‖ : ℂ) (Submodule.subset_span ⟨i, rfl⟩)
  simpa only [normalizedPolynomialSectorEigenvector, smul_smul,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnorm), one_smul] using h

/-- Completeness in the actual closed sector. -/
theorem normalizedPolynomialSectorEigenvector_dense_span (n : ℕ) (hn : 2 ≤ n) :
    (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n hn))).topologicalClosure =
        ⊤ := by
  apply top_unique
  intro x hx
  refine (polynomialSectorCombination_dense n hn).induction_on x ?_ ?_
  · exact (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n
      hn))).isClosed_topologicalClosure
  · intro c
    apply (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n
        hn))).le_topologicalClosure
    unfold polynomialSectorCombination
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (polynomialSectorEigenvector_mem_normalized_span n hn i)

/-- The concrete closed polynomial-sector Hilbert basis. -/
def polynomialSectorHilbertBasis (n : ℕ) (hn : 2 ≤ n) :
    HilbertBasis (PolynomialEigenfunctionData n) ℂ (closedPolynomialSector n hn) :=
  HilbertBasis.mk (normalizedPolynomialSectorEigenvector_orthonormal n hn)
    (by rw [normalizedPolynomialSectorEigenvector_dense_span])

@[simp] theorem polynomialSectorHilbertBasis_apply (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    polynomialSectorHilbertBasis n hn i = normalizedPolynomialSectorEigenvector n hn i := by
  simp [polynomialSectorHilbertBasis]

end
end GinibrePoincare

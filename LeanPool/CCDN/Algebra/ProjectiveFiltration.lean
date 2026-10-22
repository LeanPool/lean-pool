/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredIntersection
import LeanPool.CCDN.Algebra.CoordinatePowerGeneration

/-!
# The filtered homogeneous coordinate algebra

For an affine coordinate ideal `I`, this constructs the subalgebra of
`(K[x]/I)[w]` whose coefficient of `w^n` is represented by a polynomial of degree
at most `n`. Its homogeneous pieces recover the filtered Hilbert
function. Multiplication by the homogenizing coordinate identifies the previous
filtered space inside the next piece.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- Constants lie in every piece of the degree filtration of the coordinate ring. -/
lemma filteredCoordinateSpace_algebraMap_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (c : K) :
    algebraMap K (MvPolynomial σ K ⧸ I) c ∈ filteredCoordinateSpace I n := by
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.C c, ?_, by simp⟩
  simp [MvPolynomial.mem_restrictTotalDegree]

/-- Homogeneous coordinate algebra of the filtered affine coordinate ring. -/
def projectiveCoordinateAlgebra {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : Subalgebra K (Polynomial (MvPolynomial σ K ⧸ I)) where
  carrier := {f | ∀ n, f.coeff n ∈ filteredCoordinateSpace I n}
  mul_mem' hf hg n := by
    rw [Polynomial.coeff_mul]
    apply Submodule.sum_mem
    rintro ⟨i, j⟩ hij
    have := filteredCoordinateSpace_mul_mem I (hf i) (hg j)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hij] at this
  one_mem' n := by
    by_cases hn : n = 0
    · subst n
      simpa using filteredCoordinateSpace_algebraMap_mem I 0 1
    · simp [Polynomial.coeff_one, hn]
  add_mem' hf hg n := by
    rw [Polynomial.coeff_add]
    exact (filteredCoordinateSpace I n).add_mem (hf n) (hg n)
  zero_mem' n := by simp
  algebraMap_mem' c n := by
    by_cases hn : n = 0
    · subst n
      simpa using filteredCoordinateSpace_algebraMap_mem I 0 c
    · simp [Polynomial.algebraMap_apply, Polynomial.coeff_C, hn]

/-- The monomial `a * w ^ n` lies in the homogeneous coordinate algebra if and only if `a` lies
in the degree-`n` piece of the filtered coordinate ring. -/
lemma projective_monomial_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (a : MvPolynomial σ K ⧸ I) :
    Polynomial.monomial n a ∈ projectiveCoordinateAlgebra I ↔
      a ∈ filteredCoordinateSpace I n := by
  constructor
  · intro h
    simpa using h n
  · intro ha i
    by_cases hi : n = i
    · subst i
      simpa using ha
    · simp [Polynomial.coeff_monomial, hi]

/-- The homogenizing coordinate `w` in the homogeneous coordinate algebra. -/
def projectiveInfinityCoordinate {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : projectiveCoordinateAlgebra I :=
  ⟨Polynomial.X, by
    rw [← Polynomial.monomial_one_one_eq_X, projective_monomial_mem]
    simpa using filteredCoordinateSpace_algebraMap_mem I 1 1⟩

end
end CCDN

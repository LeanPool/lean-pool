/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic

/-!
# A lower bound for a symmetric operator with triangular matrix

This is the spectral step used in the proof of Lemma 3.10. The basis in which
the matrix is triangular need not be orthogonal.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Module

open scoped BigOperators RealInnerProductSpace

/-- A diagonal lower bound in any triangular basis is a quadratic-form lower bound
for a symmetric operator. -/
theorem symmetric_triangular_inner_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ}
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (b : Basis (Fin N) ℝ E)
    (htri : (LinearMap.toMatrix b b T).IsUpperTriangular) (a : ℝ)
    (hdiag : ∀ i, a ≤ LinearMap.toMatrix b b T i i) (x : E) :
    a * ‖x‖ ^ 2 ≤ ⟪T x, x⟫ := by
  have hn : Module.finrank ℝ E = N := by simpa using Module.finrank_eq_card_basis b
  have heig (i : Fin N) : a ≤ hT.eigenvalues hn i := by
    have he : T.charpoly.IsRoot (hT.eigenvalues hn i) :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly T _).mp (hT.hasEigenvalue_eigenvalues hn i)
    rw [← T.charpoly_toMatrix b,
      Matrix.charpoly_of_isUpperTriangular _ htri] at he
    simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at he
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp he
    rw [sub_eq_zero.mp hj]
    exact hdiag j
  let e := hT.eigenvectorBasis hn
  calc
    a * ‖x‖ ^ 2 = ∑ i : Fin N, a * ⟪e i, x⟫ ^ 2 := by
      rw [← e.sum_sq_inner_right x, Finset.mul_sum]
    _ ≤ ∑ i : Fin N, hT.eigenvalues hn i * ⟪e i, x⟫ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (heig i) (sq_nonneg _)
    _ = ⟪T x, x⟫ := by
      rw [← e.sum_inner_mul_inner (T x) x]
      apply Finset.sum_congr rfl
      intro i _
      change _ = ⟪T x, hT.eigenvectorBasis hn i⟫ * ⟪hT.eigenvectorBasis hn i, x⟫
      rw [hT x (hT.eigenvectorBasis hn i), hT.apply_eigenvectorBasis,
        real_inner_smul_right, real_inner_comm x (hT.eigenvectorBasis hn i)]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      ring

end NoncommutativeAMGM

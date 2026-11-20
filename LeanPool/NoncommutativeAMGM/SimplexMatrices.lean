/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.SimplexVectors

/-! # Positive semidefinite matrices from the concrete simplex -/

@[expose] public section

namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators

/-- The complement of two orthonormal real vectors is a positive projection. -/
theorem orthonormal_pair_complement_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u z : ι → ℝ) (hu : u ⬝ᵥ u = 1) (hz : z ⬝ᵥ z = 1) (huz : u ⬝ᵥ z = 0) :
    (1 - vecMulVec u u - vecMulVec z z).PosSemidef := by
  let P := vecMulVec u u
  let Q := vecMulVec z z
  have hzu : z ⬝ᵥ u = 0 := by rw [dotProduct_comm, huz]
  have hPP : P * P = P := by simp [P, vecMulVec_mul_vecMulVec, hu]
  have hQQ : Q * Q = Q := by simp [Q, vecMulVec_mul_vecMulVec, hz]
  have hPQ : P * Q = 0 := by simp [P, Q, vecMulVec_mul_vecMulVec, huz]
  have hQP : Q * P = 0 := by simp [P, Q, vecMulVec_mul_vecMulVec, hzu]
  have hT : (1 - P - Q).conjTranspose = 1 - P - Q := by
    simp [P, Q, conjTranspose_eq_transpose_of_trivial, transpose_vecMulVec]
  have hId : (1 - P - Q) * (1 - P - Q) = 1 - P - Q := by
    noncomm_ring [hPP, hQQ, hPQ, hQP]
  have h := posSemidef_self_mul_conjTranspose (1 - P - Q)
  rw [hT, hId] at h
  exact h

/-- The matrix family in equation (4), with explicit vectors in `ℝⁿ`. -/
noncomputable def simplexMatrix (n : ℕ) (α β : ℝ) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  α • 1 + (1 - α) • vecMulVec (simplexAxis n) (simplexAxis n) +
    β • (vecMulVec (simplexAxis n) (simplexVector n i) +
      vecMulVec (simplexVector n i) (simplexAxis n)) +
    (β ^ 2 - α) • vecMulVec (simplexVector n i) (simplexVector n i)

/-- An explicit decomposition into a nonnegative projection and a rank-one Gram matrix. -/
theorem simplexMatrix_gram (n : ℕ) (α β : ℝ) (i : Fin n) :
    simplexMatrix n α β i =
      α • (1 - vecMulVec (simplexAxis n) (simplexAxis n) -
        vecMulVec (simplexVector n i) (simplexVector n i)) +
      vecMulVec (simplexAxis n + β • simplexVector n i)
        (simplexAxis n + β • simplexVector n i) := by
  apply Matrix.ext
  intro j k
  simp [simplexMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Every member of the actual simplex family is PSD whenever `α ≥ 0`. -/
theorem simplexMatrix_posSemidef {n : ℕ} (hn : 1 < n) {α β : ℝ} (hα : 0 ≤ α)
    (i : Fin n) : (simplexMatrix n α β i).PosSemidef := by
  rw [simplexMatrix_gram]
  apply Matrix.PosSemidef.add
  · exact (orthonormal_pair_complement_posSemidef _ _
      (simplexAxis_dot_self (by omega))
      (by simpa using simplexVector_dot hn i i)
      (simplexAxis_dot_vector (by omega) i)).smul hα
  · simpa using posSemidef_vecMulVec_self_star
      (simplexAxis n + β • simplexVector n i)

/-- The normalization relation gives the exact sum `nI`, not merely an upper bound. -/
theorem simplexMatrix_sum {n : ℕ} (hn : 1 < n) (α β : ℝ)
    (hαβ : ((n : ℝ) - 2) * α + β ^ 2 = (n : ℝ) - 1) :
    ∑ i, simplexMatrix n α β i = (n : ℝ) • 1 := by
  classical
  have hcross : (∑ i, (vecMulVec (simplexAxis n) (simplexVector n i) +
      vecMulVec (simplexVector n i) (simplexAxis n))) = 0 := by
    apply Matrix.ext
    intro j k
    simp only [Matrix.sum_apply, Matrix.add_apply, vecMulVec_apply,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have hz (j : Fin n) : ∑ i, simplexVector n i j = 0 := by
      simpa only [Finset.sum_apply, Pi.zero_apply] using
        congrFun (simplexVector_sum (show 0 < n by omega)) j
    simp only [hz, mul_zero, zero_mul, add_zero, Matrix.zero_apply]
  simp only [simplexMatrix, Finset.sum_add_distrib, ← Finset.smul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, hcross, smul_zero, add_zero, simplexVector_frame hn]
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hd : (n : ℝ) - 1 ≠ 0 := by linarith
  have hcoef : (β ^ 2 - α) * ((n : ℝ) / (n - 1 : ℝ)) = (n : ℝ) * (1 - α) := by
    field_simp
    nlinarith [hαβ]
  simp only [smul_smul]
  rw [hcoef]
  apply Matrix.ext
  intro j k
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The action on the distinguished axis initiates the Appendix A recurrence. -/
theorem simplexMatrix_mulVec_axis {n : ℕ} (hn : 1 < n) (α β : ℝ) (i : Fin n) :
    simplexMatrix n α β i *ᵥ simplexAxis n =
      simplexAxis n + β • simplexVector n i := by
  have hu := simplexAxis_dot_self (show 0 < n by omega)
  have hzu : simplexVector n i ⬝ᵥ simplexAxis n = 0 := by
    rw [dotProduct_comm, simplexAxis_dot_vector (by omega)]
  simp only [simplexMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.vecMulVec_mulVec, hu, hzu, op_smul_eq_smul,
    one_smul, zero_smul, smul_zero, add_zero, zero_add]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The action on a previously encountered simplex vector, for a fresh index. -/
theorem simplexMatrix_mulVec_other {n : ℕ} (hn : 1 < n) (α β : ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    simplexMatrix n α β i *ᵥ simplexVector n j =
      α • simplexVector n j - (β / ((n : ℝ) - 1)) • simplexAxis n -
        ((β ^ 2 - α) / ((n : ℝ) - 1)) • simplexVector n i := by
  have huz := simplexAxis_dot_vector (show 0 < n by omega) j
  have hzz := simplexVector_dot hn i j
  rw [ite_eq_right hij] at hzz
  simp only [simplexMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.vecMulVec_mulVec, huz, hzz, op_smul_eq_smul,
    zero_smul, smul_zero, add_zero]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The concrete parameter required by the normalization in the introduction. -/
noncomputable def simplexAlpha (n : ℕ) (β : ℝ) : ℝ :=
  ((n : ℝ) - 1 - β ^ 2) / ((n : ℝ) - 2)

/-- For every permitted `β`, the constructed matrices are PSD and sum exactly to `nI`. -/
theorem simplexMatrix_admissible {n : ℕ} (hn : 3 ≤ n) (β : ℝ)
    (hβ : β ^ 2 ≤ (n : ℝ) - 1) :
    (∀ i, (simplexMatrix n (simplexAlpha n β) β i).PosSemidef) ∧
      ∑ i, simplexMatrix n (simplexAlpha n β) β i = (n : ℝ) • 1 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) - 2 ≠ 0 := by linarith
  constructor
  · intro i
    apply simplexMatrix_posSemidef (by omega)
    exact div_nonneg (by linarith) (by linarith)
  · apply simplexMatrix_sum (by omega)
    dsimp [simplexAlpha]
    field_simp
    ring

end NoncommutativeAMGM

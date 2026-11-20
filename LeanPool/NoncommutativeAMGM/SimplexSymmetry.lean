/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SimplexWords

/-! # Permutation symmetry and the axis eigenvector of the simplex average -/

@[expose] public section

namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators

/-- Relabeling all indices leaves an ordered without-replacement sum invariant. -/
theorem distinctProductSum_comp_equiv {R : Type*} [Semiring R] {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (A : Fin n → R) :
    distinctProductSum n m (A ∘ σ) = distinctProductSum n m A := by
  classical
  exact Fintype.sum_equiv (Equiv.embeddingCongr (Equiv.refl (Fin m)) σ) _ _ (fun _ ↦ rfl)

/-- Relabeling coordinates relabels the corresponding concrete simplex matrix. -/
theorem simplexMatrix_reindex {n : ℕ} (α β : ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Matrix.reindexAlgEquiv ℝ ℝ σ (simplexMatrix n α β i) =
      simplexMatrix n α β (σ i) := by
  classical
  apply Matrix.ext
  intro j k
  change simplexMatrix n α β i (σ.symm j) (σ.symm k) = _
  simp [simplexMatrix, Matrix.one_apply, simplexAxis, simplexVector, simplexCentered,
    Equiv.eq_symm_apply, vecMulVec_apply]

/-- The actual averaged matrix is invariant under every coordinate permutation. -/
theorem simplexMean_reindex {n m : ℕ} (α β : ℝ) (σ : Equiv.Perm (Fin n)) :
    Matrix.reindexAlgEquiv ℝ ℝ σ (withoutReplacementMean n m (simplexMatrix n α β)) =
      withoutReplacementMean n m (simplexMatrix n α β) := by
  classical
  simp only [withoutReplacementMean, map_smul, distinctProductSum, map_sum,
    map_list_prod, List.map_ofFn, Function.comp_def, simplexMatrix_reindex]
  congr 1
  exact distinctProductSum_comp_equiv σ (simplexMatrix n α β)

/-- Coordinate-permutation invariant matrices send the axis to its own span. -/
theorem invariant_matrix_axis {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ σ : Equiv.Perm (Fin n), Matrix.reindexAlgEquiv ℝ ℝ σ M = M) :
    M *ᵥ simplexAxis n =
      (simplexAxis n ⬝ᵥ (M *ᵥ simplexAxis n)) • simplexAxis n := by
  classical
  let v := M *ᵥ simplexAxis n
  have hv (i j : Fin n) : v i = v j := by
    let σ := Equiv.swap i j
    have hentries (k : Fin n) : M i k = M j (σ k) := by
      have h := congrFun (congrFun (hM σ) j) (σ k)
      simpa [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, σ] using h
    change (∑ k, M i k * simplexAxis n k) = ∑ k, M j k * simplexAxis n k
    simp_rw [hentries, simplexAxis]
    exact Equiv.sum_comp σ (fun k : Fin n ↦ M j k * (Real.sqrt (n : ℝ))⁻¹)
  let i : Fin n := ⟨0, hn⟩
  have hconst : v = (v i * Real.sqrt n) • simplexAxis n := by
    funext j
    simp only [Pi.smul_apply, simplexAxis, smul_eq_mul]
    rw [hv j i]
    have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hcoef : simplexAxis n ⬝ᵥ v = v i * Real.sqrt n := by
    calc
      _ = simplexAxis n ⬝ᵥ ((v i * Real.sqrt n) • simplexAxis n) :=
        congrArg (fun w ↦ simplexAxis n ⬝ᵥ w) hconst
      _ = _ := by rw [dotProduct_smul, simplexAxis_dot_self hn, smul_eq_mul, mul_one]
  change v = (simplexAxis n ⬝ᵥ v) • simplexAxis n
  rw [hcoef]
  exact hconst

/-- The averaged simplex matrix has the recursively computed axis eigenvalue. -/
theorem simplexMean_axis_eigenvector {n m : ℕ} (hn : 1 < n) (hmn : m ≤ n) (α β : ℝ)
    (hαβ : ((n : ℝ) - 2) * α + β ^ 2 = (n : ℝ) - 1) :
    withoutReplacementMean n m (simplexMatrix n α β) *ᵥ simplexAxis n =
      simplexRecurrence (2 * α) (α * (n : ℝ) / ((n : ℝ) - 1)) m • simplexAxis n := by
  rw [invariant_matrix_axis (show 0 < n by omega) _ (simplexMean_reindex α β),
    simplexMean_axis_coefficient hn hmn α β hαβ]

end NoncommutativeAMGM

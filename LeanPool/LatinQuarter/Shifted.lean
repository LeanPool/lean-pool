/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import LeanPool.LatinQuarter.Vanishing
public import LeanPool.LatinQuarter.Tags

/-!
# Shifted square-zero tags
-/

@[expose] public section

namespace LatinQuarter
open scoped BigOperators Matrix

/-- The `k` dummy entries occupy distinct rows and columns, indexed by
the left summand of `e`. -/
noncomputable def markedConstant {N : Type*} {k h : ℕ}
    (e : Fin k ⊕ Fin h ≃ N) (c s : N) : ZMod 2 := by
  classical
  exact if (e.symm c).isLeft ∧ c = s then 1 else 0

/-- Square-zero bookkeeping variables with a chosen diagonal block marked by ones. -/
noncomputable def shiftedTags {N : Type*} {k h : ℕ}
    (e : Fin k ⊕ Fin h ≃ N) : Matrix N N (TagRing (N × N)) :=
  fun c s => tag (c, s) + algebraMap (ZMod 2) _ (markedConstant e c s)

theorem shiftedTags_square {N : Type*} {k h : ℕ}
    (e : Fin k ⊕ Fin h ≃ N) (c s : N) :
    squareHom (shiftedTags e c s) = algebraMap (ZMod 2) _ (markedConstant e c s) := by
  classical
  simp only [shiftedTags, map_add, squareHom, frobenius_def]
  rw [pow_two, tag_sq, zero_add]
  unfold markedConstant
  split_ifs <;> simp

/-- A version of the vanishing lemma allowing arbitrary finite sets of
selected rows and columns in each minor. -/
theorem shifted_tags_product_vanishes {N ι : Type*} [Fintype ι]
    {k h : ℕ} (e : Fin k ⊕ Fin h ≃ N)
    (α : ι → Type*) [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (r c : (i : ι) → α i → N)
    (hbudget : h * h < ∑ i, (Fintype.card (α i) - k)) :
    (∏ i, ((shiftedTags e).submatrix (r i) (c i)).det) = 0 := by
  classical
  let M := (shiftedTags e).submatrix e e
  let A := M.submatrix Sum.inl Sum.inl
  let B := M.submatrix Sum.inl Sum.inr
  let C := M.submatrix Sum.inr Sum.inl
  let D := M.submatrix Sum.inr Sum.inr
  have hA : squareHom.mapMatrix A = 1 := by
    ext i j
    change squareHom (shiftedTags e (e (Sum.inl i)) (e (Sum.inl j))) = _
    rw [shiftedTags_square]
    simp [markedConstant, Matrix.one_apply, e.injective.eq_iff]
  have hC : C.map squareHom = 0 := by
    ext i j
    change squareHom (shiftedTags e (e (Sum.inr i)) (e (Sum.inl j))) = _
    rw [shiftedTags_square]
    simp [markedConstant]
  have hD : D.map squareHom = 0 := by
    ext i j
    change squareHom (shiftedTags e (e (Sum.inr i)) (e (Sum.inr j))) = _
    rw [shiftedTags_square]
    simp [markedConstant]
  let q (i : ι) := (Fintype.equivFin (α i)).symm
  have hv := marked_blocks_product_vanishes A B C D hA hC hD
    (fun i => Fintype.card (α i))
    (fun i j => e.symm (r i (q i j)))
    (fun i j => e.symm (c i (q i j))) hbudget
  have hM : Matrix.fromBlocks A B C D = M := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [hM] at hv
  have heq (i : ι) :
      (M.submatrix (fun j => e.symm (r i (q i j)))
        (fun j => e.symm (c i (q i j)))).det =
      ((shiftedTags e).submatrix (r i) (c i)).det := by
    have hm : M.submatrix (fun j => e.symm (r i (q i j)))
        (fun j => e.symm (c i (q i j))) =
        (((shiftedTags e).submatrix (r i) (c i)).submatrix (q i) (q i)) := by
      ext a b
      simp [M, Matrix.submatrix]
    rw [hm, Matrix.det_submatrix_equiv_self]
  simp_rw [heq] at hv
  exact hv

end LatinQuarter

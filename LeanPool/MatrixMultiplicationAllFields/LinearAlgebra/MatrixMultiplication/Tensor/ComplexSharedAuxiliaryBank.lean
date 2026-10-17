/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexLocalMaps
public import Mathlib.Logic.Equiv.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.Foundation.LabelHierarchySeparation

variable {K I : Type*} [CommSemiring K] [Fintype I]
variable {X Y Z : I → Type*}

def bankTensor (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    Tensor K (∀ i, X i) (∀ i, Y i) (∀ i, Z i) :=
  fun x y z => ∏ i, T i (x i) (y i) (z i)

theorem bankTensor_rankAtMost (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (r : I → ℕ) (h : ∀ i, Tensor.RankAtMost (T i) (r i)) :
    Tensor.RankAtMost (bankTensor T) (∏ i, r i) := by
  classical
  choose a b c hc using h
  let aa : (∀ i, Fin (r i)) → (∀ i, X i) → K :=
    fun f x => ∏ i, a i (f i) (x i)
  let bb : (∀ i, Fin (r i)) → (∀ i, Y i) → K :=
    fun f y => ∏ i, b i (f i) (y i)
  let cc : (∀ i, Fin (r i)) → (∀ i, Z i) → K :=
    fun f z => ∏ i, c i (f i) (z i)
  have heq : bankTensor T =
      fun x y z => ∑ f, Tensor.rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [bankTensor, hc, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [Tensor.rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi, Fintype.card_fin] using
    Tensor.rankAtMost_sum_rankOne aa bb cc

theorem bankTensor_reindex {J : Type*} [Fintype J]
    {X' Y' Z' : J → Type*} (e : I ≃ J)
    (ex : ∀ i, X i ≃ X' (e i)) (ey : ∀ i, Y i ≃ Y' (e i))
    (ez : ∀ i, Z i ≃ Z' (e i))
    (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (S : ∀ j, Tensor K (X' j) (Y' j) (Z' j))
    (compatible : ∀ i x y z, S (e i) (ex i x) (ey i y) (ez i z) = T i x y z) :
    Tensor.pullback (e.piCongr ex) (e.piCongr ey) (e.piCongr ez)
      (bankTensor S) = bankTensor T := by
  funext x y z
  change (∏ j, S j ((e.piCongr ex) x j) ((e.piCongr ey) y j)
    ((e.piCongr ez) z j)) = ∏ i, T i (x i) (y i) (z i)
  rw [← e.prod_comp (fun j => S j ((e.piCongr ex) x j)
    ((e.piCongr ey) y j) ((e.piCongr ez) z j))]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [Equiv.piCongr_apply_apply] using compatible i (x i) (y i) (z i)

theorem bankTensor_reindex_rankAtMost {J : Type*} [Fintype J]
    {X' Y' Z' : J → Type*} (e : I ≃ J)
    (ex : ∀ i, X i ≃ X' (e i)) (ey : ∀ i, Y i ≃ Y' (e i))
    (ez : ∀ i, Z i ≃ Z' (e i))
    (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (S : ∀ j, Tensor K (X' j) (Y' j) (Z' j))
    (compatible : ∀ i x y z, S (e i) (ex i x) (ey i y) (ez i z) = T i x y z)
    {r : ℕ} (hS : Tensor.RankAtMost (bankTensor S) r) :
    Tensor.RankAtMost (bankTensor T) r := by
  rw [← bankTensor_reindex e ex ey ez T S compatible]
  exact hS.pullback _ _ _

end MatrixMultiplication.Foundation.LabelHierarchySeparation

end MatrixMultiplicationAllFields

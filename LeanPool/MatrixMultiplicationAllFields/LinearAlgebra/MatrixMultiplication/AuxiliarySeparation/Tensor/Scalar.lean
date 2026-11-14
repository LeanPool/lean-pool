/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/Scalar.lean`, by Jeroen
Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Natural numbers and rank in the tensor semiring

The natural number `r` is the class of the diagonal scalar tensor with `r`
terms.  Consequently, comparison with `r` in the restriction order is exactly
the existence of a rank decomposition with `r` terms.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- Splitting the diagonal index set splits its scalar tensor into two blocks. -/
theorem scalarTensor_add_reindex (m n : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      finSumFinEquiv finSumFinEquiv (scalarTensor K (m + n)) =
      sumTensor (scalarTensor K m) (scalarTensor K n) := by
  funext x y z
  simp only [Tensor.pullback, scalarTensor,
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective.eq_iff]
  cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]

/-- A diagonal scalar tensor has its evident decomposition into simple terms. -/
theorem scalarTensor_rankAtMost (r : ℕ) : Tensor.RankAtMost (scalarTensor K r) r := by
  classical
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0), (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- The diagonal flattening also gives the matching lower bound. -/
@[simp] theorem exactRank_scalarTensor (r : ℕ) : exactRank (scalarTensor K r) = r := by
  apply le_antisymm (exactRank_le (scalarTensor_rankAtMost r))
  have h := (exactRank_spec (scalarTensor K r)).card_le_of_identity id id id
    (by intro i j; simp [scalarTensor])
  simpa only [Fintype.card_fin] using h

namespace TensorSemiring

/-- Addition of the diagonal index sets is semiring addition. -/
theorem classOf_scalarTensor_add (m n : ℕ) :
    classOf (scalarTensor K (m + n)) =
      classOf (scalarTensor K m) + classOf (scalarTensor K n) := by
  have h := classOf_eq_of_reindex _ _ _ (scalarTensor_add_reindex (K := K) m n)
  exact h.symm.trans (classOf_sum _ _)

theorem classOf_scalarTensor_zero :
    classOf (scalarTensor K 0) = (0 : (TensorClass K)) := by
  have h : scalarTensor K 0 = 0 := by
    funext x
    exact Fin.elim0 x
  rw [h, classOf_zero]

theorem classOf_scalarTensor_one :
    classOf (scalarTensor K 1) = (1 : (TensorClass K)) := by
  change classOf (scalarTensor K 1) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]

/-- Natural numbers in the quotient semiring have their intended tensor meaning. -/
@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf (scalarTensor K r) = (r : (TensorClass K)) := by
  induction r with
  | zero => exact classOf_scalarTensor_zero
  | succ r ih =>
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ,
        classOf_scalarTensor_one, ih] using
        classOf_scalarTensor_add (K := K) r 1

/-- Exact rank decompositions are precisely restrictions of diagonal tensors. -/
theorem rankAtMost_iff_isRestriction_scalarTensor
    {X Y Z : Type*} [Finite X] [Finite Y] [Finite Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    Tensor.RankAtMost T r ↔ IsRestriction T (scalarTensor K r) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Fintype Y := Fintype.ofFinite Y
  let : Fintype Z := Fintype.ofFinite Z
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨(fun x i => a i x), (fun y i => b i y), (fun z i => c i z), ?_⟩
    apply h.trans
    funext x y z
    simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  · rintro ⟨A, B, C, rfl⟩
    exact (scalarTensor_rankAtMost r).restrict A B C

/-- The restriction order below a natural number is exactly the usual rank bound. -/
theorem classOf_le_nat_iff_rankAtMost
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    classOf T ≤ (r : (TensorClass K)) ↔ Tensor.RankAtMost T r := by
  rw [← classOf_scalarTensor r, classOf_le_iff]
  exact (rankAtMost_iff_isRestriction_scalarTensor T r).symm

/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
@[simp] theorem rank_natCast (r : ℕ) : rank (r : (TensorClass K)) = r := by
  rw [← classOf_scalarTensor r, rank_classOf, exactRank_scalarTensor]

/-- The rank is a natural-number upper bound in the restriction order. -/
theorem le_rank (T : (TensorClass K)) : T ≤ (rank T : (TensorClass K)) := by
  induction T using Quotient.inductionOn with
  | h T =>
    change tensorClass T ≤ (exactRank T.coeff : (TensorClass K))
    rw [← classOf_coeff T]
    exact (classOf_le_nat_iff_rankAtMost T.coeff (exactRank T.coeff)).mpr
      (exactRank_spec T.coeff)

/-- The tensor restriction order induces the usual order on natural numbers. -/
@[simp] theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : (TensorClass K)) ≤ (n : (TensorClass K)) ↔ m ≤ n := by
  constructor
  · intro h
    simpa only [rank_natCast] using rank_mono h
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add]
    simpa only [add_zero] using
      add_mono (le_refl (m : (TensorClass K))) (zero_le (k : (TensorClass K)))

/-- A natural multiple of any nonzero tensor contains any prescribed tensor
by restriction. -/
theorem le_nat_mul_of_ne_zero (T S : (TensorClass K)) (hS : S ≠ 0) :
    T ≤ (rank T : (TensorClass K)) * S := by
  apply (le_rank T).trans
  simpa only [mul_one] using
    mul_mono (le_refl (rank T : (TensorClass K))) (one_le_of_ne_zero hS)

end TensorSemiring
end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields

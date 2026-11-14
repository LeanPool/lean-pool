/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/DirectSumClass.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
public import Mathlib.Data.Fintype.Option
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Finite direct sums in the tensor semiring

The tensor class of a block direct sum is the sum of its constituent classes.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.TensorSemiring

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

private theorem classOf_directSum_reindex {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (T : κ → Tensor K X Y Z) (e : ι ≃ κ) :
    classOf (Tensor.directSum (fun i => T (e i))) = classOf (Tensor.directSum T) := by
  apply classOf_eq_of_reindex (Equiv.prodCongr e (Equiv.refl X))
    (Equiv.prodCongr e (Equiv.refl Y)) (Equiv.prodCongr e (Equiv.refl Z))
  funext x y z
  simp [Tensor.pullback, Tensor.directSum, e.injective.eq_iff]

private theorem classOf_directSum_option {ι : Type*} [Fintype ι] [di : DecidableEq ι]
    [dopt : DecidableEq (Option ι)]
    (T : Option ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) =
      classOf (T none) + classOf (Tensor.directSum (fun i => T (some i))) := by
  rw [← classOf_sum]
  symm
  apply classOf_eq_of_reindex optionProdEquiv.symm
    optionProdEquiv.symm optionProdEquiv.symm
  funext x y z
  cases x with
  | inl x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]
  | inr x =>
    cases y <;> cases z <;> simp [Tensor.pullback, Tensor.directSum, sumTensor]

/-- Passing to tensor classes converts every finite block direct sum to a sum. -/
theorem classOf_directSum {ι : Type*} [Fintype ι] [dec : DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    classOf (Tensor.directSum T) = ∑ i, classOf (T i) := by
  have hdec : dec = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst dec
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ T : ι → Tensor K X Y Z,
      classOf (Tensor.directSum T) = ∑ i, classOf (T i)) ?_ ?_ ?_ ι T
  · intro α β _ e ih S
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← classOf_directSum_reindex S e, ih]
    exact e.sum_comp (fun i => classOf (S i))
  · intro S
    have he : (∑ i, classOf (S i)) = 0 := Finset.sum_eq_zero (fun i _ => i.elim)
    rw [he]
    apply (classOf_eq_zero_iff _).mpr
    funext x
    exact x.1.elim
  · intro α _ ih S
    rw [classOf_directSum_option
      (di := fun a b => Classical.propDecidable (a = b))
      (dopt := fun a b => Classical.propDecidable (a = b)), ih, Fintype.sum_option]

end MatrixMultiplication.AuxiliarySeparation.TensorSemiring

end

end MatrixMultiplicationAllFields

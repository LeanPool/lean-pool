/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Convolution/Basic.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization
public import Mathlib.Tactic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The polynomial multiplication tensor

The coefficient tensor `convolution a b` represents multiplication of binary forms
of degrees `a - 1` and `b - 1`, or equivalently ordinary coefficient convolution.
The output leg has `a + b - 1` coordinates.  The definitions also make sense when
an input dimension is zero, while the nonzero and full-output-support statements
use the positive dimensions assumed in Section 5 of the paper.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

variable (K) in
/-- The tensor `C(a,b)` of Section 5, in monomial coefficient coordinates. -/
def convolution (a b : ℕ) : Tensor K (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp] theorem convolution_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution K a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

@[simp] theorem convolution_ne_zero_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution K a b i j k ≠ 0 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

@[simp] theorem convolution_eq_one_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution K a b i j k = 1 ↔ i.val + j.val = k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

@[simp] theorem convolution_eq_zero_iff {a b : ℕ}
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution K a b i j k = 0 ↔ i.val + j.val ≠ k.val := by
  simp only [convolution]
  split_ifs <;> simp_all

/-- Every pair of input monomials has a valid output coordinate. -/
def convolutionOutput {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a + b - 1) :=
  ⟨i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩

@[simp] theorem convolution_at_output {a b : ℕ} (i : Fin a) (j : Fin b) :
    convolution K a b i j (convolutionOutput i j) = 1 := by
  simp [convolutionOutput]

/-- Every output monomial of the expected degree occurs in the product. -/
theorem convolution_output_supported {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (k : Fin (a + b - 1)) :
    ∃ (i : Fin a) (j : Fin b), convolution K a b i j k = 1 := by
  by_cases hk : k.val < a
  · exact ⟨⟨k.val, hk⟩, ⟨0, hb⟩, by simp⟩
  · have hk' := k.isLt
    refine ⟨⟨a - 1, by omega⟩, ⟨k.val - (a - 1), by omega⟩, ?_⟩
    apply (convolution_eq_one_iff _ _ _).mpr
    dsimp
    omega

theorem convolution_nonzero {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    convolution K a b ≠ 0 := by
  intro hz
  have hc := congrFun (congrFun (congrFun hz ⟨0, ha⟩) ⟨0, hb⟩)
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩)
  change convolution K a b ⟨0, ha⟩ ⟨0, hb⟩
    (convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩) = 0 at hc
  rw [convolution_at_output] at hc
  exact one_ne_zero hc

theorem convolution_nonzero_iff (a b : ℕ) :
    convolution K a b ≠ 0 ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    constructor
    · by_contra ha
      have ha' : a = 0 := by omega
      subst a
      apply h
      funext i
      exact Fin.elim0 i
    · by_contra hb
      have hb' : b = 0 := by omega
      subst b
      apply h
      funext i j
      exact Fin.elim0 j
  · rintro ⟨ha, hb⟩
    exact convolution_nonzero ha hb

/-- Commuting the two inputs only casts the equal output dimensions. -/
theorem convolution_comm (a b : ℕ) (i : Fin a) (j : Fin b)
    (k : Fin (a + b - 1)) :
    convolution K a b i j k =
      convolution K b a j i (Fin.cast (by omega) k) := by
  simp only [convolution, Fin.val_cast, Nat.add_comm]

/-- The boundary tensor `C(1,b)` has the coefficient matrix of a dot product. -/
theorem convolution_one_left (b : ℕ) (i : Fin 1) (j : Fin b)
    (k : Fin (1 + b - 1)) :
    convolution K 1 b i j k = if j.val = k.val then 1 else 0 := by
  simp [convolution]

/-- The other boundary tensor has the same coordinate identity. -/
theorem convolution_one_right (a : ℕ) (i : Fin a) (j : Fin 1)
    (k : Fin (a + 1 - 1)) :
    convolution K a 1 i j k = if i.val = k.val then 1 else 0 := by
  simp [convolution]

/-- Relabel the output of `C(1,b)` by its actual dimension `b`. -/
def convolutionOneOutputEquiv (b : ℕ) : Fin b ≃ Fin (1 + b - 1) :=
  finCongr (by omega)

/-- Relabel the single input coordinate of `C(1,b)` by `Unit`. -/
def convolutionOneInputEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _i := Subsingleton.elim _ _

/-- `C(1,b)` is the dot-product tensor with the singleton on the first leg. -/
theorem convolution_one_left_dotPairing (b : ℕ) :
    Tensor.pullback convolutionOneInputEquiv (Equiv.refl (Fin b))
      (convolutionOneOutputEquiv b) (convolution K 1 b) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin b))) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff]

/-- Relabel the output of `C(a,1)` by its actual dimension `a`. -/
def convolutionRightOneOutputEquiv (a : ℕ) : Fin a ≃ Fin (a + 1 - 1) :=
  finCongr (by omega)

/-- `C(a,1)` is the dot-product tensor with the singleton on the second leg. -/
theorem convolution_one_right_dotPairing (a : ℕ) :
    Tensor.pullback (Equiv.refl (Fin a)) convolutionOneInputEquiv
      (convolutionRightOneOutputEquiv a) (convolution K a 1) =
      Tensor.cyclic (Tensor.dotPairing (K := K) (Fin a)) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionRightOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff, eq_comm]

/-- Contracting the coefficient tensor computes ordinary finite convolution. -/
theorem contract_convolution {a b : ℕ} (x : Fin a → K) (y : Fin b → K)
    (k : Fin (a + b - 1)) :
    Tensor.contract (convolution K a b) x y k =
      ∑ i : Fin a, ∑ j : Fin b,
        if i.val + j.val = k.val then x i * y j else 0 := by
  simp [Tensor.contract, convolution, ite_mul]

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields

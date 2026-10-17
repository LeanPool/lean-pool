/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.ProgramComposition

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

def zeroPadMatrix {n : ℕ} (m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) = A i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {n m : ℕ} (h : n ≤ m)
    (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    (zeroPadMatrix m A * zeroPadMatrix m B) (Fin.castLE h i) (Fin.castLE h k) =
      (A * B) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin m,
        zeroPadMatrix m A (Fin.castLE h i) j *
          zeroPadMatrix m B j (Fin.castLE h k)) =
        ∑ j : Fin n,
          zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) *
            zeroPadMatrix m B (Fin.castLE h j) (Fin.castLE h k) := by
      apply sum_fin_castLE_of_zero h
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin n, A i j * B j k := by simp

def padSource {n m : ℕ} : MatrixInput m → MatrixInput n ⊕ ℂ
  | .inl (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (i, j) => if hi : i.val < n then
      if hj : j.val < n then .inl (.inr (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0

theorem padSource_eval {n m : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (fun x : MatrixInput m => Sum.elim (matrixInputs A B) id (padSource x)) =
      matrixInputs (zeroPadMatrix m A) (zeroPadMatrix m B) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨i, j⟩
  all_goals
    by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]

namespace MatrixAlgorithm

def pad {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) : MatrixAlgorithm n where
  registers := P.registers
  program := P.program.mapSource (padSource (n := n))
  output := fun i k => P.output (Fin.castLE h i) (Fin.castLE h k)

theorem pad_correct {n m : ℕ} (h : n ≤ m) {P : MatrixAlgorithm m}
    (hP : P.Correct) : (pad h P).Correct := by
  intro A B
  funext i k
  change (P.program.mapSource (padSource (n := n))).eval (matrixInputs A B)
    (P.output (Fin.castLE h i) (Fin.castLE h k)) = (A * B) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix m A) (zeroPadMatrix m B)) (Fin.castLE h i)) (Fin.castLE h k)
  exact hentry.trans (zeroPadMatrix_mul h A B i k)

@[simp] theorem pad_cost_eq {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) :
    (pad h P).cost = P.cost :=
  Program.cost_mapSource (padSource (n := n)) P.program

theorem exists_restrict {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m)
    (hP : P.Correct) : ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad h P, pad_correct h hP, (pad_cost_eq h P).le⟩

end MatrixAlgorithm

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields

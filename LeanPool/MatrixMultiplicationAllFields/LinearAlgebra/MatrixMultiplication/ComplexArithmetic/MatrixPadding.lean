/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.ProgramComposition

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic interfaces specialized from the shared field-generic implementation. -/

@[expose] public section

namespace MatrixMultiplicationAllFields

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

/-- Embed a smaller matrix in a larger rectangle by filling the remaining entries with zero. -/
abbrev zeroPadMatrix {n : ℕ} (m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  MatrixMultiplication.Arithmetic.zeroPadMatrix m m A

theorem zeroPadMatrix_castLE {n m : ℕ} (h : n ≤ m)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    zeroPadMatrix m A (Fin.castLE h i) (Fin.castLE h j) = A i j :=
  MatrixMultiplication.Arithmetic.zeroPadMatrix_castLE h h A i j

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → ℂ)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) :=
  MatrixMultiplication.Arithmetic.sum_fin_castLE_of_zero h f hf

theorem zeroPadMatrix_mul {n m : ℕ} (h : n ≤ m)
    (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) :
    (zeroPadMatrix m A * zeroPadMatrix m B) (Fin.castLE h i) (Fin.castLE h k) =
      (A * B) i k :=
  MatrixMultiplication.Arithmetic.zeroPadMatrix_mul h h h A B i k

/-- Route a padded input position to its original entry or the scalar zero. -/
abbrev padSource {n m : ℕ} : MatrixInput m → MatrixInput n ⊕ ℂ :=
  MatrixMultiplication.Arithmetic.padSource (a := n) (b := n) (c := n)

theorem padSource_eval {n m : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (fun x : MatrixInput m => Sum.elim (matrixInputs A B) id (padSource x)) =
      matrixInputs (zeroPadMatrix m A) (zeroPadMatrix m B) :=
  MatrixMultiplication.Arithmetic.padSource_eval A B

namespace MatrixAlgorithm

/-- Run a larger matrix algorithm on zero-padded inputs and retain the requested outputs. -/
abbrev pad {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) : MatrixAlgorithm n :=
  MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad h h h P

theorem pad_correct {n m : ℕ} (h : n ≤ m) {P : MatrixAlgorithm m}
    (hP : P.Correct) : (pad h P).Correct :=
  MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad_correct h h h hP

theorem pad_cost_eq {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m) :
    (pad h P).cost = P.cost :=
  MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad_cost_eq h h h P

theorem exists_restrict {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm m)
    (hP : P.Correct) : ∃ Q : MatrixAlgorithm n, Q.Correct ∧ Q.cost ≤ P.cost :=
  MatrixMultiplication.Arithmetic.MatrixAlgorithm.exists_restrict h h h P hP

end MatrixAlgorithm

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields

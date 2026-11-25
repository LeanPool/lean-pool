/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.ProgramComposition
public import LeanPool.ExactMatrixExponents.LinearAlgebra.SpectralBooks.FormalCircuit
public import Mathlib.Algebra.MvPolynomial.Monad

/-! # Formal polynomial semantics of program substitution -/

@[expose] public section

namespace MatrixMultiplicationAllFields
namespace SpectralBooks

open MatrixMultiplicationAllFields.MatrixMultiplication

open Arithmetic MvPolynomial

variable {F I J : Type*} [Field F]

private theorem registerPolynomial_substitute_all {r s : ℕ} (p : Program F I r)
    (q : Program F J s) (inputs : J → Fin r) :
    (∀ i, registerPolynomial (p.substitute q inputs).program
      ((p.substitute q inputs).oldOutput i) = registerPolynomial p i) ∧
    (∀ i, registerPolynomial (p.substitute q inputs).program
      ((p.substitute q inputs).output i) =
      bind₁ (fun j => registerPolynomial p (inputs j)) (registerPolynomial q i)) := by
  induction q with
  | nil => exact ⟨fun _ => rfl, fun i => i.elim0⟩
  | step q g ih =>
    obtain ⟨hold, hnew⟩ := ih
    constructor
    · intro i
      cases g <;> exact hold i
    · intro i
      cases g <;> refine Fin.cases ?_ (fun j => hnew j) i
      case literal value =>
        change C value = bind₁ _ (C value)
        rw [bind₁_C_right]
      case input index =>
        rw [registerPolynomial_zero, gatePolynomial, bind₁_X_right]
        exact hold (inputs index)
      case add left right =>
        rw [registerPolynomial_zero, gatePolynomial, map_add]
        exact congrArg₂ (· + ·) (hnew left) (hnew right)
      case sub left right =>
        rw [registerPolynomial_zero, gatePolynomial, map_sub]
        exact congrArg₂ (· - ·) (hnew left) (hnew right)
      case mul left right =>
        rw [registerPolynomial_zero, gatePolynomial, map_mul]
        exact congrArg₂ (· * ·) (hnew left) (hnew right)

/-- Substitution into a program acts on its register polynomials by polynomial substitution. -/
theorem registerPolynomial_substitute {r s : ℕ} (p : Program F I r)
    (q : Program F J s) (inputs : J → Fin r) (j : Fin s) :
    registerPolynomial (p.substitute q inputs).program ((p.substitute q inputs).output j) =
      bind₁ (fun i => registerPolynomial p (inputs i)) (registerPolynomial q j) :=
  (registerPolynomial_substitute_all p q inputs).2 j

end SpectralBooks
end MatrixMultiplicationAllFields

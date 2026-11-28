/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.Denominators
public import LeanPool.MathFin.Models.ModelFree.SVI.MatrixSignature

/-! # The signature test survives clearing denominators

Part of the SVI polynomial-sign certificate (#174).

The Hermite matrices are symmetric. The cleared matrix, which is `leadingCoeff^38` (a positive
factor) times the Hermite matrix when `leadingCoeff ≠ 0`, the size is `n ≤ 9` and the weight has
degree at most `22`, has the same signature test (`clearedHermite_signature`).
`certificateMatrix_signature` specialises this to the four certificate matrices of a nonconstant
polynomial of degree at most ten.

## Main results

* `hermite_symmetric`: the Hermite matrix `hermite f q n` is symmetric.
* `clearedHermite_signature`: for `leadingCoeff ≠ 0`, `n ≤ 9` and `q.natDegree ≤ 22`, the cleared
  matrix has the same `signatureTest` as `hermite f q n`.
* `derivative_size_bound`, `weight_size_bound`: for `natDegree ≤ 10`, the derivative has degree at
  most `9` and the four weights have degree at most `22`.
* `certificateMatrix_signature`: for a nonconstant `P` of degree at most ten, each of the four
  certificate matrices has the same `signatureTest` as the corresponding Hermite matrix.

## Tags

Hermite matrix, signature test, cleared denominators, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

theorem hermite_symmetric (f q : ℝ[X]) (n : ℕ) : (hermite f q n).IsSymm := by
  ext i j
  simp [hermite, Matrix.transpose_apply, Nat.add_comm]

/-- Clearing all companion denominators preserves the exact signature test. -/
theorem clearedHermite_signature (f q : ℝ[X]) (n : ℕ)
    (hf : f.leadingCoeff ≠ 0) (hn : n ≤ 9) (hq : q.natDegree ≤ 22) :
    signatureTest (clearedHermite f q n) = signatureTest (hermite f q n) := by
  rw [clearedHermite_eq_smul f q n hf hn hq]
  exact signatureTest_smul_pos _ (hermite_symmetric f q n) _ (clearing_factor_pos f hf)

theorem derivative_size_bound (P : ℝ[X]) (hd : P.natDegree ≤ 10) :
    P.derivative.natDegree ≤ 9 := by
  have hh := natDegree_derivative_le P
  omega

theorem weight_size_bound (P : ℝ[X]) (hd : P.natDegree ≤ 10) (i : Fin 4) :
    (![X^2*P^2, X*P^2, X^2*P, X*P] i).natDegree ≤ 22 := by
  fin_cases i <;> dsimp
  all_goals
    have h1 := @natDegree_mul_le ℝ _ (X^2) (P^2)
    have h2 := @natDegree_mul_le ℝ _ X (P^2)
    have h3 := @natDegree_mul_le ℝ _ (X^2) P
    have h4 := @natDegree_mul_le ℝ _ X P
    have hp := @natDegree_pow_le ℝ _ P 2
    simp only [natDegree_X_pow, natDegree_X] at *
    omega

theorem certificateMatrix_signature (P : ℝ[X]) (hd : P.natDegree ≤ 10)
    (hn : P.natDegree ≠ 0) (i : Fin 4) :
    signatureTest (certificateMatrices P i) =
      signatureTest (hermite P.derivative (![X^2*P^2, X*P^2, X^2*P, X*P] i)
        P.derivative.natDegree) := by
  have hf : P.derivative.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr
    (derivative_ne_zero.mpr hn)
  have hh := clearedHermite_signature P.derivative
    (![X^2*P^2, X*P^2, X^2*P, X*P] i) P.derivative.natDegree hf
    (derivative_size_bound P hd) (weight_size_bound P hd i)
  fin_cases i <;> simpa [certificateMatrices] using hh

end SVI
end MathFin

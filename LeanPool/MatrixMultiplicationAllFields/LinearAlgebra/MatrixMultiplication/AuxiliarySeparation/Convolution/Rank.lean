/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Convolution/Rank.lean`, by
Jeroen Zuiddam, 2026: evaluation nodes taken from an embedding `ℕ ↪ K` (upstream: `0, …, a+b-2`
in ℂ); `ℂ` replaced by a field `K`; removed the ℂ-only lemma `convolution_borderRankAtMost`
(not needed by the retained proof); `[IsAlgClosed K]` is assumed by the declarations that use it;
docstrings updated from ℂ to `K`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Polynomial convolution by evaluation and interpolation

Evaluating the two input polynomials at `a + b - 1` distinct points of `K`,
then interpolating their product, expresses the convolution tensor as a sum
of `a + b - 1` rank-one tensors. This is the polynomial multiplication rank
upper bound used in Section 5.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



open scoped BigOperators
open Polynomial

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Recover each monomial coefficient from evaluations at distinct nodes. -/
lemma monomial_coeff_eq_sum_interpolation {n m : ℕ} (hm : m < n)
    (v : Fin n → K) (hv : Function.Injective v) (k : ℕ) :
    (if m = k then (1 : K) else 0) =
      ∑ r : Fin n, v r ^ m * (Lagrange.basis Finset.univ v r).coeff k := by
  have hdeg : (X ^ m : K[X]).degree < (Finset.univ : Finset (Fin n)).card := by
    simpa using hm
  have hpoly := Lagrange.eq_interpolate (f := (X ^ m : K[X])) hv.injOn hdeg
  have hcoeff := congrArg (fun p : K[X] => p.coeff k) hpoly
  simpa only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow, eq_comm] using hcoeff

/-- Evaluation at distinct nodes and Lagrange interpolation give an explicit
rank-one decomposition of polynomial convolution. -/
theorem convolution_eq_sum_rankOne {a b : ℕ}
    (v : Fin (a + b - 1) → K) (hv : Function.Injective v) :
    convolution K a b = fun i j k => ∑ r : Fin (a + b - 1),
      Tensor.rankOne (fun i : Fin a => v r ^ i.val)
        (fun j : Fin b => v r ^ j.val)
        (fun k : Fin (a + b - 1) => (Lagrange.basis Finset.univ v r).coeff k.val)
        i j k := by
  funext i j k
  have hij : i.val + j.val < a + b - 1 := (convolutionOutput i j).isLt
  simpa only [convolution_apply, Tensor.rankOne, pow_add] using
    monomial_coeff_eq_sum_interpolation hij v hv k.val

/-- The convolution tensor `C(a,b)` has rank at most `a + b - 1` over `K`. -/
theorem convolution_rankAtMost [IsAlgClosed K] (a b : ℕ) :
    Tensor.RankAtMost (convolution K a b) (a + b - 1) := by
  let v : Fin (a + b - 1) → K := fun r => Infinite.natEmbedding K r.val
  have hv : Function.Injective v := by
    intro i j h
    exact Fin.ext ((Infinite.natEmbedding K).injective h)
  rw [convolution_eq_sum_rankOne v hv]
  simpa using Tensor.rankAtMost_sum_rankOne
    (fun r (i : Fin a) => v r ^ i.val)
    (fun r (j : Fin b) => v r ^ j.val)
    (fun r (k : Fin (a + b - 1)) => (Lagrange.basis Finset.univ v r).coeff k.val)

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields

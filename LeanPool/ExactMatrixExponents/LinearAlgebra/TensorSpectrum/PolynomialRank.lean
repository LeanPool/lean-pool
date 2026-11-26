/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialTensors
public import Lean.Elab.Tactic.Omega

/-!
# Rank of polynomial multiplication by interpolation

An evaluation family and its interpolation coefficients give one rank-one term
per node. All interpolation identities are supplied by the coefficient model.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors

variable {K : Type*} [CommSemiring K] [Nontrivial K]

/-- The evaluation and interpolation witnesses give the usual convolution rank bound. -/
theorem polynomialTensor_rankAtMost_of_interpolation (a b : ℕ)
    (nodes : Fin (a + b - 1) → K) (weight : Fin (a + b - 1) → ℕ → K)
    (coefficientIdentity : ∀ (p : Polynomial K) (d : ℕ),
      p.degree < Fintype.card (Fin (a + b - 1)) →
      p.coeff d = ∑ t, p.eval (nodes t) * weight t d) :
    Tensor.RankAtMost (polynomialTensor (K := K) a b) (a + b - 1) := by
  classical
  refine ⟨(fun t i => nodes t ^ i.val),
    (fun t j => nodes t ^ j.val),
    (fun t k => weight t k.val), ?_⟩
  funext i j k
  have hsum : i.val + j.val < a + b - 1 := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hdegree : ((Polynomial.X : Polynomial K) ^ (i.val + j.val)).degree <
      Fintype.card (Fin (a + b - 1)) := by
    rw [Polynomial.degree_X_pow, Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr hsum
  have hcoeff := coefficientIdentity
    ((Polynomial.X : Polynomial K) ^ (i.val + j.val)) k.val hdegree
  refine (polynomialTensor_eq_coeff (K := K) a b i j k).trans ?_
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Tensor.rankOne, pow_add]
    using hcoeff

end MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors

/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic

/-!
# Noncommutative arithmetic-geometric means

Definitions for Yimin Zhong, arXiv:2610.04874v1. Products are indexed by
ordered injective tuples, retaining the noncommutative order of multiplication.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- Ordered distinct-index product sum in equation (1). -/
noncomputable def distinctProductSum {R : Type*} [Semiring R] (n m : ℕ)
    (A : Fin n → R) : R :=
  ∑ f : Fin m ↪ Fin n, (List.ofFn fun j ↦ A (f j)).prod

/-- Normalized without-replacement product average, equation (5). -/
noncomputable def withoutReplacementMean {R : Type*} [Ring R] [Algebra ℝ R]
    (n m : ℕ) (A : Fin n → R) : R :=
  (((n - m).factorial : ℝ) / (n.factorial : ℝ)) • distinctProductSum n m A

/-- The number of ordered distinct-index tuples is the descending factorial. -/
theorem card_distinct_tuples (n m : ℕ) :
    Fintype.card (Fin m ↪ Fin n) = n.descFactorial m := by
  simp

/-- The paper's factorial normalization is the reciprocal of the tuple count. -/
theorem normalization_eq_inv_card {n m : ℕ} (hmn : m ≤ n) :
    ((n - m).factorial : ℝ) / (n.factorial : ℝ) =
      (Fintype.card (Fin m ↪ Fin n) : ℝ)⁻¹ := by
  rw [card_distinct_tuples]
  have h := Nat.factorial_mul_descFactorial hmn
  have hc : ((n - m).factorial : ℝ) * (n.descFactorial m : ℝ) = n.factorial :=
    by exact_mod_cast h
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hd : (n.descFactorial m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hmn))
  field_simp
  nlinarith [hc]

/-- Empty products give the identity. -/
@[simp] theorem distinctProductSum_zero {R : Type*} [Semiring R] (n : ℕ)
    (A : Fin n → R) : distinctProductSum n 0 A = 1 := by
  classical
  simp [distinctProductSum]

/-- For one factor, ordered distinct-index summation is ordinary summation. -/
@[simp] theorem distinctProductSum_one {R : Type*} [Semiring R] (n : ℕ)
    (A : Fin n → R) : distinctProductSum n 1 A = ∑ i, A i := by
  classical
  simp only [distinctProductSum, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one]
  exact Fintype.sum_equiv Equiv.uniqueEmbeddingEquivResult _ _ (fun _ ↦ rfl)

/-- The average of empty products is the identity. -/
@[simp] theorem withoutReplacementMean_zero {R : Type*} [Ring R] [Algebra ℝ R]
    (n : ℕ) (A : Fin n → R) : withoutReplacementMean n 0 A = 1 := by
  simp [withoutReplacementMean, show (n.factorial : ℝ) ≠ 0 by positivity]

/-- The length-one average is the arithmetic mean. -/
theorem withoutReplacementMean_one {R : Type*} [Ring R] [Algebra ℝ R]
    {n : ℕ} (hn : 0 < n) (A : Fin n → R) :
    withoutReplacementMean n 1 A = (n : ℝ)⁻¹ • ∑ i, A i := by
  rw [withoutReplacementMean, normalization_eq_inv_card hn,
    distinctProductSum_one, card_distinct_tuples, Nat.descFactorial_one]

/-- The constant-identity family attains the upper bound for every allowed length. -/
theorem withoutReplacementMean_identity {R : Type*} [Ring R] [Algebra ℝ R]
    {n m : ℕ} (hmn : m ≤ n) : withoutReplacementMean n m (fun _ ↦ (1 : R)) = 1 := by
  classical
  have hd : (Fintype.card (Fin m ↪ Fin n) : ℝ) ≠ 0 := by
    rw [card_distinct_tuples]
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hmn))
  rw [withoutReplacementMean, normalization_eq_inv_card hmn]
  simp only [distinctProductSum, List.ofFn_const, List.prod_replicate, one_pow,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hd, one_smul]

end NoncommutativeAMGM

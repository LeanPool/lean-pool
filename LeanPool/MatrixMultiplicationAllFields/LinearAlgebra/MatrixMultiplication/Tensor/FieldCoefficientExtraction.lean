/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Lean.Elab.Tactic.Omega

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.FieldCoefficientExtraction

variable {F X Y Z : Type*}

theorem coeff_triple [CommSemiring F] (a b c : Polynomial F) (d : ℕ) :
    (a * b * c).coeff d =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        (if j.val ≤ d - i.val then a.coeff (d - i.val - j.val) else 0) *
          b.coeff j.val * c.coeff i.val := by
  classical
  rw [show a * b * c = c * (b * a) by ring]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
      b.coeff j * c.coeff i.val) (d + 1)]
  symm
  calc
    (∑ j ∈ Finset.range (d + 1),
        (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
          b.coeff j * c.coeff i.val) =
        ∑ j ∈ Finset.range (d - i.val + 1),
          (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
            b.coeff j * c.coeff i.val := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjnot
      have h : ¬ j ≤ d - i.val := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hjnot
      simp [h]
    _ = ∑ j ∈ Finset.range (d - i.val + 1),
        c.coeff i.val * (b.coeff j * a.coeff (d - i.val - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      ring

theorem rankAtMost_coeff [CommSemiring F]
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : Tensor.RankAtMost P r) (d : ℕ) :
    Tensor.RankAtMost (fun x y z => (P x y z).coeff d) ((d + 1) ^ 2 * r) := by
  classical
  rcases hP with ⟨a, b, c, rfl⟩
  let aa : (Fin r × Fin (d + 1) × Fin (d + 1)) → X → F :=
    fun v x => if v.2.2.val ≤ d - v.2.1.val then
      (a v.1 x).coeff (d - v.2.1.val - v.2.2.val) else 0
  let bb : (Fin r × Fin (d + 1) × Fin (d + 1)) → Y → F :=
    fun v y => (b v.1 y).coeff v.2.2.val
  let cc : (Fin r × Fin (d + 1) × Fin (d + 1)) → Z → F :=
    fun v z => (c v.1 z).coeff v.2.1.val
  have heq : (fun x y z => (∑ j, Tensor.rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ v, Tensor.rankOne (aa v) (bb v) (cc v) x y z := by
    funext x y z
    simp only [Polynomial.finsetSum_coeff, Tensor.rankOne, Fintype.sum_prod_type,
      coeff_triple, aa, bb, cc]
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using Tensor.rankAtMost_sum_rankOne aa bb cc

theorem rank_power [Field F] {T : Tensor F X Y Z} {r d D : ℕ}
    (A : Tensor.PolynomialApproximation T r d D) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power T n) ((d * n + 1) ^ 2 * r ^ n) := by
  have h := rankAtMost_coeff (A.power n).rank_bound (d * n)
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq] at h
  exact h

end MatrixMultiplication.FieldCoefficientExtraction

end

end MatrixMultiplicationAllFields

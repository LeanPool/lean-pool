/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.LocalTensor
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import Mathlib.Tactic.Choose

/-!
# Local restrictions of sums and polynomial powers

Linear combinations of restrictions use one independent source copy per
summand. Coefficients and evaluations of a polynomial word use the actual tensor power.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixExponent
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.TensorSpectrum.RestrictionInterpolation

variable {R : Type*} [CommSemiring R]

section RestrictionAlgebra

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Independent maps on each full source copy may have the same target. The
result is the sum of their restricted tensors, with no cross-copy terms. -/
theorem restrict_directSum_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor R X Y Z)
    (a : ι → U → X → R) (b : ι → V → Y → R) (c : ι → W → Z → R) :
    Tensor.restrict (fun u x => a x.1 u x.2)
      (fun v y => b y.1 v y.2) (fun w z => c z.1 w z.2)
      (Tensor.directSum T) =
      fun u v w => ∑ i, Tensor.restrict (a i) (b i) (c i) (T i) u v w := by
  classical
  funext u v w
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
    ite_and, mul_ite]

/-- Scaling one local map scales the whole restricted coefficient tensor. -/
theorem restrict_scale_first (T : Tensor R X Y Z)
    (a : U → X → R) (b : V → Y → R) (c : W → Z → R) (s : R) :
    Tensor.restrict (fun u x => s * a u x) b c T =
      fun u v w => s * Tensor.restrict a b c T u v w := by
  funext u v w
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Tensor products of the local maps give a local restriction of every power.
Every input coordinate in every position is summed independently. -/
theorem restrict_power (T : Tensor R X Y Z)
    (a : U → X → R) (b : V → Y → R) (c : W → Z → R) (j : ℕ) :
    Tensor.restrict
      (fun u x => ∏ i, a (u i) (x i))
      (fun v y => ∏ i, b (v i) (y i))
      (fun w z => ∏ i, c (w i) (z i)) (Tensor.power T j) =
      Tensor.power (Tensor.restrict a b c T) j := by
  funext u v w
  simp only [Tensor.restrict, Tensor.power, Fintype.prod_sum,
    Finset.prod_mul_distrib]

theorem power_mem_restrictionOrbit {T : Tensor R X Y Z}
    {S : Tensor R U V W} (h : S ∈ LocalTensor.orbit T) (j : ℕ) :
    Tensor.power S j ∈ LocalTensor.orbit (Tensor.power T j) := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨(fun u x => ∏ i, a (u i) (x i)),
    (fun v y => ∏ i, b (v i) (y i)),
    (fun w z => ∏ i, c (w i) (z i)), (restrict_power T a b c j).symm⟩

end RestrictionAlgebra

section Coefficients

variable {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Combine actual restrictions of one tensor by scaling the maps from each source copy. -/
theorem weighted_sum_of_restrictions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Tensor R X Y Z) (A : ι → Tensor R U V W) (weight : ι → R)
    (hA : ∀ i, A i ∈ LocalTensor.orbit T) :
    (fun u v w => ∑ i, weight i * A i u v w) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : ι => T)) := by
  classical
  choose a b c he using hA
  refine ⟨fun u x => weight x.1 * a x.1 u x.2,
    fun v y => b y.1 v y.2, fun w z => c z.1 w z.2, ?_⟩
  rw [restrict_directSum_sum (fun _ : ι => T) (fun i u x => weight i * a i u x) b c]
  funext u v w
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i, restrict_scale_first]

end Coefficients

variable {U V W : Type*}

theorem polynomial_power_constant (P : Tensor (Polynomial R) U V W) (j : ℕ) :
    (fun u v w => (Tensor.power P j u v w).coeff 0) =
      Tensor.power (fun u v w => (P u v w).coeff 0) j := by
  funext u v w
  simp only [Tensor.power, Polynomial.coeff_zero_prod]

theorem polynomial_power_eval (P : Tensor (Polynomial R) U V W) (j : ℕ) (t : R) :
    (fun u v w => (Tensor.power P j u v w).eval t) =
      Tensor.power (fun u v w => (P u v w).eval t) j := by
  funext u v w
  simp only [Tensor.power, Polynomial.eval_prod]

theorem polynomial_power_degree (P : Tensor (Polynomial R) U V W) (K j : ℕ)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (u : Fin j → U) (v : Fin j → V) (w : Fin j → W) :
    (Tensor.power P j u v w).degree ≤ K * j := by
  apply Polynomial.degree_le_of_natDegree_le
  calc
    (Tensor.power P j u v w).natDegree ≤
        ∑ i, (P (u i) (v i) (w i)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin j, K := by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_le_of_degree_le (hdegree (u i) (v i) (w i))
    _ = K * j := by simp [Nat.mul_comm]

/-- Lift coefficient extraction to tensor powers and recover the constant tensor. -/
theorem polynomial_power_mem_restrictionOrbit
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor R X Y Z) (D : Tensor R U V W)
    (P : Tensor (Polynomial R) U V W) (K : ℕ)
    (hconstant : ∀ u v w, (P u v w).coeff 0 = D u v w)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (goodNode : R → Prop)
    (heval : ∀ t, goodNode t →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (j : ℕ)
    (extract :
      (∀ t, goodNode t → (fun u v w => (Tensor.power P j u v w).eval t) ∈
        LocalTensor.orbit (Tensor.power T j)) →
      (∀ u v w, (Tensor.power P j u v w).degree < Fintype.card (Fin (K * j + 1))) →
      (fun u v w => (Tensor.power P j u v w).coeff 0) ∈ LocalTensor.orbit
        (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j))) :
    Tensor.power D j ∈ LocalTensor.orbit
      (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j)) := by
  have hevalpower (t : R) (ht : goodNode t) :
      (fun u v w => (Tensor.power P j u v w).eval t) ∈
        LocalTensor.orbit (Tensor.power T j) := by
    rw [polynomial_power_eval]
    exact power_mem_restrictionOrbit (heval t ht) j
  have hdegreepower (u v w) : (Tensor.power P j u v w).degree <
      Fintype.card (Fin (K * j + 1)) := by
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (polynomial_power_degree P K j hdegree u v w)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (K * j)))
  have h := extract hevalpower hdegreepower
  rw [polynomial_power_constant, show (fun u v w => (P u v w).coeff 0) = D from
    funext fun u => funext fun v => funext fun w => hconstant u v w] at h
  exact h

end MatrixMultiplicationAllFields.TensorSpectrum.RestrictionInterpolation

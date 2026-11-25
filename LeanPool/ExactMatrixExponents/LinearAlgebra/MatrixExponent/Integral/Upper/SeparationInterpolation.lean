/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Interpolation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import Mathlib.Tactic.Choose
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.RestrictionInterpolation

/-!
# Polynomial coefficient extraction by actual restrictions

Every coefficient of a bounded polynomial tensor is a linear combination of
evaluations at common interpolation nodes. If those evaluations are local
restrictions of one source tensor, the coefficient is a restriction of the
full direct sum of that many source copies. Applying this to tensor powers
gives the linear interpolation overhead required by restriction-monotone
characters. No continuity of a character on a Euclidean closure is assumed.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.Separation

export MatrixMultiplicationAllFields.TensorSpectrum.RestrictionInterpolation
  (restrict_directSum_sum restrict_scale_first restrict_power power_mem_restrictionOrbit
    polynomial_power_constant polynomial_power_eval polynomial_power_degree)

section Interpolation

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Interpolation at any common family of distinct nonzero nodes turns actual
restriction witnesses for the evaluations into one restriction witness for the
coefficient. The full number of source copies is charged explicitly. -/
theorem polynomial_coeff_mem_restrictionOrbit {n : ℕ}
    (T : Tensor O X Y Z) (P : Tensor (Polynomial O) U V W)
    (nodes : (Fin n) → O) (hinj : IsUnit (Matrix.vandermonde nodes).det)
    (hnonzero : ∀ i, IsUnit (nodes i))
    (heval : ∀ t : O, IsUnit t →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (hdegree : ∀ u v w, (P u v w).degree < Fintype.card (Fin n)) (d : ℕ) :
    (fun u v w => (P u v w).coeff d) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : (Fin n) => T)) := by
  classical
  let weight : (Fin n) → O := fun i => Integral.weight nodes i d
  have h := TensorSpectrum.RestrictionInterpolation.weighted_sum_of_restrictions
    T (fun i u v w => (P u v w).eval (nodes i)) weight
    (fun i => heval (nodes i) (hnonzero i))
  have hcoeff : (fun u v w => (P u v w).coeff d) =
      (fun u v w => ∑ i, weight i * (P u v w).eval (nodes i)) := by
    funext u v w
    simpa only [weight, mul_comm] using Integral.interpolate nodes hinj (P u v w) d (hdegree u v w)
  rwa [hcoeff]

/-- The finite interpolation bound before applying any character. For every
power `j`, exactly `K*j+1` copies of the power of the original source suffice.
The infinite field supplies distinct nonzero nodes. -/
theorem polynomial_power_mem_restrictionOrbit
    (T : Tensor O X Y Z) (D : Tensor O U V W)
    (P : Tensor (Polynomial O) U V W) (K : ℕ)
    (hconstant : ∀ u v w, (P u v w).coeff 0 = D u v w)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (heval : ∀ t : O, IsUnit t →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (j : ℕ) :
    Tensor.power D j ∈ LocalTensor.orbit
      (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j)) := by
  classical
  obtain ⟨nodes, hinj, hnonzero⟩ := unit_nodes (K * j + 1)
  have hevalpower : ∀ t : O, IsUnit t →
      (fun u v w => (Tensor.power P j u v w).eval t) ∈
        LocalTensor.orbit (Tensor.power T j) := by
    intro t ht
    rw [polynomial_power_eval]
    exact power_mem_restrictionOrbit (heval t ht) j
  have hdegreepower : ∀ u v w, (Tensor.power P j u v w).degree <
      Fintype.card (Fin (K * j + 1)) := by
    intro u v w
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (polynomial_power_degree P K j hdegree u v w)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (K * j)))
  have h := polynomial_coeff_mem_restrictionOrbit (Tensor.power T j) (Tensor.power P j)
    nodes hinj hnonzero hevalpower hdegreepower 0
  have hD : (fun u v w => (P u v w).coeff 0) = D := by
    funext u v w
    exact hconstant u v w
  rw [polynomial_power_constant, hD] at h
  exact h

end Interpolation

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.Separation

/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
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

open MatrixMultiplicationAllFields.MatrixExponent

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.Separation

export MatrixMultiplicationAllFields.TensorSpectrum.RestrictionInterpolation
  (restrict_directSum_sum restrict_scale_first restrict_power power_mem_restrictionOrbit
    polynomial_power_constant polynomial_power_eval polynomial_power_degree)

section Interpolation

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Interpolation at any common family of distinct nonzero nodes turns actual
restriction witnesses for the evaluations into one restriction witness for the
coefficient. The full number of source copies is charged explicitly. -/
theorem polynomial_coeff_mem_restrictionOrbit {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Tensor Coeff X Y Z) (P : Tensor (Polynomial Coeff) U V W)
    (nodes : ι → Coeff) (hinj : Function.Injective nodes)
    (hnonzero : ∀ i, nodes i ≠ 0)
    (heval : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (hdegree : ∀ u v w, (P u v w).degree < Fintype.card ι) (d : ℕ) :
    (fun u v w => (P u v w).coeff d) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : ι => T)) := by
  classical
  let weight : (ι) → Coeff := fun i => (Lagrange.basis Finset.univ nodes i).coeff d
  have h := TensorSpectrum.RestrictionInterpolation.weighted_sum_of_restrictions
    T (fun i u v w => (P u v w).eval (nodes i)) weight
    (fun i => heval (nodes i) (hnonzero i))
  have hcoeff : (fun u v w => (P u v w).coeff d) =
      (fun u v w => ∑ i, weight i * (P u v w).eval (nodes i)) := by
    funext u v w
    simpa only [weight, mul_comm] using
      Tensor.coeff_eq_sum_eval nodes hinj (P u v w) d (hdegree u v w)
  rwa [hcoeff]

/-- The finite interpolation bound before applying any character. For every
power `j`, exactly `K*j+1` copies of the power of the original source suffice.
The interpolation nodes have this same cardinality. -/
theorem polynomial_power_mem_restrictionOrbit
    (T : Tensor Coeff X Y Z) (D : Tensor Coeff U V W)
    (P : Tensor (Polynomial Coeff) U V W) (K : ℕ)
    (hconstant : ∀ u v w, (P u v w).coeff 0 = D u v w)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (heval : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (j : ℕ) :
    Tensor.power D j ∈ LocalTensor.orbit
      (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j)) := by
  classical
  apply TensorSpectrum.RestrictionInterpolation.polynomial_power_mem_restrictionOrbit
    T D P K hconstant hdegree (fun t => t ≠ 0) heval j
  intro hevalpower hdegreepower
  obtain ⟨nodes, hinj, hnonzero⟩ := exists_nonzero_nodes (F := Coeff) (K * j + 1)
  exact polynomial_coeff_mem_restrictionOrbit (Tensor.power T j) (Tensor.power P j)
    nodes hinj hnonzero hevalpower hdegreepower 0

end Interpolation

end MatrixMultiplicationAllFields.MatrixExponent.Upper.Separation

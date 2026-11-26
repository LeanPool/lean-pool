/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.WeightedPolynomials
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialFiltration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.LocalTensor

/-!
# The finite-degree determinant family

The constant coefficient is the two-branch graded tensor.  Every nonzero
evaluation is an actual restriction of the original convolution tensor times
the two-dimensional pairing.  These explicit data, rather than continuity of
an arbitrary tensor character, are the inputs to finite interpolation.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

namespace MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors

variable {K : Type*} [CommRing K]

theorem determinantAdapted_mem_restrictionOrbit (a b : ℕ) :
    determinantAdaptedTensor (K := K) a b ∈ LocalTensor.orbit
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) := by
  have hd : doubledPolynomialTensor (K := K) a b ∈ LocalTensor.orbit
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) := by
    rw [← doubledPolynomialTensor_product, Tensor.pullback_eq_restrict]
    exact ⟨_, _, _, rfl⟩
  have h := LocalTensor.restrict_mem hd
    (fun i' i : Fin (a + 1) => if i = i' then (1 : K) else 0)
    (determinantInputMap b) (determinantOutputMap a b)
  have he : Tensor.restrict
      (fun i' i : Fin (a + 1) => if i = i' then (1 : K) else 0)
      (determinantInputMap b) (determinantOutputMap a b)
      (doubledPolynomialTensor a b) = determinantAdaptedTensor a b :=
    determinant_basis_change a b
  rwa [he] at h

/-- Coefficients are constant or linear in the degeneration parameter. -/
def determinantPolynomialFamily (a b : ℕ) :
    Tensor (Polynomial K) (Fin (a + 1)) (Fin (b + 3) ⊕ Fin (b + 1))
      (Fin (a + b + 3) ⊕ Fin (a + b + 1)) :=
  weightedPolynomial (determinantAdaptedTensor a b) (fun _ => 0)
    (determinantInputWeight b) (determinantOutputWeight a b)

theorem determinantPolynomialFamily_coeff_zero (a b : ℕ) :
    (fun i y z => (determinantPolynomialFamily (K := K) a b i y z).coeff 0) =
      determinantGradedTensor a b := by
  funext i y z
  rw [determinantPolynomialFamily, weightedPolynomial_coeff_zero
    (determinantAdaptedTensor a b) (fun _ => 0)
    (determinantInputWeight b) (determinantOutputWeight a b)
    (determinant_supported_weight a b)]
  exact congrFun (congrFun (congrFun (determinant_weightedLimit a b) i) y) z

theorem determinantPolynomialFamily_degree_le (a b : ℕ)
    (i : Fin (a + 1)) (y : Fin (b + 3) ⊕ Fin (b + 1))
    (z : Fin (a + b + 3) ⊕ Fin (a + b + 1)) :
    (determinantPolynomialFamily (K := K) a b i y z).degree ≤ (1 : ℕ) := by
  apply weightedPolynomial_degree_le
  intro i' y' z' hc
  cases y' <;> cases z' <;>
    simp_all [determinantAdaptedTensor, determinantInputWeight, determinantOutputWeight]

theorem determinantPolynomialFamily_eval_mem_restrictionOrbit (a b : ℕ) (t : K)
    (he : (fun i y z => (determinantPolynomialFamily a b i y z).eval t) ∈
      LocalTensor.orbit (determinantAdaptedTensor a b)) :
    (fun i y z => (determinantPolynomialFamily a b i y z).eval t) ∈
      LocalTensor.orbit
        (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) :=
  LocalTensor.orbit_trans (determinantAdapted_mem_restrictionOrbit a b) he

end MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors

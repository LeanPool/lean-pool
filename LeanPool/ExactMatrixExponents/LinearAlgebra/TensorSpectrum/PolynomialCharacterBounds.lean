/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.CharacterDegeneration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorCharacterPowers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassDirectSum
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialFiltrationFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialSectorFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationPolynomial

/-!
# Character bounds for the determinant, tripling and separation families

A character evaluates the shared polynomial degenerations through its
semiring operations. The actual restriction inequalities come from the
coefficient model.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent

namespace MatrixMultiplicationAllFields.TensorSpectrum.TensorClass

open PolynomialTensors

/-- A coefficient model's comparison for a bounded polynomial restriction family. -/
abbrev Character.PolynomialBound {K : Type*} [CommSemiring K] (f : Character K)
    (node : K → Prop) : Prop :=
  ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (D : Tensor K U V W) (P : Tensor (Polynomial K) U V W) (degree : ℕ),
    (∀ u v w, (P u v w).coeff 0 = D u v w) →
    (∀ u v w, (P u v w).degree ≤ degree) →
    (∀ t, node t → (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T) →
    f (ofTensor D) ≤ f (ofTensor T)

section Determinant

variable {K : Type*} [CommRing K]

theorem binaryDotTensor_class : ofTensor (binaryDotTensor (K := K)) = dotX 2 := by
  have heq : Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      (binaryDotTensor (K := K)) = CoefficientTensor.dotXCoeff 2 := by
    funext x y z
    simp [Tensor.pullback, TensorSpectrum.PolynomialTensors.binaryDotTensor,
      CoefficientTensor.dotXCoeff]
  change ofTensor binaryDotTensor = ofTensor (CoefficientTensor.dotXCoeff 2)
  rw [← heq]
  exact (ofTensor_pullback_equiv _ _ _ _).symm

theorem Character.determinant_graded_le (f : Character K) (a b : ℕ)
    (h : f (ofTensor (determinantGradedTensor a b)) ≤ f (ofTensor
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor))) :
    (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) := by
  rw [← ofTensor_mul, Character.map_mul, binaryDotTensor_class] at h
  have hr : (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) * f.dotXValue 2 := by
    exact_mod_cast h
  rw [f.dotXValue_eq_rpow 2 (by decide), mul_comm] at hr
  exact hr

theorem Character.determinant_graded_le_of_evaluation (f : Character K) {node : K → Prop}
    (compare : f.PolynomialBound node) (a b : ℕ)
    (heval : ∀ t, node t → (fun i y z => (determinantPolynomialFamily a b i y z).eval t) ∈
      LocalTensor.orbit (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor)) :
    (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) :=
  f.determinant_graded_le a b (compare
    (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor)
    (determinantGradedTensor a b) (determinantPolynomialFamily a b) 1
    (fun i y z => congrFun (congrFun (congrFun
      (determinantPolynomialFamily_coeff_zero a b) i) y) z)
    (determinantPolynomialFamily_degree_le a b) heval)

end Determinant

variable {K : Type*} [CommSemiring K]

theorem Character.tripling_graded_le (f : Character K) (a h : ℕ)
    (hpower : ∀ j : ℕ,
      Tensor.power (triplingSectorTensor (K := K) a h) j ∈ LocalTensor.orbit
      (Tensor.directSum (fun _ : Fin (1 * j + 1) =>
        Tensor.power (polynomialTensor a (triplingWidth a h)) j))) :
    (f (ofTensor (triplingSectorTensor a h)) : ℝ) ≤
      (f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ) := by
  exact_mod_cast f.polynomial_constant_le
    (polynomialTensor a (triplingWidth a h)) (triplingSectorTensor a h) 1 hpower
theorem Character.tripling_graded_le_of_evaluation (f : Character K) {node : K → Prop}
    (compare : f.PolynomialBound node) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (heval : ∀ t, node t → (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) ∈
      LocalTensor.orbit (polynomialTensor a (triplingWidth a h))) :
    (f (ofTensor (triplingSectorTensor a h)) : ℝ) ≤
      (f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ) := by
  exact_mod_cast compare (polynomialTensor a (triplingWidth a h)) (triplingSectorTensor a h)
    (triplingPolynomialFamily a h ha hh) 1
    (triplingPolynomialFamily_coeff_zero a h ha hh)
    (triplingPolynomialFamily_degree_le a h ha hh) heval

theorem Character.charged_separation (f : Character K)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (factor : ℕ) (A : Fin M → Tensor K X Y Z)
    (h : f (ofTensor (Separation.separated A)) ≤ f (ofTensor
      (Tensor.directSum (fun _ : Fin (factor * M) => Tensor.sharedFirst A)))) :
    (∑ h, f (ofTensor (A h))) *
        f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      ((factor : ℝ≥0) * M) * f (ofTensor (Tensor.sharedFirst A)) := by
  rw [Character.map_directSum_const] at h
  have houtput : f (ofTensor (Separation.separated A)) =
      (∑ h, f (ofTensor (A h))) *
        f (ofTensor (Separation.dotPairingX (Fin M))) := by
    unfold Separation.separated
    rw [Character.map_directSum_fin]
    simp only [← ofTensor_mul, Character.map_mul, Finset.sum_mul]
  rw [houtput] at h
  simpa only [Nat.cast_mul] using h

/-- Equal branch values let the number of branches cancel in the separation bound. -/
theorem Character.charged_separation_equal (f : Character K)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (factor : ℕ) (hM : 0 < M) (A : Fin M → Tensor K X Y Z)
    (c : ℝ≥0) (hvalue : ∀ h, f (ofTensor (A h)) = c)
    (h : (∑ i, f (ofTensor (A i))) * f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      ((factor : ℝ≥0) * M) * f (ofTensor (Tensor.sharedFirst A))) :
    c * f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      (factor : ℝ≥0) * f (ofTensor (Tensor.sharedFirst A)) := by
  simp only [hvalue, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have hM' : (0 : ℝ≥0) < M := by exact_mod_cast hM
  apply (mul_le_mul_iff_right₀ hM').mp
  calc
    (M : ℝ≥0) * (c * f (ofTensor (Separation.dotPairingX (Fin M)))) =
        ((M : ℝ≥0) * c) * f (ofTensor (Separation.dotPairingX (Fin M))) :=
      (mul_assoc _ _ _).symm
    _ ≤ ((factor : ℝ≥0) * M) * f (ofTensor (Tensor.sharedFirst A)) := h
    _ = (M : ℝ≥0) * ((factor : ℝ≥0) * f (ofTensor (Tensor.sharedFirst A))) := by ring

end MatrixMultiplicationAllFields.TensorSpectrum.TensorClass

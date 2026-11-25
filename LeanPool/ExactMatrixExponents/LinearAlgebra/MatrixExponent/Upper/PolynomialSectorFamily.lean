/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialSectors
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialWeightFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialSectorFamily

/-!
# The polynomial witness for the three-sector degeneration

Every coefficient has degree at most one.  Its constant coefficient is the
entire shared-first-input sector assembly.  At each nonzero parameter the
evaluated tensor is an actual restriction of the original polynomial tensor.
These explicit facts support interpolation without assuming that an arbitrary
tensor character preserves topological limits.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper

/-- The tripling polynomial family over the coefficient ring. -/
abbrev triplingPolynomialFamily :=
  TensorSpectrum.PolynomialTensors.triplingPolynomialFamily (K := Coeff)

theorem triplingPolynomialFamily_coeff_zero (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).coeff 0 = triplingSectorTensor a h x y z :=
  TensorSpectrum.PolynomialTensors.triplingPolynomialFamily_coeff_zero a h ha hh x y z

theorem triplingPolynomialFamily_degree_le (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).degree ≤ (1 : ℕ) :=
  TensorSpectrum.PolynomialTensors.triplingPolynomialFamily_degree_le a h ha hh x y z

/-- Every nonzero evaluation is an exact restriction of the original source
tensor. The sector reindexing is one fixed pair of local maps, with identity
on the common first input, after the diagonal maps. -/
theorem triplingPolynomialFamily_eval_mem_restrictionOrbit
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) {t : Coeff} (ht : t ≠ 0) :
    (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) ∈
      LocalTensor.orbit (polynomialTensor a (triplingWidth a h)) := by
  classical
  let E : Tensor Coeff (Fin a) (Fin (triplingWidth a h))
      (Fin (a + triplingWidth a h - 1)) :=
    fun x y z => (weightedPolynomial (polynomialTensor a (triplingWidth a h))
      (fun _ => 0) (fun y => triplingYWeight a h y.val)
      (fun z => triplingZWeight a h z.val) x y z).eval t
  have hE : E ∈ LocalTensor.orbit (polynomialTensor a (triplingWidth a h)) :=
    weightedPolynomial_eval_mem_restrictionOrbit _ _ _ _
      (TensorSpectrum.PolynomialTensors.tripling_source_weights_nonneg a h ha) ht
  have hr := LocalTensor.restrict_mem hE
    (fun (x' x : Fin a) => if x = x' then (1 : Coeff) else 0)
    (fun (y' : TriplingY a h) (y : Fin (triplingWidth a h)) =>
      if y = triplingYEquiv a h ha hh y' then (1 : Coeff) else 0)
    (fun (z' : TriplingZ a h) (z : Fin (a + triplingWidth a h - 1)) =>
      if z = triplingZEquiv a h ha hh z' then (1 : Coeff) else 0)
  have hp : Tensor.pullback (id : Fin a → Fin a)
      (triplingYEquiv a h ha hh) (triplingZEquiv a h ha hh) E =
      (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) := rfl
  rw [Tensor.pullback_eq_restrict] at hp
  simp only [id_eq] at hp
  rw [hp] at hr
  exact hr

end MatrixMultiplicationAllFields.MatrixExponent.Upper

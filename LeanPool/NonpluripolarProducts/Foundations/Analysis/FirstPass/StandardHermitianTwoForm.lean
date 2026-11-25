/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HermitianGeometry
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# The standard Hermitian two-form and pullbacks of semipositive `(1,1)`-forms

Pure linear algebra on the model space `ℂⁿ = ComplexModel n`.

* `standardHermitianTwoForm n` is the real two-form `ω(v, w) = Im ⟪v, w⟫` (Mathlib's inner
  product is conjugate-linear in the first slot). It is definitionally the flat fundamental
  form `Kahler.fundamentalFormAlt`, so it is of type `(1,1)` and strictly positive.
* `exists_linearMap_eq_standard_comp`: a real `(1,1)`-form `A` with `A(v, iv) ≥ 0` is the
  pullback of `ω` by a `ℂ`-linear map `S`. The proof builds the Hermitian form
  `h(v, w) = A(v, iw) + i A(v, w)`, the positive operator `T` with `⟪v, T w⟫ = h(v, w)`, and
  writes `T = S^* S` in the C⋆-algebra of operators.
* `normSq_det_le_of_standard_comp_add`: if `W^*ω = S^*ω + R^*ω`, then
  `|det S|² ≤ |det W|²`. This is `det P ≤ det (P + Q)` for positive semidefinite
  Gram matrices.
* `det_ne_zero_of_standard_comp_strictlyPositive` and `normSq_det_eq_realDet` relate the
  complex determinant to strict positivity and to the real determinant.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace Matrix

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

noncomputable section

variable {n : ℕ}

theorem standardHermitianTwoForm_isOneOne (n : ℕ) : IsOneOne (standardHermitianTwoForm n) :=
  flatFundamentalForm_isOneOne n

theorem standardHermitianTwoForm_isStrictlyPositive (n : ℕ) :
    IsStrictlyPositive (standardHermitianTwoForm n) :=
  flatFundamentalForm_isStrictlyPositive n

theorem standardHermitianTwoForm_compContinuousLinearMap_apply
    (S : ComplexModel n →ₗ[ℂ] ComplexModel n) (v w : ComplexModel n) :
    (standardHermitianTwoForm n).compContinuousLinearMap
        (LinearMap.toContinuousLinearMap (S.restrictScalars ℝ)) ![v, w] =
      (inner ℂ (S v) (S w)).im := by
  change standardHermitianTwoForm n ![S v, S w] = _
  simp

/-- The Hermitian form of a real `(1,1)`-form, as a sesquilinear map. -/
private def hermitianSesq {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (hA : IsOneOne A) :
    ComplexModel n →ₗ⋆[ℂ] ComplexModel n →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (hermitianOfTwoForm A)
    (hermitianOfTwoForm_add_left A)
    (fun c v w => by simpa using hermitianOfTwoForm_smul_left hA c v w)
    (hermitianOfTwoForm_add_right A)
    (fun c v w => by simpa using hermitianOfTwoForm_smul_right c v w)

private theorem hermitianSesq_apply {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hA : IsOneOne A) (v w : ComplexModel n) :
    hermitianSesq hA v w = hermitianOfTwoForm A v w := rfl

/-- The operator `T` with `⟪v, T w⟫ = h(v, w)`. -/
private def hermitianOperator {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (hA : IsOneOne A) :
    ComplexModel n →ₗ[ℂ] ComplexModel n :=
  ∑ j, (hermitianSesq hA (EuclideanSpace.basisFun (Fin n) ℂ j)).smulRight
    (EuclideanSpace.basisFun (Fin n) ℂ j)

private theorem inner_hermitianOperator {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hA : IsOneOne A) (v w : ComplexModel n) :
    inner ℂ v (hermitianOperator hA w) = hermitianOfTwoForm A v w := by
  set b := EuclideanSpace.basisFun (Fin n) ℂ
  rw [← hermitianSesq_apply hA]
  conv_rhs => rw [← b.sum_repr' v]
  simp only [hermitianOperator, map_sum, map_smulₛₗ, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smulRight_apply, inner_sum, inner_smul_right, LinearMap.smul_apply,
    smul_eq_mul, inner_conj_symm]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem hermitianOperator_isPositive {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hA : IsOneOne A) (hpos : PositiveClasses.CoefficientSemipositive A) :
    (hermitianOperator hA).IsPositive := by
  rw [LinearMap.isPositive_iff_complex]
  intro x
  have h1 : inner ℂ (hermitianOperator hA x) x = (A ![x, Complex.I • x] : ℂ) := by
    rw [← inner_conj_symm, inner_hermitianOperator]
    simp [hermitianOfTwoForm, twoForm_self]
  rw [h1]
  simp [hpos x]

/-- Every semipositive real `(1,1)`-form on `ℂⁿ` is the pullback of the standard Hermitian
form by a `ℂ`-linear map. -/
theorem exists_linearMap_eq_standard_comp {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hA : IsOneOne A) (hpos : PositiveClasses.CoefficientSemipositive A) :
    ∃ S : ComplexModel n →ₗ[ℂ] ComplexModel n,
      ∀ v w, A ![v, w] = (inner ℂ (S v) (S w)).im := by
  have hT : 0 ≤ LinearMap.toContinuousLinearMap (hermitianOperator hA) := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, LinearMap.isPositive_toContinuousLinearMap_iff]
    exact hermitianOperator_isPositive hA hpos
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
  refine ⟨B.toLinearMap, fun v w => ?_⟩
  have h := congrArg (fun T : ComplexModel n →L[ℂ] ComplexModel n => inner ℂ v (T w)) hB
  simp only [LinearMap.coe_toContinuousLinearMap', inner_hermitianOperator,
    ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right] at h
  simp [← h, hermitianOfTwoForm]

/-- If a strictly positive form is the pullback of the standard form by `S`, then `S` is
injective, so `det S ≠ 0`. -/
theorem det_ne_zero_of_standard_comp_strictlyPositive
    {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    {S : ComplexModel n →ₗ[ℂ] ComplexModel n}
    (hS : ∀ v w, A ![v, w] = (inner ℂ (S v) (S w)).im) (hA : IsStrictlyPositive A) :
    LinearMap.det S ≠ 0 := by
  rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot']
  intro v hv
  by_contra hne
  have := hA v hne
  rw [hS, map_smul, hv] at this
  simp at this

/-- The real determinant of a `ℂ`-linear map is the squared modulus of its complex determinant. -/
theorem normSq_det_eq_realDet (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    LinearMap.det (S.restrictScalars ℝ) = Complex.normSq (LinearMap.det S) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- For a positive semidefinite `X`, `det (1 + X) ≥ 1`. -/
private theorem one_le_det_one_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : 1 ≤ (1 + X).det := by
  have hH := hX.isHermitian
  have h1 : 1 + X = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
      (1 + Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) := by
    conv_lhs => rw [hH.spectral_theorem]
    simp only [map_add, map_one]
  rw [h1, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, Unitary.coe_star_mul_self, Matrix.det_one, one_mul,
    ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.det_diagonal]
  have h2 : ∏ i, ((1 : ℂ) + (RCLike.ofReal ∘ hH.eigenvalues) i) =
      ((∏ i, (1 + hH.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h2, ← Complex.ofReal_one, Complex.real_le_real]
  calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
    _ ≤ ∏ i, (1 + hH.eigenvalues i) :=
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
        (fun i _ => le_add_of_nonneg_right (hX.eigenvalues_nonneg i))

open scoped MatrixOrder in
/-- Determinant monotonicity: `det P ≤ det (P + Q)` for positive semidefinite `P`, `Q`. -/
private theorem det_le_det_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : Matrix ι ι ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) : P.det ≤ (P + Q).det := by
  by_cases hdet : P.det = 0
  · rw [hdet]
    exact (hP.add hQ).det_nonneg
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hdet hP ⊢
  have hy : IsUnit y.det := by
    rw [Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  set X := (y⁻¹)ᴴ * Q * y⁻¹ with hXdef
  have hX : X.PosSemidef := hQ.conjTranspose_mul_mul_same _
  have hinv : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul y hy
  have hinvH : yᴴ * (y⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  have hsum : yᴴ * (1 + X) * y = yᴴ * y + Q := by
    simp only [hXdef, mul_add, add_mul, mul_one]
    congr 1
    calc yᴴ * ((y⁻¹)ᴴ * Q * y⁻¹) * y = (yᴴ * (y⁻¹)ᴴ) * Q * (y⁻¹ * y) := by
          simp only [mul_assoc]
      _ = Q := by rw [hinv, hinvH, one_mul, mul_one]
  have hdetsum : (yᴴ * y + Q).det = (1 + X).det * (yᴴ * y).det := by
    rw [← hsum]
    simp only [Matrix.det_mul]
    ring
  rw [hdetsum]
  calc (yᴴ * y).det = 1 * (yᴴ * y).det := (one_mul _).symm
    _ ≤ (1 + X).det * (yᴴ * y).det :=
      mul_le_mul_of_nonneg_right (one_le_det_one_add hX)
        (Matrix.posSemidef_conjTranspose_mul_self y).det_nonneg

/-- If `W^*W = S^*S + R^*R` (encoded by the pulled-back standard forms), then
`|det S|² ≤ |det W|²`. -/
theorem normSq_det_le_of_standard_comp_add (S R W : ComplexModel n →ₗ[ℂ] ComplexModel n)
    (h : ∀ v w, (inner ℂ (W v) (W w)).im =
      (inner ℂ (S v) (S w)).im + (inner ℂ (R v) (R w)).im) :
    Complex.normSq (LinearMap.det S) ≤ Complex.normSq (LinearMap.det W) := by
  have hinner : ∀ v w, inner ℂ (W v) (W w) = inner ℂ (S v) (S w) + inner ℂ (R v) (R w) := by
    intro v w
    have h2 := h v (Complex.I • w)
    simp only [map_smul, inner_smul_right, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_add] at h2
    apply Complex.ext
    · simpa using h2
    · simpa using h v w
  have hWW : W.adjoint ∘ₗ W = S.adjoint ∘ₗ S + R.adjoint ∘ₗ R := by
    apply LinearMap.ext
    intro w
    apply ext_inner_left ℂ
    intro v
    simp [LinearMap.adjoint_inner_right, inner_add_right, hinner]
  have key : ∀ T : ComplexModel n →ₗ[ℂ] ComplexModel n,
      ((Complex.normSq (LinearMap.det T) : ℝ) : ℂ) = LinearMap.det (T.adjoint ∘ₗ T) := by
    intro T
    rw [← LinearMap.normDet_sq, LinearMap.normDet_eq_norm_det, Complex.normSq_eq_norm_sq]
    rfl
  rw [← Complex.real_le_real, key, key, hWW]
  set b := EuclideanSpace.basisFun (Fin n) ℂ
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis, map_add]
  exact det_le_det_add
    ((LinearMap.posSemidef_toMatrix_iff b).2 (LinearMap.isPositive_adjoint_comp_self S))
    ((LinearMap.posSemidef_toMatrix_iff b).2 (LinearMap.isPositive_adjoint_comp_self R))

/-- A semipositive real `(1,1)`-form is literally the pullback of the standard form. -/
theorem exists_linearMap_eq_standard_compContinuousLinearMap
    {A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hA : IsOneOne A) (hpos : PositiveClasses.CoefficientSemipositive A) :
    ∃ S : ComplexModel n →ₗ[ℂ] ComplexModel n,
      A = (standardHermitianTwoForm n).compContinuousLinearMap
        (LinearMap.toContinuousLinearMap (S.restrictScalars ℝ)) := by
  obtain ⟨S, hS⟩ := exists_linearMap_eq_standard_comp hA hpos
  refine ⟨S, ?_⟩
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, hS, standardHermitianTwoForm_compContinuousLinearMap_apply]

end

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere

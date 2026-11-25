/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityGeneral
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardKahlerTopPower
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityFrame

/-!
# The exterior-power/determinant density identity for an arbitrary real `(1,1)`-form

`Pending.CoordinateDensityGeneral` proves
`actualTopPowerDensity A = normalizedTopPowerDensity A` for a **semipositive**
real `(1,1)`-form, by writing `A = ω(S·, S·)`.  That hypothesis is not available
for the two-forms the restricted masses actually integrate: `β + ddᶜ v` for a
chart-smooth real `v` is of type `(1,1)` but never semipositive in general.

This file removes it.  The argument is unitary diagonalization:

* the entry `G_A(v, w) = A(v, i w) - i A(v, w)` is `ℂ`-linear in `v` and
  conjugate linear in `w` whenever `A` is of type `(1,1)`, so
  `normalizedHermitianMatrix A` is a Hermitian matrix and transforms by
  `H ↦ Σᵀ H ΣBar` under the pullback of `A` along the `ℂ`-linear map with matrix
  `Σ` (`normalizedHermitianMatrix_compLinearMap`);
* hence BOTH densities are multiplied by `|det_ℂ Σ|²` under such a pullback —
  the actual one by `actualTopPowerDensity_compContinuousLinearMap` and
  `normSq_det_eq_realDet`;
* choosing `Σ` to be the entrywise conjugate of the eigenvector unitary of `H`
  makes the pulled-back matrix the real diagonal matrix of eigenvalues, where
  the identity is the weighted diagonal computation
  `actualTopPowerDensity_eq_factorial_mul_prod_of_diagonal_weights`, which
  assumes nothing about the signs of the weights;
* the pullback factor `|det_ℂ Σ|²` is `1` for a unitary `Σ`.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

section HermitianEntry

/-- The Hermitian entry `G_A(v, w) = A(v, i w) - i A(v, w)` of a real two-form.
For a form of type `(1,1)` it is `ℂ`-linear in `v` and conjugate linear in `w`,
and `normalizedHermitianMatrix A` is `π` times its matrix in the standard basis. -/
def hermitianEntry (A : CoordinateRealTwoForm n) (v w : ComplexModel n) : ℂ :=
  (A ![v, Complex.I • w] : ℂ) - Complex.I * (A ![v, w] : ℂ)

theorem normalizedHermitianMatrix_apply' (A : CoordinateRealTwoForm n) (j k : Fin n) :
    normalizedHermitianMatrix A j k =
      (Real.pi : ℂ) * hermitianEntry A (coordinateVector j) (coordinateVector k) :=
  rfl

theorem hermitianEntry_eq_conj (A : CoordinateRealTwoForm n) (v w : ComplexModel n) :
    hermitianEntry A v w = starRingEnd ℂ (hermitianOfTwoForm A v w) := by
  simp only [hermitianEntry, hermitianOfTwoForm, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  ring

variable {A : CoordinateRealTwoForm n}

theorem hermitianEntry_add_left (v v' w : ComplexModel n) :
    hermitianEntry A (v + v') w = hermitianEntry A v w + hermitianEntry A v' w := by
  simp only [hermitianEntry_eq_conj, hermitianOfTwoForm_add_left, map_add]

theorem hermitianEntry_add_right (v w w' : ComplexModel n) :
    hermitianEntry A v (w + w') = hermitianEntry A v w + hermitianEntry A v w' := by
  simp only [hermitianEntry_eq_conj, hermitianOfTwoForm_add_right, map_add]

theorem hermitianEntry_smul_left (hA : IsOneOne A) (c : ℂ) (v w : ComplexModel n) :
    hermitianEntry A (c • v) w = c * hermitianEntry A v w := by
  simp [hermitianEntry_eq_conj, hermitianOfTwoForm_smul_left hA, map_mul]

theorem hermitianEntry_smul_right (c : ℂ) (v w : ComplexModel n) :
    hermitianEntry A v (c • w) = (starRingEnd ℂ) c * hermitianEntry A v w := by
  simp only [hermitianEntry_eq_conj, hermitianOfTwoForm_smul_right, map_mul]

end HermitianEntry

section Pullback

variable {A : CoordinateRealTwoForm n}

theorem hermitianEntry_zero_left (w : ComplexModel n) : hermitianEntry A 0 w = 0 := by
  have h1 : A ![(0 : ComplexModel n), Complex.I • w] = 0 := by
    have := twoForm_smul_left A 0 (0 : ComplexModel n) (Complex.I • w)
    simpa using this
  have h2 : A ![(0 : ComplexModel n), w] = 0 := by
    have := twoForm_smul_left A 0 (0 : ComplexModel n) w
    simpa using this
  simp [hermitianEntry, h1, h2]

theorem hermitianEntry_zero_right (v : ComplexModel n) : hermitianEntry A v 0 = 0 := by
  have h2 : A ![v, (0 : ComplexModel n)] = 0 := by
    have := twoForm_smul_right A 0 v (0 : ComplexModel n)
    simpa using this
  simp [hermitianEntry, h2]

theorem hermitianEntry_sum_left {ι : Type*} (hA : IsOneOne A) (s : Finset ι)
    (c : ι → ℂ) (x : ι → ComplexModel n) (w : ComplexModel n) :
    hermitianEntry A (∑ p ∈ s, c p • x p) w =
      ∑ p ∈ s, c p * hermitianEntry A (x p) w := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hermitianEntry_zero_left (A := A) w
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, hermitianEntry_add_left, hermitianEntry_smul_left hA, ih,
        Finset.sum_insert ha]

theorem hermitianEntry_sum_right {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (x : ι → ComplexModel n) (v : ComplexModel n) :
    hermitianEntry A v (∑ q ∈ s, c q • x q) =
      ∑ q ∈ s, (starRingEnd ℂ) (c q) * hermitianEntry A v (x q) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hermitianEntry_zero_right (A := A) v
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, hermitianEntry_add_right, hermitianEntry_smul_right, ih,
        Finset.sum_insert ha]

/-- The image of a standard coordinate vector, expanded in the standard basis. -/
theorem apply_coordinateVector_eq_sum (S : ComplexModel n →ₗ[ℂ] ComplexModel n) (j : Fin n) :
    S (coordinateVector j) = ∑ p, standardMatrix S p j • coordinateVector p := by
  ext q
  rw [show ((∑ p, standardMatrix S p j • coordinateVector p : ComplexModel n)).ofLp q =
      ∑ p, (standardMatrix S p j • coordinateVector p : ComplexModel n).ofLp q by simp]
  rw [Finset.sum_eq_single q]
  · simp [coordinateVector, standardMatrix_apply]
  · intro b _ hb
    simp [coordinateVector, Ne.symm hb]
  · simp

/-- The pullback of a real two-form along a `ℂ`-linear map. -/
abbrev compLinearMap (A : CoordinateRealTwoForm n)
    (S : ComplexModel n →ₗ[ℂ] ComplexModel n) : CoordinateRealTwoForm n :=
  A.compContinuousLinearMap (LinearMap.toContinuousLinearMap (S.restrictScalars ℝ))

theorem compLinearMap_apply (A : CoordinateRealTwoForm n)
    (S : ComplexModel n →ₗ[ℂ] ComplexModel n) (v w : ComplexModel n) :
    compLinearMap A S ![v, w] = A ![S v, S w] := by
  rw [compLinearMap, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem isOneOne_compLinearMap (hA : IsOneOne A)
    (S : ComplexModel n →ₗ[ℂ] ComplexModel n) : IsOneOne (compLinearMap A S) := by
  intro v w
  rw [compLinearMap_apply, compLinearMap_apply, map_smul, map_smul]
  exact hA (S v) (S w)

theorem hermitianEntry_compLinearMap (S : ComplexModel n →ₗ[ℂ] ComplexModel n)
    (v w : ComplexModel n) :
    hermitianEntry (compLinearMap A S) v w = hermitianEntry A (S v) (S w) := by
  simp only [hermitianEntry, compLinearMap_apply, map_smul]

/-- **The transformation law of the coefficient matrix.**  Under the pullback of a
real `(1,1)`-form along a `ℂ`-linear map with standard matrix `Σ`, the normalized
Hermitian coefficient matrix becomes `Σᵀ H ΣBar`. -/
theorem normalizedHermitianMatrix_compLinearMap (hA : IsOneOne A)
    (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    normalizedHermitianMatrix (compLinearMap A S) =
      (standardMatrix S)ᵀ * normalizedHermitianMatrix A *
        (standardMatrix S).map (starRingEnd ℂ) := by
  ext j k
  have hL : normalizedHermitianMatrix (compLinearMap A S) j k =
      ∑ p, ∑ q, (standardMatrix S)ᵀ j p * normalizedHermitianMatrix A p q *
        ((standardMatrix S).map (starRingEnd ℂ)) q k := by
    rw [normalizedHermitianMatrix_apply', hermitianEntry_compLinearMap,
      apply_coordinateVector_eq_sum S j, apply_coordinateVector_eq_sum S k,
      hermitianEntry_sum_left hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hermitianEntry_sum_right, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [normalizedHermitianMatrix_apply']
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    ring
  have hR : ((standardMatrix S)ᵀ * normalizedHermitianMatrix A *
      (standardMatrix S).map (starRingEnd ℂ)) j k =
      ∑ q, ∑ p, (standardMatrix S)ᵀ j p * normalizedHermitianMatrix A p q *
        ((standardMatrix S).map (starRingEnd ℂ)) q k := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [hL, hR, Finset.sum_comm]

end Pullback

section Densities

variable {A : CoordinateRealTwoForm n}

/-- The genuine top exterior-power density is multiplied by `|det_ℂ S|²` under the
pullback along a `ℂ`-linear map. -/
theorem actualTopPowerDensity_compLinearMap (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    actualTopPowerDensity (compLinearMap A S) =
      Complex.normSq (LinearMap.det S) * actualTopPowerDensity A := by
  rw [compLinearMap, actualTopPowerDensity_compContinuousLinearMap]
  congr 1
  rw [← normSq_det_eq_realDet]
  rfl

/-- The determinant density is multiplied by the same factor `|det_ℂ S|²`. -/
theorem normalizedTopPowerDensity_compLinearMap (hA : IsOneOne A)
    (S : ComplexModel n →ₗ[ℂ] ComplexModel n) :
    normalizedTopPowerDensity (compLinearMap A S) =
      Complex.normSq (LinearMap.det S) * normalizedTopPowerDensity A := by
  have hdet : (normalizedHermitianMatrix (compLinearMap A S)).det =
      ((Complex.normSq (LinearMap.det S) : ℝ) : ℂ) * (normalizedHermitianMatrix A).det := by
    have hconj : ((standardMatrix S).map (starRingEnd ℂ)).det =
        starRingEnd ℂ ((standardMatrix S).det) :=
      (RingHom.map_det (starRingEnd ℂ) (standardMatrix S)).symm
    rw [normalizedHermitianMatrix_compLinearMap hA, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, hconj, det_standardMatrix, Complex.normSq_eq_conj_mul_self]
    ring
  rw [normalizedTopPowerDensity, normalizedTopPowerDensity, complexTopCoefficient_eq,
    complexTopCoefficient_eq, hdet,
    show (((n.factorial : ℝ) / Real.pi ^ n : ℝ) : ℂ) *
        (((Complex.normSq (LinearMap.det S) : ℝ) : ℂ) * (normalizedHermitianMatrix A).det) =
        ((Complex.normSq (LinearMap.det S) : ℝ) : ℂ) *
          ((((n.factorial : ℝ) / Real.pi ^ n : ℝ) : ℂ) * (normalizedHermitianMatrix A).det) from
      by ring]
  simp

end Densities

section Diagonal

variable {A : CoordinateRealTwoForm n}

/-- **The identity for a form whose coefficient matrix is real diagonal.**  No
positivity is assumed: the weights `d j` are arbitrary reals. -/
theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_of_diagonal
    (hA : IsOneOne A) (d : Fin n → ℝ)
    (hdiag : normalizedHermitianMatrix A = Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have key : ∀ j k : Fin n, hermitianEntry A (coordinateVector j) (coordinateVector k) =
      if j = k then ((d j / Real.pi : ℝ) : ℂ) else 0 := by
    intro j k
    have h : (Real.pi : ℂ) * hermitianEntry A (coordinateVector j) (coordinateVector k) =
        (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) j k := by
      rw [← normalizedHermitianMatrix_apply', hdiag]
    by_cases hjk : j = k
    · subst hjk
      rw [Matrix.diagonal_apply_eq] at h
      rw [ite_eq_left rfl]
      push_cast
      field_simp
      linear_combination h
    · rw [Matrix.diagonal_apply_ne _ hjk] at h
      rw [ite_eq_right hjk]
      exact (mul_eq_zero.1 h).resolve_left hpiC
  have hre : ∀ j k : Fin n, A ![coordinateVector j, Complex.I • coordinateVector k] =
      if j = k then d j / Real.pi else 0 := by
    intro j k
    have h := congrArg Complex.re (key j k)
    simpa [hermitianEntry, apply_ite Complex.re] using h
  have him : ∀ j k : Fin n, A ![coordinateVector j, coordinateVector k] = 0 := by
    intro j k
    have h := congrArg Complex.im (key j k)
    have hrhs : (if j = k then ((d j / Real.pi : ℝ) : ℂ) else 0).im = 0 := by
      by_cases hjk : j = k <;> simp [hjk]
    rw [hrhs] at h
    simp only [hermitianEntry, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_sub,
      neg_eq_zero, zero_add] at h
    linarith
  have hframe : ∀ a c : Fin n × Fin 2,
      A ![coordinateRealFrame (finProdFinEquiv a), coordinateRealFrame (finProdFinEquiv c)] =
        if a.1 = c.1 then (fun j => d j / Real.pi) a.1 *
          (((c.2 : ℕ) : ℝ) - ((a.2 : ℕ) : ℝ)) else 0 := by
    rintro ⟨j, b⟩ ⟨k, c⟩
    rw [coordinateTwoForm_apply_realFrame_block A hA j k b c, him j k, hre j k]
    by_cases hjk : j = k
    · subst hjk
      fin_cases b <;> fin_cases c <;> norm_num
    · fin_cases b <;> fin_cases c <;> simp [hjk]
  rw [actualTopPowerDensity_eq_factorial_mul_prod_of_diagonal_weights A
      (fun j => d j / Real.pi) hframe,
    normalizedTopPowerDensity, complexTopCoefficient_eq, hdiag, Matrix.det_diagonal]
  have hprod : (∏ j, ((d j : ℝ) : ℂ)) = ((∏ j, d j : ℝ) : ℂ) := by push_cast; ring
  rw [hprod, ← Complex.ofReal_mul, Complex.ofReal_re, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp

end Diagonal

section General

open Matrix

/-- **The exterior-power/determinant density identity for an ARBITRARY real
`(1,1)`-form.**  The genuine top exterior power of `A` on the standard real frame
is the Bedford--Taylor determinant density of its complex coefficient matrix, with
no semipositivity hypothesis — so it applies to `β + ddᶜ v` for an arbitrary
chart-smooth real `v`, not only to semipositive forms.

This is the blueprint statement `fpma:geometric-density`; the semipositive case is
`actualTopPowerDensity_eq_normalizedTopPowerDensity_of_semipositive`.
-/
theorem actualTopPowerDensity_eq_normalizedTopPowerDensity
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  classical
  have hH : (normalizedHermitianMatrix A).IsHermitian :=
    normalizedHermitianMatrix_isHermitian A hA
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  set S : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm (U.map (starRingEnd ℂ)) with hSdef
  have hSM : standardMatrix S = U.map (starRingEnd ℂ) := by
    rw [standardMatrix, hSdef, LinearEquiv.apply_symm_apply]
  have htrans : (U.map (starRingEnd ℂ))ᵀ = star U := by
    ext j k
    simp
  have hmapmap : (U.map (starRingEnd ℂ)).map (starRingEnd ℂ) = U := by
    ext j k
    simp
  have hdiag : normalizedHermitianMatrix (compLinearMap A S) =
      Matrix.diagonal fun j => ((hH.eigenvalues j : ℝ) : ℂ) := by
    rw [normalizedHermitianMatrix_compLinearMap hA, hSM, htrans, hmapmap]
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← hUdef] at this
    exact this
  have hdetU : Complex.normSq (Matrix.det U) = 1 := by
    have h1 : (star U) * U = 1 := by
      rw [hUdef]
      exact_mod_cast Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have h2 : (starRingEnd ℂ) (Matrix.det U) * Matrix.det U = 1 := by
      have := congrArg Matrix.det h1
      rwa [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose,
        Matrix.det_conjTranspose, Complex.star_def] at this
    have h3 : ((Complex.normSq (Matrix.det U) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h2
    exact_mod_cast h3
  have hdetS : Complex.normSq (LinearMap.det S) = 1 := by
    have hd : LinearMap.det S = (U.map (starRingEnd ℂ)).det := by
      rw [← det_standardMatrix, hSM]
    have hconj : (U.map (starRingEnd ℂ)).det = (starRingEnd ℂ) U.det :=
      (RingHom.map_det (starRingEnd ℂ) U).symm
    rw [hd, hconj, Complex.normSq_conj, hdetU]
  have h3 := actualTopPowerDensity_eq_normalizedTopPowerDensity_of_diagonal
    (isOneOne_compLinearMap hA S) (fun j => hH.eigenvalues j) hdiag
  rw [actualTopPowerDensity_compLinearMap S, normalizedTopPowerDensity_compLinearMap hA S,
    hdetS, one_mul, one_mul] at h3
  exact h3

/-- **The geometric meaning of the coordinate density** (blueprint
`fpma:geometric-density`).  For a twice differentiable real function `u`, the
density of the genuine top exterior power `(ddᶜu)^n` with respect to Lebesgue
measure in the standard complex orientation is `D_u = smoothDensity u`.  No
plurisubharmonicity is assumed. -/
theorem actualTopPowerDensity_smoothDDC {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) :
    actualTopPowerDensity (smoothDDC u z) = smoothDensity u z := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity _ (smoothDDC_isOneOne hu),
    normalizedTopPowerDensity_smoothDDC hu]

end General

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere

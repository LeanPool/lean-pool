/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Gram determinants of a positive semidefinite bilinear form, and Hadamard's inequality

Let `E` be a finite-dimensional real inner product space and `Q : E →L[ℝ] E →L[ℝ] ℝ` a symmetric
positive semidefinite bilinear form.

* `riesz b ℓ = ∑ i, ℓ (b i) • b i` is the Riesz map of an orthonormal basis `b`
  (`inner_riesz : ⟪y, riesz b ℓ⟫ = ℓ y`; it does not depend on `b`), and
  `riesz b (innerSL ℝ p) = p` (`riesz_innerSL`).  For `Q = D²v(x)`, `riesz b ∘L Q` is the
    derivative
  of the gradient map `x ↦ riesz b (Dv(x))` (used by the Alexandrov--Bakelman--Pucci estimate).
* `det_riesz_comp`: `det (riesz b ∘L Q) = det (Q (c k) (c l))` for EVERY orthonormal basis `c`,
    so the
  Gram determinant of `Q` does not depend on the orthonormal basis.
* `posSemidef_gram`: the Gram matrix `(Q (c k) (c l))` is positive semidefinite.
* `det_le_prod_diag` (**Hadamard's inequality**): for a real positive semidefinite matrix,
  `det M ≤ ∏ M_kk` (rescale to unit diagonal, then AM--GM on the eigenvalues).
* `det_gram_le_prod`: `det (Q (b i) (b j)) ≤ ∏_k Q (c k) (c k)` for any two orthonormal bases.

Hadamard's inequality is the step "for real nonnegative symmetric matrices `(a_pq)` one has
`det(a_pq) ≤ a_11 ⋯ a_mm`" of Błocki's proof of the uniform estimate
(`blocki05-uniform-estimate:page-0003`, `lnm2038-monge-ampere:page-0220`).  TN.4 B5, nonlinear
track N2.
-/

@[expose] public section

open Matrix
open scoped InnerProductSpace RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.GramDeterminant

/-! ### Hadamard's inequality -/

section Hadamard

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- In a positive semidefinite real matrix, a zero diagonal entry kills its row. -/
theorem apply_eq_zero_of_diag_eq_zero {M : Matrix κ κ ℝ} (hM : M.PosSemidef) {k : κ}
    (hk : M k k = 0) (j : κ) : M k j = 0 := by
  have hsymm : M j k = M k j := by
    have := congrFun (congrFun hM.1 k) j
    simpa [Matrix.conjTranspose_apply] using this
  have h2 := (hM.submatrix ![k, j]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hk, zero_mul,
    zero_sub, hsymm] at h2
  nlinarith [sq_nonneg (M k j)]

/-- **Hadamard's inequality**: a positive semidefinite real matrix has `det M ≤ ∏ M_kk`. -/
theorem det_le_prod_diag {M : Matrix κ κ ℝ} (hM : M.PosSemidef) : M.det ≤ ∏ k, M k k := by
  by_cases hz : ∃ k, M k k = 0
  · obtain ⟨k, hk⟩ := hz
    rw [Matrix.det_eq_zero_of_row_eq_zero k (apply_eq_zero_of_diag_eq_zero hM hk)]
    exact Finset.prod_nonneg fun i _ => hM.diag_nonneg
  simp only [not_exists] at hz
  have hpos : ∀ k, 0 < M k k := fun k => lt_of_le_of_ne hM.diag_nonneg (Ne.symm (hz k))
  by_cases hκ : IsEmpty κ
  · simp [Matrix.det_isEmpty]
  rw [not_isEmpty_iff] at hκ
  -- rescale to unit diagonal
  set d : κ → ℝ := fun k => (Real.sqrt (M k k))⁻¹ with hd
  have hdpos : ∀ k, 0 < d k := fun k => inv_pos.mpr (Real.sqrt_pos.mpr (hpos k))
  set D : Matrix κ κ ℝ := Matrix.diagonal d with hD
  set Nm : Matrix κ κ ℝ := D * M * D with hN
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]; simp
  have hNpsd : Nm.PosSemidef := by
    have := hM.mul_mul_conjTranspose_same D
    rwa [hDh] at this
  have hNdiag : ∀ k, Nm k k = 1 := by
    intro k
    simp only [hN, hD, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have h := Real.mul_self_sqrt (hpos k).le
    have hs : Real.sqrt (M k k) ≠ 0 := (Real.sqrt_pos.mpr (hpos k)).ne'
    rw [hd]
    field_simp
    nlinarith [h]
  have hdetN : Nm.det = (∏ k, d k) ^ 2 * M.det := by
    simp only [hN, Matrix.det_mul, hD, Matrix.det_diagonal]; ring
  -- `det N ≤ 1` by AM--GM on the eigenvalues
  have hN1 : Nm.det ≤ 1 := by
    set ev := hNpsd.1.eigenvalues with hev
    have hevnn : ∀ i, 0 ≤ ev i := hNpsd.eigenvalues_nonneg
    have hdet : Nm.det = ∏ i, ev i := by
      have := hNpsd.1.det_eq_prod_eigenvalues
      simpa using this
    have htr : Nm.trace = ∑ i, ev i := by
      have := hNpsd.1.trace_eq_sum_eigenvalues
      simpa using this
    have htr' : Nm.trace = Fintype.card κ := by
      simp [Matrix.trace, hNdiag]
    have hcard : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    have hamgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) ev
      (fun _ _ => zero_le_one) (by simpa using hcard) (fun i _ => hevnn i)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hamgm
    rw [← htr, htr', div_self hcard.ne'] at hamgm
    rw [hdet]
    have hp : 0 ≤ ∏ i, ev i := Finset.prod_nonneg fun i _ => hevnn i
    exact (Real.rpow_inv_le_iff_of_pos hp zero_le_one hcard).mp hamgm |>.trans (by simp)
  have hprod : (∏ k, d k) ^ 2 * ∏ k, M k k = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k _
    rw [hd, inv_pow, Real.sq_sqrt (hpos k).le, inv_mul_cancel₀ (hpos k).ne']
  have hdp : 0 < (∏ k, d k) ^ 2 := by
    have := Finset.prod_pos fun k (_ : k ∈ Finset.univ) => hdpos k
    positivity
  have : (∏ k, d k) ^ 2 * M.det ≤ (∏ k, d k) ^ 2 * ∏ k, M k k := by
    rw [← hdetN, hprod]; exact hN1
  exact le_of_mul_le_mul_left this hdp

end Hadamard

/-! ### The Riesz map of an orthonormal basis and Gram determinants -/

section Gram

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Riesz map `ℓ ↦ ∑ i, ℓ (b i) • b i` of an orthonormal basis (independent of the basis,
`inner_riesz`). -/
noncomputable def riesz (b : OrthonormalBasis ι ℝ E) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.apply ℝ ℝ (b i)).smulRight (b i)

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
theorem riesz_apply (b : OrthonormalBasis ι ℝ E) (ℓ : E →L[ℝ] ℝ) :
    riesz b ℓ = ∑ i, ℓ (b i) • b i := by
  simp [riesz, _root_.sum_apply]

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
theorem inner_riesz (b : OrthonormalBasis ι ℝ E) (ℓ : E →L[ℝ] ℝ) (y : E) :
    ⟪y, riesz b ℓ⟫ = ℓ y := by
  rw [riesz_apply, inner_sum]
  conv_rhs => rw [← b.sum_repr' y]
  simp only [map_sum, map_smul, smul_eq_mul, inner_smul_right, real_inner_comm (b _) y]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
theorem riesz_innerSL (b : OrthonormalBasis ι ℝ E) (p : E) :
    riesz b (innerSL ℝ p) = p := by
  rw [riesz_apply]
  conv_rhs => rw [← b.sum_repr' p]
  simp only [innerSL_apply_apply, real_inner_comm p]

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- The determinant of `riesz b ∘L Q` is the Gram determinant of `Q` in ANY orthonormal basis. -/
theorem det_riesz_comp (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    ((riesz b).comp Q).det = (Matrix.of fun k l => Q (c k) (c l)).det := by
  have hM : LinearMap.toMatrix c.toBasis c.toBasis ((riesz b).comp Q : E →ₗ[ℝ] E) =
      (Matrix.of fun k l => Q (c k) (c l))ᵀ := by
    refine Matrix.ext fun k l => ?_
    rw [LinearMap.toMatrix_apply]
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, inner_riesz, Matrix.transpose_apply, Matrix.of_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix c.toBasis, hM, Matrix.det_transpose]

omit [DecidableEq κ] [FiniteDimensional ℝ E] in
/-- The Gram matrix of a symmetric positive semidefinite bilinear form is positive
semidefinite. -/
theorem posSemidef_gram (c : OrthonormalBasis κ ℝ E) {Q : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (hpos : ∀ x, 0 ≤ Q x x) :
    (Matrix.of fun k l => Q (c k) (c l)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.ext fun k l => ?_
    simp [Matrix.conjTranspose_apply, hsymm (c l) (c k)]
  · have hx : star x ⬝ᵥ ((Matrix.of fun k l => Q (c k) (c l)) *ᵥ x) =
        Q (∑ k, x k • c k) (∑ l, x l • c l) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, map_smul,
        _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hsymm (c l) (c k)]; ring
    rw [hx]
    exact hpos _

omit [FiniteDimensional ℝ E] in
theorem det_gram_nonneg (c : OrthonormalBasis κ ℝ E) {Q : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (hpos : ∀ x, 0 ≤ Q x x) :
    0 ≤ (Matrix.of fun k l => Q (c k) (c l)).det := by
  classical
  exact (posSemidef_gram c hsymm hpos).det_nonneg

omit [DecidableEq κ] [FiniteDimensional ℝ E] in
/-- **Hadamard's inequality for Gram determinants**, across orthonormal bases:
`det (Q (b i) (b j)) ≤ ∏_k Q (c k) (c k)`. -/
theorem det_gram_le_prod (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    {Q : E →L[ℝ] E →L[ℝ] ℝ} (hsymm : ∀ x y, Q x y = Q y x) (hpos : ∀ x, 0 ≤ Q x x) :
    (Matrix.of fun i j => Q (b i) (b j)).det ≤ ∏ k, Q (c k) (c k) := by
  classical
  rw [← det_riesz_comp b b Q, det_riesz_comp b c Q]
  have := det_le_prod_diag (posSemidef_gram c hsymm hpos)
  simpa using this

end Gram

end SGPT.Foundations.Analysis.Pending.GramDeterminant

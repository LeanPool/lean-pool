/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GramDeterminant
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SemiconcaveDegenerateHessian

/-!
# The real Hessian determinant is bounded by the square of the complex one

For a symmetric positive semidefinite real bilinear form `Q` on `ℂⁿ = ℝ²ⁿ` (the real Hessian
`D²u(z)` of a `C²` function at a point where `D²u ≥ 0`) with complex Hessian matrix
`H = complexHessianOfBilin Q` (`H_{jkBar} = (Q(e_j, e_k) + Q(ie_j, ie_k))/4 + i(Q(e_j, ie_k)
    - Q(ie_j, e_k))/4`):

`det (Q (b α) (b β)) ≤ 4ⁿ (det H)²`  for every real orthonormal basis `b`
    (`det_le_four_pow_mul_sq`),

and `0 ≤ Re det H` (`re_det_nonneg`).  This is Błocki's pointwise inequality
`det D²u ≤ 4ⁿ (det(u_{jkBar}))²` (`blocki05-uniform-estimate:page-0002`--`page-0003`,
    proof of Theorem 1;
`lnm2038-monge-ampere:page-0220`).

## Proof (Błocki's)

Let `w_1, …, w_n` be an orthonormal eigenbasis of `H` with eigenvalues `λ_l`, and `x_l` the vector
with coordinates `conj (w_l)`.  Then `(x_l, i x_l)` is a real orthonormal basis of `ℂⁿ` and
`λ_l = (Q(x_l, x_l) + Q(ix_l, ix_l))/4` (the quadratic form of `H` is the Levi form,
`dotProduct_mulVec_complexHessianOfBilin`).  By Hadamard's inequality in this basis
(`GramDeterminant.det_gram_le_prod`) and `st ≤ ((s + t)/2)²`,
`det ≤ ∏_l Q(x_l, x_l) Q(ix_l, ix_l) ≤ ∏_l (2λ_l)² = 4ⁿ (det H)²`.

TN.4 B5, nonlinear track N2 (b).
-/

@[expose] public section

open Matrix
open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant

open FirstPass FirstPass.MongeAmpere SemiconcaveHessian GramDeterminant

variable {n : ℕ}

/-- The complex Hessian of a symmetric bilinear form is Hermitian. -/
theorem isHermitian_complexHessianOfBilin {Q : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) : (complexHessianOfBilin Q).IsHermitian := by
  ext j k
  apply Complex.ext <;>
    simp [Matrix.conjTranspose_apply, complexHessianOfBilin, hsymm (coordinateVector k)
      (coordinateVector j),
      hsymm (Complex.I • coordinateVector k) (Complex.I • coordinateVector j),
      hsymm (coordinateVector k) (Complex.I • coordinateVector j),
      hsymm (Complex.I • coordinateVector k) (coordinateVector j)]

theorem I_smul_coordCombination (y : Fin n → ℂ) :
    Complex.I • coordCombination y =
      ∑ j, ((y j).im • coordinateVector j + (y j).re • (Complex.I • coordinateVector j)) := by
  unfold coordCombination
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_sub, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  rw [← sub_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

/-- The quadratic form of `complexHessianOfBilin Q` is the Levi form of `Q` at the vector with the
conjugate coordinates. -/
theorem dotProduct_mulVec_complexHessianOfBilin {Q : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((complexHessianOfBilin Q).mulVec y) =
      ((leviFormOfBilin Q (coordCombination y) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [leviFormOfBilin, Complex.ofReal_re]
    rw [I_smul_coordCombination y]
    simp [dotProduct, Matrix.mulVec, complexHessianOfBilin, coordCombination,
      Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_eq_mul]
    ring_nf
    simp_rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [Finset.sum_mul]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm (coordinateVector i) (Complex.I • coordinateVector j),
      hsymm (Complex.I • coordinateVector i) (coordinateVector j)]
    ring
  · simpa using (isHermitian_complexHessianOfBilin hsymm).im_star_dotProduct_mulVec_self y

/-- `coordCombination y` is the vector with coordinates `conj (y j)`. -/
theorem coordCombination_eq_toLp (y : Fin n → ℂ) :
    coordCombination y = WithLp.toLp 2 (fun j => star (y j)) := by
  have h := coordCombination_star (n := n) (WithLp.toLp 2 (fun j => star (y j)))
  simpa using h

theorem real_inner_eq_re (u v : ComplexModel n) : ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
  simp [PiLp.inner_apply, Complex.inner, Complex.re_sum, mul_comm]

/-- The two complex units `1, i`. -/
def unitPair : Fin 2 → ℂ := ![1, Complex.I]

theorem re_conj_unitPair_mul (s t : Fin 2) :
    (conj (unitPair s) * unitPair t).re = if s = t then 1 else 0 := by
  fin_cases s <;> fin_cases t <;> simp [unitPair]

/-- From a complex orthonormal family `x_l`, the real family `(x_l, i x_l)` is orthonormal. -/
theorem orthonormal_unitPair_smul {x : Fin n → ComplexModel n} (hx : Orthonormal ℂ x) :
    Orthonormal ℝ (fun p : Fin n × Fin 2 => unitPair p.2 • x p.1) := by
  rw [orthonormal_iff_ite]
  rintro ⟨l, s⟩ ⟨m, t⟩
  rw [real_inner_eq_re, inner_smul_left, inner_smul_right, ← mul_assoc,
    (orthonormal_iff_ite.mp hx) l m]
  by_cases hlm : l = m
  · subst hlm
    simp only [ite_true, mul_one, re_conj_unitPair_mul, Prod.mk.injEq, true_and]
  · simp [hlm]

/-- **Błocki's inequality** `det D²u ≤ 4ⁿ (det u_{jkBar})²` at a point where `D²u ≥ 0`, for a
symmetric positive semidefinite real bilinear form on `ℂⁿ` and any real orthonormal basis
(`blocki05-uniform-estimate:page-0002`--`page-0003`). -/
theorem det_le_four_pow_mul_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (Q : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (hsymm : ∀ x y, Q x y = Q y x) (hpos : ∀ x, 0 ≤ Q x x) :
    (Matrix.of fun i j => Q (b i) (b j)).det ≤
      4 ^ n * ((complexHessianOfBilin Q).det.re) ^ 2 := by
  classical
  set H := complexHessianOfBilin Q with hHdef
  have hH := isHermitian_complexHessianOfBilin hsymm
  set w := hH.eigenvectorBasis with hw
  set ev := hH.eigenvalues with hev
  -- the conjugate eigenvectors
  set x : Fin n → ComplexModel n := fun l => coordCombination (⇑(w l)) with hxdef
  have hxinner : ∀ l m, ⟪x l, x m⟫_ℂ = if l = m then 1 else 0 := by
    intro l m
    have hwo := (orthonormal_iff_ite.mp w.orthonormal) m l
    simp only [hxdef, coordCombination_eq_toLp, EuclideanSpace.inner_toLp_toLp]
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hwo
    have : (fun j => star ((w m : Fin n → ℂ) j)) ⬝ᵥ star (fun j => star ((w l : Fin n → ℂ) j)) =
        (WithLp.ofLp (w l)) ⬝ᵥ star (WithLp.ofLp (w m)) := by
      rw [dotProduct_comm]; simp [dotProduct]
    rw [this, hwo]
    by_cases h : l = m
    · simp [h]
    · simp [h, Ne.symm h]
  have hxo : Orthonormal ℂ x := orthonormal_iff_ite.mpr hxinner
  -- the eigenvalues are Levi values
  have hlevi : ∀ l, leviFormOfBilin Q (x l) = ev l := by
    intro l
    have h1 := dotProduct_mulVec_complexHessianOfBilin hsymm (⇑(w l))
    rw [← hHdef, hH.mulVec_eigenvectorBasis l, dotProduct_smul] at h1
    have hn1 : star (⇑(w l)) ⬝ᵥ (⇑(w l)) = 1 := by
      have := (orthonormal_iff_ite.mp w.orthonormal) l l
      rw [ite_eq_left rfl, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
      exact this
    rw [hn1] at h1
    have := congrArg Complex.re h1
    simpa [hxdef] using this.symm
  -- the real orthonormal basis `(x_l, i x_l)`
  set c : Fin n × Fin 2 → ComplexModel n := fun p => unitPair p.2 • x p.1 with hcdef
  have hco : Orthonormal ℝ c := orthonormal_unitPair_smul hxo
  have hcard : Fintype.card (Fin n × Fin 2) = Module.finrank ℝ (ComplexModel n) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace]; simp [mul_comm]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range c) :=
    (hco.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge
  set cb := OrthonormalBasis.mk hco hsp with hcb
  have hcbc : ⇑cb = c := OrthonormalBasis.coe_mk hco hsp
  -- Hadamard in the basis `cb`, then AM-GM pairwise
  have hhad := det_gram_le_prod b cb hsymm hpos
  rw [hcbc, Fintype.prod_prod_type] at hhad
  have hpair : ∀ l, (∏ s : Fin 2, Q (c (l, s)) (c (l, s))) ≤ 4 * ev l ^ 2 := by
    intro l
    rw [Fin.prod_univ_two]
    have h0 : c (l, 0) = x l := by simp [hcdef, unitPair]
    have h1 : c (l, 1) = Complex.I • x l := by simp [hcdef, unitPair]
    rw [h0, h1, ← hlevi l, leviFormOfBilin]
    nlinarith [sq_nonneg (Q (x l) (x l) - Q (Complex.I • x l) (Complex.I • x l))]
  have hprod : (∏ l, ∏ s : Fin 2, Q (c (l, s)) (c (l, s))) ≤ ∏ l, (4 * ev l ^ 2) :=
    Finset.prod_le_prod₀ (fun l _ => Finset.prod_nonneg fun s _ => hpos _) fun l _ => hpair l
  have hdet : H.det.re = ∏ l, ev l := by
    rw [hH.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact Complex.ofReal_re _
  calc (Matrix.of fun i j => Q (b i) (b j)).det ≤ ∏ l, (4 * ev l ^ 2) := hhad.trans hprod
    _ = 4 ^ n * (H.det.re) ^ 2 := by
      rw [hdet, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow]

/-- For a positive semidefinite symmetric `Q`, `det H ≥ 0`. -/
theorem re_det_nonneg {Q : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (hpos : ∀ x, 0 ≤ Q x x) :
    0 ≤ (complexHessianOfBilin Q).det.re := by
  classical
  have hH := isHermitian_complexHessianOfBilin hsymm
  have hpsd : (complexHessianOfBilin Q).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
    rw [dotProduct_mulVec_complexHessianOfBilin hsymm y]
    have : 0 ≤ leviFormOfBilin Q (coordCombination y) := by
      unfold leviFormOfBilin
      have := hpos (coordCombination y)
      have := hpos (Complex.I • coordCombination y)
      positivity
    exact_mod_cast this
  exact (Complex.nonneg_iff.mp hpsd.det_nonneg).1

/-- The coordinate complex Hessian of `u` is `complexHessianOfBilin` of its second derivative. -/
theorem complexHessian_eq_complexHessianOfBilin (u : ComplexModel n → ℝ) (z : ComplexModel n) :
    complexHessian u z = complexHessianOfBilin (fderiv ℝ (fderiv ℝ u) z) := by
  ext j k
  simp [complexHessian, complexHessianOfBilin, realHessian_eq_fderiv]

end SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant

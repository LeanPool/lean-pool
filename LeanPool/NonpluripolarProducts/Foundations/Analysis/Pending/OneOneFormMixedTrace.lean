/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalProductCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DeterminantTraceInf

/-!
# `α ∧ β^{n-1}` as a trace, and `det^{1/n}` as an infimum over `β`

Blueprint `ana:mixed-trace-infimum` (`blueprint/src/analytic.tex`; TN.5, toward
    `ana:volume-semicontinuity`: the
identification of the infimum functional of `ana:ac-density-liminf` with `det^{1/n}` for constant
    `(1,1)`-forms).  Source:
Boucksom 2002 (`bou02-volume`), the use of `det(α)^{1/n}` with `det(α) = αⁿ/ωⁿ` in Lemma 3.5
    (arXiv); the matrix identities
are elementary (Laplace expansion along a row, `(n-1)!` permutations fixing a slot, AM-GM).

On `ℂⁿ`, `n = m + 1`, write `H_α` for the normalized Hermitian coefficient matrix of a real
    `(1,1)`-form `α`
(`normalizedHermitianMatrix`; `α = (i/2π) ∑ H_{jk} dz_j ∧ dzBar_k`) and `topDensity` for the value
    of a top-degree form on the
standard real frame (`TopDegreeDensity`), so that `topDensity (αⁿ) = n! det H_α / πⁿ`.

* `sum_perm_apply`: `∑_σ f(σ i) = m! ∑_j f j` for the permutations of `Fin (m + 1)`;
* `det_updateRow_eq_sum_adjugate`: `det (B with row j replaced by b) = ∑_k b_k adj(B)_{kj}`
    (Laplace);
* `mixedCoefficient_update_const`: the mixed coefficient of `(B, …, B, A, B, …, B)` is
    `m! tr (A adj B)`;
* **`topDensity_wedge_formPower`**: `topDensity (β^m ∧ α) = m! Re tr (H_α adj H_β) / π^{m+1}`
    (real `(1,1)`-forms; for
  `det H_β ≠ 0` this is `m! det H_β tr (H_β⁻¹ H_α) / πⁿ`);
* `exists_isSemipositiveOneOne_normalizedHermitianMatrix_eq`: every positive definite Hermitian
    matrix is `H_β` for a
  semipositive `(1,1)`-form `β` (a pullback of the standard form);
* **`isGLB_topDensity_wedge_formPower`**: for a semipositive `(1,1)`-form `α`, the infimum of
    `topDensity (β^m ∧ α)` over the
  semipositive `β` with `H_β` positive definite of determinant `1` is
    `(n!/πⁿ) (πⁿ/n! · topDensity(αⁿ))^{1/n}`, i.e.
  `(n!/πⁿ) det(H_α)^{1/n}` (with `ana:determinant-trace-inf`).

Sorry-free.
-/

@[expose] public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder MatrixOrder

namespace SGPT.Foundations.Analysis.Pending.OneOneFormMixedTrace

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
    TopDegreeDensity
  DeterminantTraceInf MinkowskiDeterminant

/-! ### Permutations and rows -/

/-- **`∑_σ f(σ i) = m! ∑_j f j`** over the permutations of `Fin (m + 1)`. -/
theorem sum_perm_apply {M : Type*} [AddCommMonoid M] (m : ℕ) (f : Fin (m + 1) → M)
    (i : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), f (σ i) = m.factorial • ∑ j, f j := by
  -- reduce to `i = 0` by right multiplication with the swap of `0` and `i`
  have h0 : ∑ σ : Equiv.Perm (Fin (m + 1)), f (σ i) = ∑ σ : Equiv.Perm (Fin (m + 1)), f (σ 0) := by
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap 0 i)) _ _ fun σ => ?_
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  rw [h0]
  have h1 : ∑ σ : Equiv.Perm (Fin (m + 1)), f (σ 0) =
      ∑ p : Fin (m + 1) × Equiv.Perm (Fin m), f p.1 := by
    refine Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ fun σ => ?_
    conv_lhs => rw [← Equiv.symm_apply_apply Equiv.Perm.decomposeFin σ]
    rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [Finset.smul_sum]

/-- **Laplace expansion along a row**: `det (updateRow B j b) = ∑_k b_k adj(B)_{kj}`. -/
theorem det_updateRow_eq_sum_adjugate {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (b : Fin n → ℂ) :
    (B.updateRow j b).det = ∑ k, b k * adjugate B k j := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, mulVec,
    dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [transpose_apply, mul_comm]

/-- **The mixed coefficient of `(B, …, A, …, B)`** (one slot `A`) is `m! tr (A adj B)`. -/
theorem mixedCoefficient_update_const (m : ℕ) (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (i : Fin (m + 1)) :
    MixedMongeAmpere.mixedCoefficient (Function.update (fun _ => B) i A) =
      (m.factorial : ℂ) * (A * adjugate B).trace := by
  unfold MixedMongeAmpere.mixedCoefficient
  have hrow : ∀ σ : Equiv.Perm (Fin (m + 1)),
      Matrix.det (fun j k => Function.update (fun _ => B) i A (σ j) j k) =
        ∑ k, A (σ.symm i) k * adjugate B k (σ.symm i) := by
    intro σ
    have h := mixedCoefficient_updateRow (fun _ => B) i A σ
    have hB : (Matrix.of fun j k => (fun _ => B : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1))
      ℂ) (σ j) j k) = B := by
      ext j k
      rfl
    rw [hB] at h
    change Matrix.det (Matrix.of fun j k => Function.update (fun _ => B) i A (σ j) j k) = _
    rw [h, det_updateRow_eq_sum_adjugate]
  simp_rw [hrow]
  rw [show (∑ σ : Equiv.Perm (Fin (m + 1)), ∑ k, A (σ.symm i) k * adjugate B k (σ.symm i)) =
      ∑ σ : Equiv.Perm (Fin (m + 1)), ∑ k, A (σ i) k * adjugate B k (σ i) from
    Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => rfl]
  rw [sum_perm_apply m (fun j => ∑ k, A j k * adjugate B k j) i, nsmul_eq_mul]
  congr 1

/-! ### `β^m ∧ α` as a trace -/

section Forms

variable {m : ℕ}

/-- The coefficient matrices of the family `(β, …, β, α)`. -/
theorem normalizedHermitianMatrix_snoc (α β : RealForm (m + 1) 2) :
    (fun i => normalizedHermitianMatrix (Fin.snoc (α := fun _ => RealForm (m + 1) 2) (fun _ => β)
      α i)) =
      Function.update (fun _ => normalizedHermitianMatrix β) (Fin.last m)
        (normalizedHermitianMatrix α) := by
  funext i
  by_cases hi : i = Fin.last m
  · subst hi
    simp
  · rw [Function.update_of_ne hi]
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simp

/-- **`β^m ∧ α` as a trace**: for real `(1,1)`-forms on `ℂ^{m+1}`,
`topDensity (β^m ∧ α) = m! Re tr (H_α adj H_β) / π^{m+1}`. -/
theorem topDensity_wedge_formPower (α β : RealForm (m + 1) 2) (hα : IsOneOne α) (hβ : IsOneOne β) :
    topDensity (coordinateWedge (formPower β m) α) =
      (m.factorial : ℝ) * (normalizedHermitianMatrix α * adjugate (normalizedHermitianMatrix
        β)).trace.re /
        Real.pi ^ (m + 1) := by
  have h1 : coordinateWedge (formPower β m) α = wedgeProd (m + 1) (Fin.snoc (fun _ => β) α) := by
    rw [wedgeProd_snoc, formPower_eq_wedgeProd]
  have hall : ∀ i : Fin (m + 1), IsOneOne (Fin.snoc (α := fun _ => RealForm (m + 1) 2)
    (fun _ => β) α i) := by
    intro i
    by_cases hi : i = Fin.last m
    · subst hi
      simpa using hα
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      simpa using hβ
  rw [h1, topDensity_wedgeProd, actualMixedTopDensity_eq_normalizedMixedTopDensity _ hall,
    normalizedMixedTopDensity, normalizedHermitianMatrix_snoc, mixedCoefficient_update_const]
  simp [Complex.mul_re]

/-- **Every positive semidefinite Hermitian matrix is the coefficient matrix of a semipositive
    `(1,1)`-form** (a pullback of
the standard form). -/
theorem exists_isSemipositiveOneOne_normalizedHermitianMatrix_eq {n : ℕ} {M : Matrix (Fin n)
    (Fin n) ℂ}
    (hM : M.PosSemidef) : ∃ β : RealForm n 2, IsSemipositiveOneOne β ∧ normalizedHermitianMatrix β
      = M := by
  set N : Matrix (Fin n) (Fin n) ℂ := ((Real.pi : ℂ)⁻¹) • M.map (starRingEnd ℂ) with hNdef
  have hMt : M.map (starRingEnd ℂ) = Mᵀ := by
    ext j k
    have h := congrFun (congrFun hM.isHermitian k) j
    simp only [conjTranspose_apply] at h
    simp [← h]
  have hN : N.PosSemidef := by
    rw [hNdef, hMt]
    exact hM.transpose.smul (by
      have : (0 : ℂ) < (Real.pi : ℂ)⁻¹ := by
        rw [← Complex.ofReal_inv]
        exact_mod_cast inv_pos.mpr Real.pi_pos
      exact this.le)
  obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN.nonneg
  set S : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm y with hSdef
  have hS : standardMatrix S = y := by
    rw [standardMatrix, hSdef, LinearEquiv.apply_symm_apply]
  refine ⟨standardPullback S, ?_, ?_⟩
  · exact (LocalProductCurrents.isSemipositiveOneOne_kahlerForm (n := n)).comp _ fun v => by simp
  · rw [normalizedHermitianMatrix_standardPullback, gramMatrix_eq, hS, ←
    Matrix.star_eq_conjTranspose, ← hy, hNdef]
    ext j k
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀,
      Complex.conj_ofReal,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    field_simp

/-- The wedge-density infimum expressed in terms of the Hermitian determinant. -/
theorem isGLB_topDensity_wedge_formPower_of_posSemidef {α : RealForm (m + 1) 2} (hα : IsOneOne α)
    (hA : (normalizedHermitianMatrix α).PosSemidef) :
    IsGLB {s : ℝ | ∃ β : RealForm (m + 1) 2, IsSemipositiveOneOne β ∧ (normalizedHermitianMatrix
      β).PosDef ∧
        (normalizedHermitianMatrix β).det = 1 ∧ s = topDensity (coordinateWedge (formPower β m) α)}
      (((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) *
        (normalizedHermitianMatrix α).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
  set A := normalizedHermitianMatrix α with hAdef
  set c : ℝ := ((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) with hcdef
  have hc : 0 < c := by positivity
  have hGLB := isGLB_re_trace_div hA
  rw [Fintype.card_fin] at hGLB
  have hval : ∀ β : RealForm (m + 1) 2, IsSemipositiveOneOne β → (normalizedHermitianMatrix
    β).PosDef →
      (normalizedHermitianMatrix β).det = 1 →
      topDensity (coordinateWedge (formPower β m) α) =
        c * (((normalizedHermitianMatrix β)⁻¹ * A).trace.re / ((m + 1 : ℕ) : ℝ)) := by
    intro β hβ hpd hdet
    have hadj : adjugate (normalizedHermitianMatrix β) = (normalizedHermitianMatrix β)⁻¹ := by
      rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    rw [topDensity_wedge_formPower α β hα hβ.1, hadj, Matrix.trace_mul_comm, hcdef,
      Nat.factorial_succ]
    push_cast
    field_simp
    rfl
  refine ⟨?_, fun b hb => ?_⟩
  · rintro s ⟨β, hβ, hpd, hdet, rfl⟩
    rw [hval β hβ hpd hdet]
    refine mul_le_mul_of_nonneg_left (hGLB.1 ⟨_, hpd.inv, ?_, rfl⟩) hc.le
    rw [Matrix.det_nonsing_inv, hdet, Ring.inverse_one]
  · have hlow : b / c ∈ lowerBounds {s : ℝ | ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ,
    B.PosDef ∧ B.det = 1 ∧
        s = (B * A).trace.re / ((m + 1 : ℕ) : ℝ)} := by
      rintro s ⟨B, hB, hdetB, rfl⟩
      obtain ⟨β, hβ, hHβ⟩ := exists_isSemipositiveOneOne_normalizedHermitianMatrix_eq
        hB.inv.posSemidef
      have hunit : IsUnit B.det := by rw [hdetB]; exact isUnit_one
      have hpd : (normalizedHermitianMatrix β).PosDef := by rw [hHβ]; exact hB.inv
      have hdet : (normalizedHermitianMatrix β).det = 1 := by
        rw [hHβ, Matrix.det_nonsing_inv, hdetB, Ring.inverse_one]
      have h := hb ⟨β, hβ, hpd, hdet, rfl⟩
      rw [hval β hβ hpd hdet, hHβ, Matrix.nonsing_inv_nonsing_inv B hunit] at h
      rw [div_le_iff₀ hc, mul_comm]
      exact h
    have := hGLB.2 hlow
    rw [div_le_iff₀ hc, mul_comm] at this
    exact this

/-- **`det^{1/n}` of a semipositive `(1,1)`-form as an infimum** (`n = m + 1`): for a semipositive
    real `(1,1)`-form `α`, the
infimum of `topDensity (β^m ∧ α)` over the semipositive `(1,1)`-forms `β` whose coefficient matrix
    is positive definite of
determinant `1` is `(n!/πⁿ) (πⁿ/n! · topDensity(αⁿ))^{1/n}`, that is, `(n!/πⁿ) det(H_α)^{1/n}`. -/
theorem isGLB_topDensity_wedge_formPower {α : RealForm (m + 1) 2} (hα : IsSemipositiveOneOne α) :
    IsGLB {s : ℝ | ∃ β : RealForm (m + 1) 2, IsSemipositiveOneOne β ∧ (normalizedHermitianMatrix
      β).PosDef ∧
        (normalizedHermitianMatrix β).det = 1 ∧ s = topDensity (coordinateWedge (formPower β m) α)}
      (((m + 1).factorial / Real.pi ^ (m + 1) : ℝ) *
        (Real.pi ^ (m + 1) / (m + 1).factorial * actualTopPowerDensity α) ^ (((m + 1 : ℕ) : ℝ)⁻¹))
          := by
  set A := normalizedHermitianMatrix α with hAdef
  -- `det A` through the top density of `α`
  have hdetA : A.det.re = Real.pi ^ (m + 1) / (m + 1).factorial * actualTopPowerDensity α := by
    rw [actualTopPowerDensity_eq_normalizedTopPowerDensity α hα.1, normalizedTopPowerDensity,
      complexTopCoefficient_eq,
      ← hAdef, Complex.re_ofReal_mul]
    field_simp
  rw [← hdetA]
  exact isGLB_topDensity_wedge_formPower_of_posSemidef hα.1
    (normalizedHermitianMatrix_posSemidef hα)

end Forms

end SGPT.Foundations.Analysis.Pending.OneOneFormMixedTrace

end

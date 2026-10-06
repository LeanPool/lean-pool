/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.Sharp

/-!
# High-contrast homogenization: Geometry.SchurData

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur data of a positive doubled block

Every positive `2d`-by-`2d` block has a unique factorization
`H = G_{-k}^t diag(s, s_*^{-1}) G_{-k}` with `s, s_* > 0`, the triple
`(s, s_*, k)` being its Schur data (`e.annealed.schur`).  Existence and
uniqueness are read off the blocks: positivity gives `s_*^{-1} = H_{22} > 0`,
then `k = -H_{22}^{-1}H_{21}` and `s = H_{11} - H_{12}H_{22}^{-1}H_{21} > 0`.

The last clause of the canonical balance needs one more fact, also proved
here: the sharp involution acts on Schur data by `(s, s_*, k) ↦ (s_*, s, -k^t)`.
On a self-dual block this forces `s = s_*` and `k` skew, which is the canonical
factorization.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- The Schur form `G_{-k}^t diag(s, s_*^{-1}) G_{-k}` of
`e.annealed.schur`. -/
@[expose]
def schurBlock (s sStar k : Mat d) : FullBlockMat d :=
  (fullBlockShear (-k))ᴴ * Matrix.fromBlocks s 0 0 sStar⁻¹ * fullBlockShear (-k)

/-- The Schur form written out. -/
theorem schurBlock_eq (s sStar k : Mat d) :
    schurBlock s sStar k =
      Matrix.fromBlocks (s + kᴴ * sStar⁻¹ * k) (-(kᴴ * sStar⁻¹))
        (-(sStar⁻¹ * k)) sStar⁻¹ := by
  rw [schurBlock, conjTranspose_fullBlockShear, fullBlockShear,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

@[simp] theorem toBlocks₁₁_schurBlock (s sStar k : Mat d) :
    (schurBlock s sStar k).toBlocks₁₁ = s + kᴴ * sStar⁻¹ * k := by
  rw [schurBlock_eq, Matrix.toBlocks_fromBlocks₁₁]

@[simp] theorem toBlocks₂₁_schurBlock (s sStar k : Mat d) :
    (schurBlock s sStar k).toBlocks₂₁ = -(sStar⁻¹ * k) := by
  rw [schurBlock_eq, Matrix.toBlocks_fromBlocks₂₁]

@[simp] theorem toBlocks₂₂_schurBlock (s sStar k : Mat d) :
    (schurBlock s sStar k).toBlocks₂₂ = sStar⁻¹ := by
  rw [schurBlock_eq, Matrix.toBlocks_fromBlocks₂₂]

/-! ## Diagonal blocks of a positive block -/

private theorem dotProduct_mulVec_inl (H : FullBlockMat d) (x : Fin d → ℝ) :
    star (Sum.elim x 0) ⬝ᵥ H *ᵥ Sum.elim x 0 = star x ⬝ᵥ H.toBlocks₁₁ *ᵥ x := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.toBlocks₁₁,
    Finset.mul_sum]

private theorem dotProduct_mulVec_inr (H : FullBlockMat d) (x : Fin d → ℝ) :
    star (Sum.elim 0 x) ⬝ᵥ H *ᵥ Sum.elim 0 x = star x ⬝ᵥ H.toBlocks₂₂ *ᵥ x := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.toBlocks₂₂,
    Finset.mul_sum]

private theorem elim_left_ne_zero {x : Fin d → ℝ} (hx : x ≠ 0) :
    Sum.elim x (0 : Fin d → ℝ) ≠ 0 := by
  intro h
  exact hx (funext fun i => congrFun h (Sum.inl i))

private theorem elim_right_ne_zero {x : Fin d → ℝ} (hx : x ≠ 0) :
    Sum.elim (0 : Fin d → ℝ) x ≠ 0 := by
  intro h
  exact hx (funext fun i => congrFun h (Sum.inr i))

/-- The upper-left block of a positive definite doubled block is positive
definite. -/
theorem posDef_toBlocks₁₁ {H : FullBlockMat d} (hH : H.PosDef) :
    H.toBlocks₁₁.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hH.isHermitian.submatrix Sum.inl) ?_
  intro x hx
  rw [← dotProduct_mulVec_inl]
  exact hH.dotProduct_mulVec_pos (elim_left_ne_zero hx)

/-- The lower-right block of a positive definite doubled block is positive
definite. -/
theorem posDef_toBlocks₂₂ {H : FullBlockMat d} (hH : H.PosDef) :
    H.toBlocks₂₂.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hH.isHermitian.submatrix Sum.inr) ?_
  intro x hx
  rw [← dotProduct_mulVec_inr]
  exact hH.dotProduct_mulVec_pos (elim_right_ne_zero hx)

/-- The off-diagonal blocks of a Hermitian doubled block are adjoint. -/
theorem toBlocks₁₂_eq_conjTranspose {H : FullBlockMat d} (hH : H.IsHermitian) :
    H.toBlocks₁₂ = (H.toBlocks₂₁)ᴴ := by
  ext i j
  simpa [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using
    hH.apply (Sum.inr j) (Sum.inl i)

/-- Passing to the upper-left block is monotone for the Loewner order. -/
theorem toBlocks₁₁_mono {A B : FullBlockMat d} (h : A ≤ B) :
    A.toBlocks₁₁ ≤ B.toBlocks₁₁ := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hsub := hPS.submatrix (Sum.inl : Fin d → BlockCoord d)
  rw [Matrix.le_iff]
  exact hsub

/-- Passing to the lower-right block is monotone for the Loewner order.  This is
the reference text's step "taking the lower-right principal blocks". -/
theorem toBlocks₂₂_mono {A B : FullBlockMat d} (h : A ≤ B) :
    A.toBlocks₂₂ ≤ B.toBlocks₂₂ := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hsub := hPS.submatrix (Sum.inr : Fin d → BlockCoord d)
  rw [Matrix.le_iff]
  exact hsub

@[simp] theorem toBlocks₁₁_smul (c : ℝ) (A : FullBlockMat d) :
    (c • A).toBlocks₁₁ = c • A.toBlocks₁₁ := rfl

@[simp] theorem toBlocks₂₂_smul (c : ℝ) (A : FullBlockMat d) :
    (c • A).toBlocks₂₂ = c • A.toBlocks₂₂ := rfl

/-! ## Existence and uniqueness of the Schur data -/

/-- Positivity of the Schur form. -/
theorem posDef_schurBlock {s sStar k : Mat d} (hs : s.PosDef) (hstar : sStar.PosDef) :
    (schurBlock s sStar k).PosDef := by
  have hdiag : (Matrix.fromBlocks s 0 0 sStar⁻¹ : FullBlockMat d).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · have h1 : sᴴ = s := hs.isHermitian
      have h2 : (sStar⁻¹)ᴴ = sStar⁻¹ := by
        rw [Matrix.conjTranspose_nonsing_inv, hstar.isHermitian]
      rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, h1, h2]
      simp
    · intro y hy
      rw [Matrix.fromBlocks_mulVec]
      have hsplit : star y ⬝ᵥ
          Sum.elim (s *ᵥ (y ∘ Sum.inl) + (0 : Mat d) *ᵥ (y ∘ Sum.inr))
            ((0 : Mat d) *ᵥ (y ∘ Sum.inl) + sStar⁻¹ *ᵥ (y ∘ Sum.inr)) =
          star (y ∘ Sum.inl) ⬝ᵥ s *ᵥ (y ∘ Sum.inl) +
            star (y ∘ Sum.inr) ⬝ᵥ sStar⁻¹ *ᵥ (y ∘ Sum.inr) := by
        simp [dotProduct, Fintype.sum_sum_type, Function.comp]
      rw [hsplit]
      rcases eq_or_ne (y ∘ Sum.inl) 0 with hl | hl
      · have hr : y ∘ Sum.inr ≠ 0 := by
          intro hr
          exact hy (funext fun α => by cases α with
            | inl i => exact congrFun hl i
            | inr i => exact congrFun hr i)
        have h1 : star (y ∘ Sum.inl) ⬝ᵥ s *ᵥ (y ∘ Sum.inl) = 0 := by
          rw [hl]; simp
        rw [h1, zero_add]
        exact hstar.inv.dotProduct_mulVec_pos hr
      · have h2 : 0 ≤ star (y ∘ Sum.inr) ⬝ᵥ sStar⁻¹ *ᵥ (y ∘ Sum.inr) :=
          hstar.inv.posSemidef.dotProduct_mulVec_nonneg _
        have h1 : 0 < star (y ∘ Sum.inl) ⬝ᵥ s *ᵥ (y ∘ Sum.inl) :=
          hs.dotProduct_mulVec_pos hl
        linarith only [h1, h2]
  have hc := hdiag.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (isUnit_fullBlockShear (-k)))
  exact hc

/-- **Uniqueness of the Schur data** (`e.annealed.schur`). -/
theorem schurBlock_injective {s₁ t₁ k₁ s₂ t₂ k₂ : Mat d} (ht₁ : t₁.PosDef)
    (ht₂ : t₂.PosDef) (h : schurBlock s₁ t₁ k₁ = schurBlock s₂ t₂ k₂) :
    s₁ = s₂ ∧ t₁ = t₂ ∧ k₁ = k₂ := by
  have hdet₁ : IsUnit t₁.det := isUnit_det_of_posDef ht₁
  have hdet₂ : IsUnit t₂.det := isUnit_det_of_posDef ht₂
  have h22 : t₁⁻¹ = t₂⁻¹ := by
    have := congrArg Matrix.toBlocks₂₂ h
    simpa using this
  have ht : t₁ = t₂ := by
    have := congrArg (fun M : Mat d => M⁻¹) h22
    simpa [Matrix.nonsing_inv_nonsing_inv _ hdet₁, Matrix.nonsing_inv_nonsing_inv _ hdet₂]
      using this
  have hk : k₁ = k₂ := by
    have h21 := congrArg Matrix.toBlocks₂₁ h
    simp only [toBlocks₂₁_schurBlock, neg_inj] at h21
    rw [h22] at h21
    have hinvu : IsUnit (t₂⁻¹).det := isUnit_det_of_posDef ht₂.inv
    have := congrArg (fun M : Mat d => (t₂⁻¹)⁻¹ * M) h21
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hinvu] using this
  have hs : s₁ = s₂ := by
    have h11 := congrArg Matrix.toBlocks₁₁ h
    simp only [toBlocks₁₁_schurBlock] at h11
    rw [h22, hk] at h11
    exact add_right_cancel h11
  exact ⟨hs, ht, hk⟩

/-- The upper Schur block of a positive Schur form is positive definite.  The
quadratic form of `schurBlock s s_* k` at the sheared state `(x, k x)` is the
quadratic form of `s` at `x`. -/
theorem posDef_of_posDef_schurBlock {s sStar k : Mat d} (hstar : sStar.PosDef)
    (h : (schurBlock s sStar k).PosDef) : s.PosDef := by
  have hstarsymm : (sStar⁻¹)ᴴ = sStar⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hstar.isHermitian]
  have hqf : ∀ x : Fin d → ℝ,
      star (Sum.elim x (k *ᵥ x)) ⬝ᵥ (schurBlock s sStar k) *ᵥ Sum.elim x (k *ᵥ x)
        = star x ⬝ᵥ s *ᵥ x := by
    intro x
    rw [schurBlock_eq, Matrix.fromBlocks_mulVec]
    have hupper : (s + kᴴ * sStar⁻¹ * k) *ᵥ (Sum.elim x (k *ᵥ x) ∘ Sum.inl) +
        (-(kᴴ * sStar⁻¹)) *ᵥ (Sum.elim x (k *ᵥ x) ∘ Sum.inr) = s *ᵥ x := by
      have hl : (Sum.elim x (k *ᵥ x) ∘ Sum.inl) = x := rfl
      have hr : (Sum.elim x (k *ᵥ x) ∘ Sum.inr) = k *ᵥ x := rfl
      rw [hl, hr, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.add_mulVec]
      abel
    have hlower : (-(sStar⁻¹ * k)) *ᵥ (Sum.elim x (k *ᵥ x) ∘ Sum.inl) +
        sStar⁻¹ *ᵥ (Sum.elim x (k *ᵥ x) ∘ Sum.inr) = 0 := by
      have hl : (Sum.elim x (k *ᵥ x) ∘ Sum.inl) = x := rfl
      have hr : (Sum.elim x (k *ᵥ x) ∘ Sum.inr) = k *ᵥ x := rfl
      rw [hl, hr, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
      abel
    rw [hupper, hlower]
    simp [dotProduct, Fintype.sum_sum_type]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have h11 : ((schurBlock s sStar k).toBlocks₁₁)ᴴ = (schurBlock s sStar k).toBlocks₁₁ :=
      h.isHermitian.submatrix Sum.inl
    rw [toBlocks₁₁_schurBlock] at h11
    have hcorr : (kᴴ * sStar⁻¹ * k)ᴴ = kᴴ * sStar⁻¹ * k := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hstarsymm, Matrix.mul_assoc]
    rw [Matrix.conjTranspose_add, hcorr] at h11
    exact add_right_cancel h11
  · intro x hx
    rw [← hqf x]
    refine h.dotProduct_mulVec_pos ?_
    intro hc
    exact hx (funext fun i => congrFun hc (Sum.inl i))

/-- **Existence of the Schur data** (`e.annealed.schur`). -/
theorem exists_schurBlock {H : FullBlockMat d} (hH : H.PosDef) :
    ∃ s sStar k : Mat d, s.PosDef ∧ sStar.PosDef ∧ H = schurBlock s sStar k := by
  set t : Mat d := H.toBlocks₂₂ with htdef
  have ht : t.PosDef := posDef_toBlocks₂₂ hH
  have htdet : IsUnit t.det := isUnit_det_of_posDef ht
  have htsymm : tᴴ = t := ht.isHermitian
  set k : Mat d := -(t⁻¹ * H.toBlocks₂₁) with hkdef
  set s : Mat d := H.toBlocks₁₁ - H.toBlocks₁₂ * t⁻¹ * H.toBlocks₂₁ with hsdef
  have h12 : H.toBlocks₁₂ = (H.toBlocks₂₁)ᴴ := toBlocks₁₂_eq_conjTranspose hH.isHermitian
  have htinvsymm : (t⁻¹)ᴴ = t⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, htsymm]
  have hstar : (t⁻¹).PosDef := ht.inv
  have hstarinv : (t⁻¹)⁻¹ = t := Matrix.nonsing_inv_nonsing_inv _ htdet
  -- the three block identities
  have e21 : -((t⁻¹)⁻¹ * k) = H.toBlocks₂₁ := by
    rw [hstarinv, hkdef, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ htdet, Matrix.one_mul]
  have hkH : kᴴ = -(H.toBlocks₁₂ * t⁻¹) := by
    rw [hkdef, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, htinvsymm, ← h12]
  have e12 : -(kᴴ * (t⁻¹)⁻¹) = H.toBlocks₁₂ := by
    rw [hkH, hstarinv, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ htdet, Matrix.mul_one]
  have e11 : s + kᴴ * (t⁻¹)⁻¹ * k = H.toBlocks₁₁ := by
    have hprod : kᴴ * (t⁻¹)⁻¹ * k = H.toBlocks₁₂ * t⁻¹ * H.toBlocks₂₁ := by
      rw [hkH, hstarinv, hkdef]
      calc -(H.toBlocks₁₂ * t⁻¹) * t * -(t⁻¹ * H.toBlocks₂₁)
          = H.toBlocks₁₂ * (t⁻¹ * t) * (t⁻¹ * H.toBlocks₂₁) := by noncomm_ring
        _ = H.toBlocks₁₂ * t⁻¹ * H.toBlocks₂₁ := by
            rw [Matrix.nonsing_inv_mul _ htdet, Matrix.mul_one, Matrix.mul_assoc]
    rw [hprod, hsdef]
    abel
  have hform : H = schurBlock s t⁻¹ k := by
    rw [schurBlock_eq, e11, e12, e21, hstarinv, htdef]
    exact (Matrix.fromBlocks_toBlocks H).symm
  have hs : s.PosDef := posDef_of_posDef_schurBlock hstar (hform ▸ hH)
  exact ⟨s, t⁻¹, k, hs, hstar, hform⟩

/-- **The Schur data of the sharp.**  Inverting the Schur form shows that `H^♯`
has Schur data `(s_*, s, -k^t)`. -/
theorem fullBlockSharp_schurBlock {s sStar k : Mat d} (hs : s.PosDef)
    (hstar : sStar.PosDef) :
    fullBlockSharp (schurBlock s sStar k) = schurBlock sStar s (-kᴴ) := by
  have hsdet : IsUnit s.det := isUnit_det_of_posDef hs
  have hstardet : IsUnit sStar.det := isUnit_det_of_posDef hstar
  have hsinv : (s⁻¹)⁻¹ = s := Matrix.nonsing_inv_nonsing_inv _ hsdet
  have hstarinv : (sStar⁻¹)⁻¹ = sStar := Matrix.nonsing_inv_nonsing_inv _ hstardet
  have hssymm : sᴴ = s := hs.isHermitian
  have hstarsymm : (sStar⁻¹)ᴴ = sStar⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hstar.isHermitian]
  rw [schurBlock_eq, schurBlock_eq, fullBlockSharp, fullBlockRefl]
  have hinv : (Matrix.fromBlocks (s + kᴴ * sStar⁻¹ * k) (-(kᴴ * sStar⁻¹))
      (-(sStar⁻¹ * k)) (sStar⁻¹) : FullBlockMat d)⁻¹ =
      Matrix.fromBlocks s⁻¹ (s⁻¹ * kᴴ) (k * s⁻¹) (sStar + k * s⁻¹ * kᴴ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.fromBlocks_multiply]
    have h11 : (s + kᴴ * sStar⁻¹ * k) * s⁻¹ + -(kᴴ * sStar⁻¹) * (k * s⁻¹) = 1 := by
      calc (s + kᴴ * sStar⁻¹ * k) * s⁻¹ + -(kᴴ * sStar⁻¹) * (k * s⁻¹)
          = s * s⁻¹ := by noncomm_ring
        _ = 1 := Matrix.mul_nonsing_inv _ hsdet
    have h12 : (s + kᴴ * sStar⁻¹ * k) * (s⁻¹ * kᴴ) +
        -(kᴴ * sStar⁻¹) * (sStar + k * s⁻¹ * kᴴ) = 0 := by
      calc (s + kᴴ * sStar⁻¹ * k) * (s⁻¹ * kᴴ) +
            -(kᴴ * sStar⁻¹) * (sStar + k * s⁻¹ * kᴴ)
          = (s * s⁻¹) * kᴴ - kᴴ * (sStar⁻¹ * sStar) := by noncomm_ring
        _ = 0 := by
            rw [Matrix.mul_nonsing_inv _ hsdet, Matrix.nonsing_inv_mul _ hstardet,
              Matrix.one_mul, Matrix.mul_one, sub_self]
    have h21 : -(sStar⁻¹ * k) * s⁻¹ + sStar⁻¹ * (k * s⁻¹) = 0 := by noncomm_ring
    have h22 : -(sStar⁻¹ * k) * (s⁻¹ * kᴴ) + sStar⁻¹ * (sStar + k * s⁻¹ * kᴴ) = 1 := by
      calc -(sStar⁻¹ * k) * (s⁻¹ * kᴴ) + sStar⁻¹ * (sStar + k * s⁻¹ * kᴴ)
          = sStar⁻¹ * sStar := by noncomm_ring
        _ = 1 := Matrix.nonsing_inv_mul _ hstardet
    rw [h11, h12, h21, h22, Matrix.fromBlocks_one]
  have hkk : ((-kᴴ : Mat d))ᴴ = -k := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose]
  rw [hinv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, hkk,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

end

end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.SchurData
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSymmetricSkew

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The symmetric Schur skew at small diagonal contrast

The large-contrast version of the symmetric-skew estimate fails, while its
perturbative form is sufficient for the small-contrast centering estimate.
This file proves that form directly: if a
Schur block with a SYMMETRIC skew coordinate dominates its own sharp, then the
`σ*`-normalized skew is bounded by half of the normalized diagonal gap —
first order in `θ − 1`, with an absolute constant.

The proof tests the sharp ordering at the single doubled vector
`(x, t·k x)` with `t = (θ+1)/(θ−1)`: at this shift the cross terms cancel and
the quadratic gain appears with the exact constant `4/(θ−1)`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The quadratic form of a Schur block at a doubled vector. -/
private theorem schurBlock_quad (s sStar κ : Mat d) (x y : Vec d) :
    (Sum.elim x y) ⬝ᵥ (schurBlock s sStar κ) *ᵥ (Sum.elim x y) =
      x ⬝ᵥ s *ᵥ x +
        (y - κ *ᵥ x) ⬝ᵥ sStar⁻¹ *ᵥ (y - κ *ᵥ x) := by
  rw [schurBlock, Initialization.quad_conj]
  have hshear : fullBlockShear (-κ) *ᵥ Sum.elim x y =
      Sum.elim x (y - κ *ᵥ x) := by
    rw [fullBlockShear, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero, Matrix.neg_mulVec]
    congr 1
    funext i
    simp [sub_eq_neg_add]
  rw [hshear, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec,
    add_zero, zero_add]
  exact sumElim_dotProduct_sumElim _ _ _ _

/-- The scaled quadratic form. -/
private theorem quad_smul {M : Mat d} (c : ℝ) (u : Vec d) :
    (c • u) ⬝ᵥ M *ᵥ (c • u) = c ^ 2 * (u ⬝ᵥ M *ᵥ u) := by
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

/-- **The symmetric Schur skew is first order in the diagonal gap.**  If the
Schur block of `(S, S₊, k)` with symmetric `k` dominates its sharp and
`S ≤ θ·S₊`, then the `S₊⁻¹`-quadratic of `k` is bounded by `((θ−1)/2)²`
times the `S₊`-quadratic.  This is the perturbative half of the printed
display HC (2.81), proved without the refuted large-contrast half. -/
theorem symmetricSchurSkew_quad_le_of_sharp_le
    {S SStar k : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hk : kᴴ = k)
    (hsharp : fullBlockSharp (schurBlock S SStar k) ≤ schurBlock S SStar k)
    {theta : ℝ} (htheta : 1 < theta)
    (hS_le : S ≤ theta • SStar) (x : Vec d) :
    (k *ᵥ x) ⬝ᵥ SStar⁻¹ *ᵥ (k *ᵥ x) ≤
      (theta - 1) ^ 2 / 4 * (x ⬝ᵥ SStar *ᵥ x) := by
  have htheta0 : (0 : ℝ) < theta := lt_trans zero_lt_one htheta
  have hgap0 : (0 : ℝ) < theta - 1 := by linarith only [htheta]
  have hne : theta - 1 ≠ 0 := ne_of_gt hgap0
  set t : ℝ := (theta + 1) / (theta - 1) with ht
  set u : Vec d := k *ᵥ x with hu
  set y : Vec d := t • u with hy
  set Q : ℝ := u ⬝ᵥ SStar⁻¹ *ᵥ u with hQ
  set A : ℝ := x ⬝ᵥ SStar *ᵥ x with hA
  -- the sharp is the reversed Schur block
  rw [fullBlockSharp_schurBlock hS hStar] at hsharp
  -- the tested order
  have hquad := Initialization.dotProduct_mulVec_le_of_le hsharp (Sum.elim x y)
  rw [schurBlock_quad SStar S (-kᴴ) x y, schurBlock_quad S SStar k x y]
    at hquad
  -- the two shifted vectors are multiples of `k x`
  have hyplus : y - (-kᴴ) *ᵥ x = (t + 1) • u := by
    rw [hy, hu, hk, Matrix.neg_mulVec, sub_neg_eq_add, add_smul, one_smul]
  have hyminus : y - k *ᵥ x = (t - 1) • u := by
    rw [hy, hu, sub_smul, one_smul]
  rw [hyplus, hyminus, quad_smul, quad_smul] at hquad
  -- the inverse order `θ⁻¹ S₊⁻¹ ≤ S⁻¹`
  have hsmulPos : (theta • SStar).PosDef := hStar.smul htheta0
  have hinv : (theta • SStar)⁻¹ ≤ S⁻¹ :=
    HCPolySupport.HighContrast.inv_le_inv_of_le hS hsmulPos hS_le
  have hsmulInv : (theta • SStar)⁻¹ = theta⁻¹ • SStar⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt htheta0),
      Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar), one_smul]
  rw [hsmulInv] at hinv
  have hSinvQ : theta⁻¹ * Q ≤ u ⬝ᵥ S⁻¹ *ᵥ u := by
    have h := Initialization.dotProduct_mulVec_le_of_le hinv u
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    exact h
  -- the diagonal gap
  have hSx : x ⬝ᵥ S *ᵥ x ≤ theta * A := by
    have h := Initialization.dotProduct_mulVec_le_of_le hS_le x
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    exact h
  -- assemble the scalar inequality
  have hQ0 : 0 ≤ Q := by
    have := (hStar.inv.posSemidef).dotProduct_mulVec_nonneg u
    simpa using this
  have hchain :
      A + (t + 1) ^ 2 * (theta⁻¹ * Q) ≤ theta * A + (t - 1) ^ 2 * Q := by
    have hmul : (t + 1) ^ 2 * (theta⁻¹ * Q) ≤
        (t + 1) ^ 2 * (u ⬝ᵥ S⁻¹ *ᵥ u) :=
      mul_le_mul_of_nonneg_left hSinvQ (by positivity)
    calc
      A + (t + 1) ^ 2 * (theta⁻¹ * Q) ≤
          A + (t + 1) ^ 2 * (u ⬝ᵥ S⁻¹ *ᵥ u) := by
        linarith only [hmul]
      _ ≤ x ⬝ᵥ S *ᵥ x + (t - 1) ^ 2 * Q := hquad
      _ ≤ theta * A + (t - 1) ^ 2 * Q := by
        linarith only [hSx]
  -- the exact coefficients at the optimal shift
  have htplus : t + 1 = 2 * theta / (theta - 1) := by
    rw [ht]
    field_simp
    ring
  have htminus : t - 1 = 2 / (theta - 1) := by
    rw [ht]
    field_simp
    ring
  have hcoeff :
      (t + 1) ^ 2 * theta⁻¹ - (t - 1) ^ 2 = 4 / (theta - 1) := by
    rw [htplus, htminus]
    field_simp
    ring
  have hfour : 4 / (theta - 1) * Q ≤ (theta - 1) * A := by
    nlinarith only [hchain, hcoeff, hQ0]
  have hscale : 0 < (theta - 1) / 4 := by positivity
  calc
    Q = (theta - 1) / 4 * (4 / (theta - 1) * Q) := by
      field_simp
    _ ≤ (theta - 1) / 4 * ((theta - 1) * A) :=
      mul_le_mul_of_nonneg_left hfour hscale.le
    _ = (theta - 1) ^ 2 / 4 * A := by ring

/-- Matrix-order form of the symmetric-skew bound. -/
theorem symmetricSchurSkew_conj_le_of_sharp_le
    {S SStar k : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hk : kᴴ = k)
    (hsharp : fullBlockSharp (schurBlock S SStar k) ≤ schurBlock S SStar k)
    {theta : ℝ} (htheta : 1 < theta)
    (hS_le : S ≤ theta • SStar) :
    kᴴ * SStar⁻¹ * k ≤ ((theta - 1) ^ 2 / 4) • SStar := by
  have hherm : (kᴴ * SStar⁻¹ * k).IsHermitian := by
    change (kᴴ * SStar⁻¹ * k)ᴴ = kᴴ * SStar⁻¹ * k
    calc
      (kᴴ * SStar⁻¹ * k)ᴴ = kᴴ * (SStar⁻¹)ᴴ * (kᴴ)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.mul_assoc]
      _ = kᴴ * SStar⁻¹ * k := by
        rw [hStar.inv.isHermitian.eq, Matrix.conjTranspose_conjTranspose]
  have hhermR : (((theta - 1) ^ 2 / 4) • SStar).IsHermitian := by
    change (((theta - 1) ^ 2 / 4) • SStar)ᴴ = ((theta - 1) ^ 2 / 4) • SStar
    rw [Matrix.conjTranspose_smul, star_trivial, hStar.isHermitian.eq]
  refine Initialization.le_of_dotProduct_mulVec_le hherm hhermR fun x => ?_
  have h := symmetricSchurSkew_quad_le_of_sharp_le hS hStar hk hsharp
    htheta hS_le x
  rw [Initialization.quad_conj k SStar⁻¹ x, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  exact h

end

end HCPolySupport.HighContrast.Quenched

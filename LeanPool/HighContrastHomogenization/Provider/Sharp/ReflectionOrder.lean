/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge

/-!
# High-contrast homogenization: Provider.Sharp.ReflectionOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp order and the two signed reflection bounds

The primal-adjoint involution of `s.scale.selection` sends a doubled block `H`
to `H^♯ = R H^{-1} R`, the reflection being `R = (0 I; I 0)`, and the pathwise
elementary block bounds assert `H^♯ ≤ H`.  This file isolates the
linear algebra of that assertion: on a symmetric positive definite block the
sharp order is *equivalent* to the pair of signed reflection bounds `-R ≤ H` and
`R ≤ H`, that is, to the single scalar statement that half the doubled quadratic
form of `H` dominates the absolute pairing `|P₁ · P₂|` of the two halves of a
doubled vector.

Both directions are elementary and use no spectral theory.  The quadratic form of
`R` at `(P₁, P₂)` is `2 P₁·P₂`, so the two signed bounds polarize to
`2 (u₁·v₂ + u₂·v₁) ≤ u·Hu + v·Hv`; fed the pair `u = X`, `v = H^{-1} R X`, that
inequality gives the sharp order at `X`, because the mixed pairing and the second
quadratic term are then both equal to `(RX)·H^{-1}(RX)`.  Conversely the Young
inequality `2 u·v ≤ u·Hu + v·H^{-1}v`, itself the expansion of
`(u - H^{-1}v)·H(u - H^{-1}v) ≥ 0`, evaluated at `v = ±RX` returns the two signed
bounds.

The direction that produces the sharp order needs no invertibility: where the
flattened block is singular the sharp is the zero block, and the two signed
bounds already force the quadratic form of `H` to be nonnegative.
-/

namespace HCPolySupport
namespace HighContrast
namespace Sharp

noncomputable section

variable {d : ℕ}

/-! ## The reflection and the dilation as quadratic forms -/

/-- The doubled quadratic form of a dilation is the dilated quadratic form. -/
theorem blockVecDot_blockMatVecMul_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  have hmul : blockMatVecMul (blockScale c A) X = c • blockMatVecMul A X := by
    refine Prod.ext ?_ ?_ <;>
      simp [blockScale, blockMatVecMul, smul_matVecMul, smul_add]
  rw [hmul, blockVecDot_smul_right]

/-- In dimension zero every doubled quadratic form vanishes, so the block Loewner
order holds between any two blocks. -/
theorem blockMatLoewnerLE_of_dim_zero (A B : BlockMat 0) : BlockMatLoewnerLE A B := by
  intro X
  simp [blockVecDot, vecDot]

/-! ## The structural inverse -/

/-- The structural inverse is a right inverse where the flattened block is
invertible. -/
theorem blockMatMul_blockMatInv {H : BlockMat d} (hdet : IsUnit (toFullBlockMat H).det) :
    Book.Ch02.blockMatMul H (Book.Ch02.blockMatInv H) = Book.Ch02.blockIdentity d := by
  refine toFullBlockMat_injective ?_
  rw [toFullBlockMat_blockMatMul, toFullBlockMat_blockMatInv, toFullBlockMat_blockIdentity]
  exact Matrix.mul_nonsing_inv _ hdet

/-- The structural inverse is a right inverse of the doubled action. -/
theorem blockMatVecMul_blockMatInv {H : BlockMat d} (hdet : IsUnit (toFullBlockMat H).det)
    (Y : BlockVec d) :
    blockMatVecMul H (blockMatVecMul (Book.Ch02.blockMatInv H) Y) = Y := by
  rw [← blockMatVecMul_blockMatMul, blockMatMul_blockMatInv hdet, blockMatVecMul_blockIdentity]

/-- The sharp quadratic form is the inverse quadratic form at the swapped
vector. -/
theorem blockVecDot_blockMatVecMul_blockSharp (H : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockSharp H) X) =
      blockVecDot (X.2, X.1) (blockMatVecMul (Book.Ch02.blockMatInv H) (X.2, X.1)) := by
  rw [blockSharp, blockVecDot_blockMatVecMul_blockReflect]

/-! ## Polarization of the signed bounds -/

/-- The two signed reflection bounds polarize: the mixed pairing of two doubled
vectors is dominated by the sum of their quadratic forms. -/
theorem two_mul_blockVecDot_swap_le {H : BlockMat d} (hsymm : IsSymmetricBlockMat H)
    (hplus : ∀ X : BlockVec d,
      vecDot X.1 X.2 ≤ 1 / 2 * blockVecDot X (blockMatVecMul H X))
    (hminus : ∀ X : BlockVec d,
      -vecDot X.1 X.2 ≤ 1 / 2 * blockVecDot X (blockMatVecMul H X))
    (u v : BlockVec d) :
    2 * blockVecDot (u.2, u.1) v ≤
      blockVecDot u (blockMatVecMul H u) + blockVecDot v (blockMatVecMul H v) := by
  have hcross := blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hsymm u v
  have hsum : blockVecDot (u + v) (blockMatVecMul H (u + v)) =
      blockVecDot u (blockMatVecMul H u) + 2 * blockVecDot u (blockMatVecMul H v) +
        blockVecDot v (blockMatVecMul H v) := by
    rw [blockMatVecMul_add, blockVecDot_add_left, blockVecDot_add_right,
      blockVecDot_add_right, hcross]
    ring
  have hdif : blockVecDot (u + (-1 : ℝ) • v) (blockMatVecMul H (u + (-1 : ℝ) • v)) =
      blockVecDot u (blockMatVecMul H u) - 2 * blockVecDot u (blockMatVecMul H v) +
        blockVecDot v (blockMatVecMul H v) := by
    rw [blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left, blockVecDot_add_right,
      blockVecDot_add_right, blockVecDot_smul_right, blockVecDot_smul_left,
      blockVecDot_smul_left, blockVecDot_smul_right, hcross]
    ring
  have hpsum : (u + v).1 = u.1 + v.1 := rfl
  have hqsum : (u + v).2 = u.2 + v.2 := rfl
  have hpdif : (u + (-1 : ℝ) • v).1 = u.1 + (-1 : ℝ) • v.1 := rfl
  have hqdif : (u + (-1 : ℝ) • v).2 = u.2 + (-1 : ℝ) • v.2 := rfl
  have hpair : blockVecDot (u.2, u.1) v = vecDot u.2 v.1 + vecDot u.1 v.2 := rfl
  have h1 := hplus (u + v)
  have h2 := hminus (u + (-1 : ℝ) • v)
  rw [hpsum, hqsum, hsum] at h1
  rw [hpdif, hqdif, hdif] at h2
  simp only [vecDot_add_left, vecDot_add_right, vecDot_smul_left, vecDot_smul_right] at h1 h2
  rw [hpair, vecDot_comm u.2 v.1]
  linarith only [h1, h2]

/-! ## The sharp order from the signed bounds -/

/-- **The signed reflection bounds give the sharp order**: this is the linear
algebra behind the elementary block bounds.  No invertibility is assumed. -/
theorem blockMatLoewnerLE_blockSharp_of_signed {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H)
    (hplus : ∀ X : BlockVec d,
      vecDot X.1 X.2 ≤ 1 / 2 * blockVecDot X (blockMatVecMul H X))
    (hminus : ∀ X : BlockVec d,
      -vecDot X.1 X.2 ≤ 1 / 2 * blockVecDot X (blockMatVecMul H X)) :
    BlockMatLoewnerLE (blockSharp H) H := by
  intro X
  change 1 / 2 * blockVecDot X (blockMatVecMul (blockSharp H) X) ≤
    1 / 2 * blockVecDot X (blockMatVecMul H X)
  by_cases hdet : IsUnit (toFullBlockMat H).det
  · have hHW := blockMatVecMul_blockMatInv hdet ((X.2, X.1) : BlockVec d)
    have hquad : blockVecDot (blockMatVecMul (Book.Ch02.blockMatInv H) (X.2, X.1))
          (blockMatVecMul H (blockMatVecMul (Book.Ch02.blockMatInv H) (X.2, X.1))) =
        blockVecDot (X.2, X.1) (blockMatVecMul (Book.Ch02.blockMatInv H) (X.2, X.1)) := by
      rw [hHW, blockVecDot_comm]
    have hpol := two_mul_blockVecDot_swap_le hsymm hplus hminus X
      (blockMatVecMul (Book.Ch02.blockMatInv H) (X.2, X.1))
    rw [hquad] at hpol
    rw [blockVecDot_blockMatVecMul_blockSharp]
    linarith only [hpol]
  · have hzero : blockVecDot X (blockMatVecMul (blockSharp H) X) = 0 := by
      rw [blockVecDot_blockMatVecMul_eq_dotProduct, toFullBlockMat_blockSharp, fullBlockSharp,
        Matrix.nonsing_inv_apply_not_isUnit _ hdet]
      simp
    rw [hzero]
    linarith only [hplus X, hminus X]

/-! ## The signed bounds from the sharp order -/

/-- A positive definite doubled block has a nonnegative doubled quadratic form. -/
theorem zero_le_blockVecDot_blockMatVecMul_of_blockPosDef {H : BlockMat d}
    (hpd : Book.Ch02.BlockPosDef H) (Z : BlockVec d) :
    0 ≤ blockVecDot Z (blockMatVecMul H Z) := by
  by_cases hz : Z = 0
  · have h0 : blockMatVecMul H (0 : BlockVec d) = 0 := by
      refine Prod.ext ?_ ?_ <;> simp [blockMatVecMul, matVecMul_zero]
    rw [hz, h0]
    simp [blockVecDot, vecDot_zero_left]
  · exact (hpd Z hz).le

end

end Sharp
end HighContrast
end HCPolySupport

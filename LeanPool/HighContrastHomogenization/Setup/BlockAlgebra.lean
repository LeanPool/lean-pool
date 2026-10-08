/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.BlockMatrix
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# High-contrast homogenization: Setup.BlockAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Doubled block algebra: Schur data, contrasts, and matrix square roots

This file fixes the algebraic objects the reference text builds on a doubled
block matrix: the Schur parametrization of `e.annealed.schur`, the
scalar Loewner bound encoding the matrix norm `|·|`, the intrinsic contrast of
the reference block, the reference aspect ratio of `e.reference.aspect.ratio`,
and the positive semidefinite square root.
-/

namespace HCPolySupport
namespace HighContrast

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- Scalar dilation of a doubled block matrix. -/
@[expose]
def blockScale (c : ℝ) (A : BlockMat d) : BlockMat d :=
  { upperLeft := c • A.upperLeft
    upperRight := c • A.upperRight
    lowerLeft := c • A.lowerLeft
    lowerRight := c • A.lowerRight }

/-- A skew-symmetric `d × d` matrix. -/
@[expose]
def IsSkewMat (h : Mat d) : Prop :=
  matTranspose h = -h

/-- The scalar Loewner bound `inf { t ≥ 0 : M ≤ t · I }`; on symmetric positive
semidefinite arguments this is the spectral norm `|M|`. -/
@[expose]
def specBound (M : Mat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))}

/-- The Schur `σ_*` block of a doubled block matrix in the parametrization
`e.annealed.schur`: the lower-right block is `σ_*⁻¹`. -/
@[expose]
def schurSigmaStar (H : BlockMat d) : Mat d :=
  H.lowerRight⁻¹

/-- The Schur skew block `k` of a doubled block matrix: the lower-left block is
`-σ_*⁻¹ k`. -/
@[expose]
def schurSkew (H : BlockMat d) : Mat d :=
  -(H.lowerRight⁻¹ * H.lowerLeft)

/-- The Schur symmetric block `σ` of a doubled block matrix: the upper-left
block is `σ + kᵗ σ_*⁻¹ k`. -/
@[expose]
def schurSigma (H : BlockMat d) : Mat d :=
  H.upperLeft - matTranspose (schurSkew H) * H.lowerRight * schurSkew H

/-- The intrinsic contrast of a doubled block matrix, in the Loewner-scaling
form: `inf` of the `t ≥ 0` for which some skew `h` gives
`σ + (k - h)ᵗ σ_*⁻¹ (k - h) ≤ t σ_*`.  On Schur-form positive blocks this is
the paper's `min_h |σ_*^{-1/2}(σ + (k-h)ᵗ σ_*⁻¹ (k-h)) σ_*^{-1/2}|`
(the intrinsic contrast of the reference block, `e.Theta.m`). -/
@[expose]
def blockContrast (H : BlockMat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
    MatLoewnerLE
      (schurSigma H +
        matTranspose (schurSkew H - h) * H.lowerRight * (schurSkew H - h))
      (t • schurSigmaStar H)}

/-- `λ_0` of the reference block (`e.reference.aspect.ratio`): `|σ_{*,0}^{-1}|⁻¹`,
where `σ_{*,0}^{-1}` is the lower-right block. -/
@[expose]
def lambdaRef (E : BlockMat d) : ℝ :=
  (specBound E.lowerRight)⁻¹

/-- `Λ_0` of the reference block (`e.reference.aspect.ratio`):
`min_h |σ_0 + (k_0 - h)ᵗ σ_{*,0}^{-1} (k_0 - h)|` in Loewner-scaling form. -/
@[expose]
def bigLambdaRef (E : BlockMat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
    MatLoewnerLE
      (schurSigma E +
        matTranspose (schurSkew E - h) * E.lowerRight * (schurSkew E - h))
      (t • (1 : Mat d))}

/-- The reference aspect ratio `Π := Λ_0 / λ_0` (`e.reference.aspect.ratio`). -/
@[expose]
def aspectRatio (E : BlockMat d) : ℝ :=
  bigLambdaRef E / lambdaRef E

/-- The reference intrinsic contrast `Θ` (the intrinsic contrast of the reference block). -/
@[expose]
def refContrast (E : BlockMat d) : ℝ :=
  blockContrast E

/-- The positive-semidefinite square root, by canonical choice of the unique
positive-semidefinite `B` with `B * B = M`; junk value `1` otherwise. -/
@[expose]
def matSqrt {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Matrix n n ℝ :=
  if h : ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = M then h.choose else 1

/-! ## Entrywise bookkeeping -/

/-- Entries of a scalar dilation of a doubled block matrix. -/
theorem blockMatEntry_blockScale (c : ℝ) (A : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (blockScale c A) α β = c * blockMatEntry A α β := by
  cases α <;> cases β <;> rfl

/-- The sum of the absolute values of the entries of a doubled block matrix; a
crude but uniform entrywise scale. -/
@[expose]
def blockEntrySum (A : BlockMat d) : ℝ :=
  ∑ α : BlockCoord d, ∑ β : BlockCoord d, |blockMatEntry A α β|

theorem blockEntrySum_nonneg (A : BlockMat d) : 0 ≤ blockEntrySum A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_blockMatEntry_le_blockEntrySum (A : BlockMat d) (α β : BlockCoord d) :
    |blockMatEntry A α β| ≤ blockEntrySum A := by
  refine le_trans ?_
    (Finset.single_le_sum (f := fun γ : BlockCoord d =>
      ∑ δ : BlockCoord d, |blockMatEntry A γ δ|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ α))
  exact Finset.single_le_sum
    (f := fun δ : BlockCoord d => |blockMatEntry A α δ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ β)

theorem blockEntrySum_blockScale {c : ℝ} (hc : 0 ≤ c) (A : BlockMat d) :
    blockEntrySum (blockScale c A) = c * blockEntrySum A := by
  simp only [blockEntrySum, blockMatEntry_blockScale, abs_mul, abs_of_nonneg hc,
    Finset.mul_sum]

/-- Two-sided entrywise control of a symmetric doubled block matrix whose
quadratic form is nonnegative on the diagonal and on the sums of two basis
vectors, and is there dominated by that of a reference block. -/
theorem abs_blockMatEntry_le_of_bounds {A F : BlockMat d}
    (hsymm : IsSymmetricBlockMat A)
    (hdiag0 : ∀ γ : BlockCoord d, 0 ≤ blockMatEntry A γ γ)
    (hdiagF : ∀ γ : BlockCoord d, blockMatEntry A γ γ ≤ blockMatEntry F γ γ)
    {α β : BlockCoord d}
    (hsum0 : 0 ≤ blockVecDot (blockBasis α + blockBasis β)
      (blockMatVecMul A (blockBasis α + blockBasis β)))
    (hsumF : blockVecDot (blockBasis α + blockBasis β)
        (blockMatVecMul A (blockBasis α + blockBasis β)) ≤
      blockVecDot (blockBasis α + blockBasis β)
        (blockMatVecMul F (blockBasis α + blockBasis β))) :
    |blockMatEntry A α β| ≤ 2 * blockEntrySum F := by
  have hCF := blockEntrySum_nonneg F
  have hFbound : ∀ γ δ : BlockCoord d, blockMatEntry F γ δ ≤ blockEntrySum F :=
    fun γ δ => le_trans (le_abs_self _) (abs_blockMatEntry_le_blockEntrySum F γ δ)
  have hAsymm : blockMatEntry A β α = blockMatEntry A α β := hsymm β α
  rw [blockBasis_sum_pairing, hAsymm] at hsum0 hsumF
  rw [blockBasis_sum_pairing] at hsumF
  have hup : blockMatEntry A α β ≤ 2 * blockEntrySum F := by
    linarith only [hsumF, hdiag0 α, hdiag0 β, hFbound α α, hFbound α β,
      hFbound β α, hFbound β β]
  have hlow : -(2 * blockEntrySum F) ≤ blockMatEntry A α β := by
    linarith only [hsum0, hdiagF α, hdiagF β, hFbound α α, hFbound β β, hCF]
  exact abs_le.2 ⟨hlow, hup⟩

/-- The doubled quadratic form, expanded over the flattened basis. -/
theorem toFullBlockMat_eq_blockMatEntry (A : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat A α β = blockMatEntry A α β := by
  cases α <;> cases β <;> rfl

theorem blockVecDot_blockMatVecMul_eq_sum (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec X α * (blockMatEntry A α β * toFullBlockVec X β) := by
  rw [← dotProduct_toFullBlockVec X (blockMatVecMul A X), toFullBlockVec_blockMatVecMul]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, toFullBlockMat_eq_blockMatEntry]

/-- The doubled quadratic form on the flux slot is the quadratic form of the
lower-right block. -/
theorem blockVecDot_inr (H : BlockMat d) (x : Vec d) :
    blockVecDot ((0 : Vec d), x) (blockMatVecMul H ((0 : Vec d), x)) =
      vecDot x (matVecMul H.lowerRight x) := by
  simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]

end

end HighContrast
end HCPolySupport

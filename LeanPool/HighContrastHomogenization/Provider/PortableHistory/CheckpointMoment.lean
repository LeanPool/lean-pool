/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize

/-!
# High-contrast homogenization: Provider.PortableHistory.CheckpointMoment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centered moment at the checkpoint

The startup estimate of `p.fixed.geometry.one.grid.propagation` needs one comparison between
the two ways a centered response is measured: the Schatten size `v_b^q`, which
is a mixed norm of `(E_b^q)^{-1/2}(A_b^q(0) - E_b^q)(E_b^q)^{-1/2}`, and the
scalar size, which is what the centered history `𝓗_q^{cen}(b)` accumulates.  The
printed step is

`(v_b^q)^Q ≤ 2d 𝓗_q^{cen}(b)`,

"at scale `b` the operator norm is among the terms defining `𝓗_q^{cen}(b)`".

Two facts produce it.  First, the scalar size is the spectral norm of the
normalized block.  Its norm sandwich and the spectral Schatten estimate then
bound the Schatten size by `(2d)^{1/Q}` times the scalar size.  Second, the term
of the supremum defining `𝓗_q^{cen}(b)` at the scale `j = b` and the lattice
index `w = 0` is exactly the scalar size of the centered response of the cell
`⋄_b^q`, with geometric weight `3^0 = 1`, and its center — the origin — lies in
`⋄_b^q`.
-/

namespace HCPolySupport
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The scalar size against the Schatten size -/

/-- The scalar size of a symmetric block against a positive block is
nonnegative. -/
theorem zero_le_blockSize {X F : BlockMat d} (hX : IsSymmetricBlockMat X)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) :
    0 ≤ blockSize X F :=
  blockSize_nonneg hX hF hFpd

/-- **The Schatten size costs at most `(2d)^{1/Q}` against the scalar size.**
The scalar size is the spectral norm of the normalized block, whose norm
sandwich bounds its Schatten size by the dimensional factor. -/
theorem schattenSize_le_blockSize [NeZero d] {X F : BlockMat d} (hX : IsSymmetricBlockMat X)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {Q : ℝ} (hQ : 0 < Q) :
    schattenSize Q X F ≤ (2 * d : ℝ) ^ Q⁻¹ * blockSize X F := by
  rw [blockSize_eq_norm hX hF hFpd]
  have hNsym : IsSymmetricBlockMat (normalizedBlock X F) :=
    isSymmetricBlockMat_normalizedBlock hX
  have hNherm : (toFullBlockMat (normalizedBlock X F))ᴴ =
      toFullBlockMat (normalizedBlock X F) := by
    rw [conjTranspose_eq_transpose']
    exact isSymm_toFullBlockMat hNsym
  obtain ⟨hup, hlo⟩ := sandwich_of_norm_le hNherm le_rfl
  refine Recurrence.schattenNorm_le_of_posSemidef hNsym hQ (norm_nonneg _)
    (Matrix.le_iff.mp hup) ?_
  have h := Matrix.le_iff.mp hlo
  rwa [neg_smul, sub_neg_eq_add, add_comm] at h

/-! ## The checkpoint term of the centered history -/

/-- The aligned adapted cell at the zero lattice index is the centered adapted
cell. -/
theorem adaptedCellAt_zero (q : Mat d) (k : ℤ) : adaptedCellAt q k 0 = adaptedCell q k := by
  rw [Recurrence.adaptedCellAt_eq_image, standardCell_zero]
  rfl

/-- The centered response of the cell `⋄_b^q` is one of the terms of the
supremum defining `𝓗_q^{cen}(b)`. -/
theorem ofReal_blockSize_le_centeredSup {P : Measure (CoeffSpace d)} {q : Mat d}
    (hq : q.PosDef) {rhoMax : ℝ} {jStar b : ℤ} (hb : jStar ≤ b) (a : CoeffSpace d) :
    ENNReal.ofReal (blockSize (blockSub (coarseBlock (adaptedCell q b) a) (adaptedMean P q b))
        (adaptedMean P q b)) ≤
      ⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w a) (adaptedMean P q j))
            (adaptedMean P q b)) := by
  have hmem : adaptedCellCenter q b (0 : Fin d → ℤ) ∈ adaptedCell q b := by
    rw [Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq (le_refl b)]
    intro i
    simp
  refine le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le (le_refl b)
    (le_iSup_of_le 0 (le_iSup_of_le hmem (le_of_eq ?_)))))
  have hweight : (3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (b : ℝ))) = 1 := by
    rw [show -rhoMax * ((b : ℝ) - (b : ℝ)) = 0 by ring, Real.rpow_zero]
  rw [hweight, one_mul, adaptedResponse, adaptedCellAt_zero]

/-! ## The checkpoint display -/

end

end PortableHistory
end HighContrast
end HCPolySupport

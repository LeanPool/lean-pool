/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.PositiveGapClosure
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization: Provider.Transport.CellDomination

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Domination of an adapted response by a reference block

The well-definedness paragraph of `p.two.grid.transport` reads one
pathwise inequality — the coarse response of an adapted cell lies below a
multiple of the reference block `𝐄` — and extracts from it everything the
printed quantities need in order to denote.  Two extractions are needed, and
both are recorded here in the generality in which the transport uses them, with
no probability in sight.

The first is entrywise: a symmetric doubled block whose quadratic form is caught
between zero and that of `c𝐄` has all its entries bounded by `2|c|` times the
entry scale of `𝐄`.  That is what makes the annealed block an expectation.

The second is the centered Schatten size at the block's own normalization.
Writing `G_hat = E^{-1/2}𝐀E^{-1/2}` for the normalized response, the centered
normalization is `G_hat - I`; it is above `-I` for free, since `G_hat` is positive
semidefinite, and it is below `tI` as soon as `tr G_hat ≤ t`, a positive
semidefinite matrix being below its own trace.  The scalar Loewner sandwich
`-(1+|t|)I ≤ G_hat - I ≤ (1+|t|)I` then gives the Schatten size directly.  The
trace hypothesis is in turn a consequence of the same Loewner bound, the
congruence by `E^{-1/2}` being order preserving and the trace monotone.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The entrywise bound -/

private theorem blockEntrySum_blockScale_abs (c : ℝ) (A : BlockMat d) :
    blockEntrySum (blockScale c A) = |c| * blockEntrySum A := by
  simp only [blockEntrySum, blockMatEntry_blockScale, abs_mul, Finset.mul_sum]

/-- **The entrywise bound on a dominated coarse response.**  A coarse response
below `c𝐄` in the Loewner order has every entry bounded by `2|c|` times the
entry scale of the reference block; the lower bound comes from the response's
own positivity, which needs no hypothesis. -/
theorem abs_blockMatEntry_coarseBlock_le_of_blockMatLoewnerLE {U : Set (Vec d)}
    {a : CoeffSpace d} {c : ℝ} {E : BlockMat d}
    (hle : BlockMatLoewnerLE (coarseBlock U a) (blockScale c E))
    (α β : BlockCoord d) :
    |blockMatEntry (coarseBlock U a) α β| ≤ 2 * (|c| * blockEntrySum E) := by
  have hsymm : IsSymmetricBlockMat (coarseBlock U a) := by
    rw [coarseBlock]
    exact isSymmetricBlockMat_coarseBlockMatrix _ _
  have hentry := abs_blockMatEntry_le_of_bounds (F := blockScale c E) hsymm
    (zero_le_blockMatEntry_coarseBlock_diag _ a)
    (fun γ => by
      have h := hle (blockBasis γ)
      rw [blockBasis_pairing, blockBasis_pairing] at h
      linarith only [h])
    (zero_le_blockVecDot_coarseBlock_blockBasis_add _ a α β)
    (by linarith only [hle (blockBasis α + blockBasis β)])
  rwa [blockEntrySum_blockScale_abs] at hentry

/-! ## The centered Schatten size -/

private theorem smul_one_le_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {s t : ℝ} (h : s ≤ t) :
    s • (1 : Matrix n n ℝ) ≤ t • (1 : Matrix n n ℝ) := by
  refine Matrix.le_iff.mpr ?_
  rw [← sub_smul]
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by linarith only [h])

/-- **The trace of a normalized block is monotone in the block.**  The
congruence by `E^{-1/2}` preserves the Loewner order and the trace is monotone,
so a Loewner bound `𝐀 ≤ c𝐄` becomes the scalar bound
`tr(E^{-1/2}𝐀E^{-1/2}) ≤ c·tr(E^{-1/2}𝐄E^{-1/2})`. -/
theorem trace_toFullBlockMat_normalizedBlock_le {A Em Eref : BlockMat d}
    (hEmpd : (toFullBlockMat Em).PosDef) {c : ℝ}
    (hle : toFullBlockMat A ≤ c • toFullBlockMat Eref) :
    Matrix.trace (toFullBlockMat (normalizedBlock A Em)) ≤
      c * Matrix.trace (toFullBlockMat (normalizedBlock Eref Em)) := by
  have hSsym : (matSqrt (toFullBlockMat Em)⁻¹)ᴴ = matSqrt (toFullBlockMat Em)⁻¹ := by
    rw [conjTranspose_eq_transpose', transpose_matSqrt_inv hEmpd]
  have hconj := conj_le_conj' hSsym hle
  rw [Matrix.mul_smul, Matrix.smul_mul] at hconj
  have hnn := (Matrix.le_iff.mp hconj).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    ← Recurrence.toFullBlockMat_normalizedBlock, ← Recurrence.toFullBlockMat_normalizedBlock] at hnn
  linarith only [hnn]

/-- **The centered Schatten size from a trace bound.**  The normalized response
`G_hat = E^{-1/2}𝐀E^{-1/2}` is positive semidefinite, hence below `(tr G_hat)I`; if its
trace is at most `t`, the centered normalization `G_hat - I` is caught between
`∓(1+|t|)I`, and the Schatten size of a block in such a sandwich is at most
`(2d)^{1/Q}` times the width. -/
theorem schattenSize_blockSub_le_of_trace_le {Q : ℝ} (hQ : 0 < Q) {A Em : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hApsd : (toFullBlockMat A).PosSemidef)
    (hEm : IsSymmetricBlockMat Em) (hEmpd : (toFullBlockMat Em).PosDef) {t : ℝ}
    (ht : Matrix.trace (toFullBlockMat (normalizedBlock A Em)) ≤ t) :
    schattenSize Q (blockSub A Em) Em ≤ (2 * d : ℝ) ^ Q⁻¹ * (1 + |t|) := by
  set F : FullBlockMat d := toFullBlockMat Em with hF
  set S : FullBlockMat d := matSqrt F⁻¹ with hS
  set G : FullBlockMat d := S * toFullBlockMat A * S with hG
  have hSsym : Sᴴ = S := by
    rw [conjTranspose_eq_transpose', hS, transpose_matSqrt_inv hEmpd]
  have hGpsd : G.PosSemidef := by
    have h := hApsd.conjTranspose_mul_mul_same S
    rwa [hSsym] at h
  have hGeq : toFullBlockMat (normalizedBlock A Em) = G := by
    rw [Recurrence.toFullBlockMat_normalizedBlock, ← hF, ← hS, ← hG]
  have hHeq : toFullBlockMat (normalizedBlock (blockSub A Em) Em) = G - 1 := by
    rw [Recurrence.toFullBlockMat_normalizedBlock_blockSub, ← hF, ← hS, ← hG,
      matSqrt_inv_conj hEmpd]
  have hGle : G ≤ t • (1 : FullBlockMat d) :=
    le_trans (Recurrence.le_trace_smul_one hGpsd)
      (smul_one_le_smul_one (by rw [hGeq] at ht; exact ht))
  set w : ℝ := 1 + |t| with hw
  clear_value w
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have habs : t ≤ |t| := le_abs_self t
  have hsub : (w • (1 : FullBlockMat d) -
      toFullBlockMat (normalizedBlock (blockSub A Em) Em)).PosSemidef := by
    rw [hHeq]
    have hrw : w • (1 : FullBlockMat d) - (G - 1) = (w + 1) • (1 : FullBlockMat d) - G := by
      rw [add_smul, one_smul]
      abel
    rw [hrw]
    exact Matrix.le_iff.mp
      (le_trans hGle (smul_one_le_smul_one (by rw [hw]; linarith only [habs])))
  have hadd : (w • (1 : FullBlockMat d) +
      toFullBlockMat (normalizedBlock (blockSub A Em) Em)).PosSemidef := by
    rw [hHeq]
    have hrw : w • (1 : FullBlockMat d) + (G - 1) = |t| • (1 : FullBlockMat d) + G := by
      rw [hw, add_smul, one_smul]
      abel
    rw [hrw]
    exact (Matrix.PosSemidef.smul Matrix.PosSemidef.one (abs_nonneg t)).add hGpsd
  exact Recurrence.schattenNorm_le_of_posSemidef
    (isSymmetricBlockMat_normalizedBlock (isSymmetricBlockMat_blockSub hA hEm)) hQ hw0
    hsub hadd

end

end Transport
end HighContrast
end HCPolySupport

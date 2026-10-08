/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowTerminalNormalization

/-!
# High-contrast homogenization: Provider.Transport.WindowCenteredBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centered bound for a dominated cell

The centered displays of `e.source.adapted.bound` — the centered `L^Q` bound
for the early target cells and its source-tail form — rest on one pathwise
inequality, the normalized centered bound
`e.two.grid.whitney.centered.split`: if a response and its
mean are both below multiples of the reference block, then the Schatten size of
the centered response, normalized by any positive block `F`, is at most
`(2d)^{1/Q}Λ(F;𝐄)` times the sum of the two multiples.

Only two facts enter.  A symmetric block caught between `∓tF` has normalized
Schatten size at most `(2d)^{1/Q}t`, because the congruence by `F^{-1/2}` turns
the sandwich into a sandwich against the identity and the Schatten norm of such
a block is read off its `2d` eigenvalues.  And a difference of two positive
blocks, each below a multiple of `F`, is caught between the two multiples with
opposite signs — the centered block is never larger than either of its parts.

No cancellation is claimed: this is the crude bound, and the constant it
produces is the one the printed clause writes as `C_{d,Q}`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- Flattening a difference of doubled blocks is the difference of the
flattenings. -/
theorem toFullBlockMat_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  rw [Recurrence.toFullBlockMat_blockSub_apply]
  rfl

/-- **A two-sided Loewner sandwich bounds the normalized Schatten size.**  The
congruence by `F^{-1/2}` carries the sandwich `-tF ≤ H ≤ tF` onto a sandwich
against the identity, where the Schatten norm is at most `(2d)^{1/Q}t`. -/
theorem schattenSize_le_of_sandwich {Q : ℝ} (hQ : 0 < Q) {H F : BlockMat d}
    (hH : IsSymmetricBlockMat H) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) {t : ℝ} (ht : 0 ≤ t)
    (hup : toFullBlockMat H ≤ t • toFullBlockMat F)
    (hlo : (-t) • toFullBlockMat F ≤ toFullBlockMat H) :
    schattenSize Q H F ≤ (2 * d : ℝ) ^ Q⁻¹ * t := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  have h1 : toFullBlockMat (normalizedBlock H F) ≤ t • (1 : FullBlockMat d) := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
    exact (conj_normalize hFfull t).mp hup
  have h2 : (-t) • (1 : FullBlockMat d) ≤ toFullBlockMat (normalizedBlock H F) :=
    (PortableHistory.neg_smul_le_iff_normalize hFfull t).mp hlo
  refine Recurrence.schattenNorm_le_of_posSemidef (isSymmetricBlockMat_normalizedBlock hH) hQ ht
    (Matrix.le_iff.mp h1) ?_
  have h3 := Matrix.le_iff.mp h2
  rwa [neg_smul, sub_neg_eq_add, add_comm] at h3

/-- **The centered cell bound.**  A response and its mean, each below a multiple of
the reference block and each positive, have a centered difference whose
normalized Schatten size is at most `(2d)^{1/Q}Λ(F;𝐄)` times the sum of the two
multiples. -/
theorem schattenSize_blockSub_le_of_bounds {Q : ℝ} (hQ : 0 < Q)
    {A Am Eref F : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hAps : (toFullBlockMat A).PosSemidef) (hAm : IsSymmetricBlockMat Am)
    (hAmps : (toFullBlockMat Am).PosSemidef) (hEref : IsSymmetricBlockMat Eref)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {s u : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hAle : BlockMatLoewnerLE A (blockScale s Eref))
    (hAmle : BlockMatLoewnerLE Am (blockScale u Eref)) :
    schattenSize Q (blockSub A Am) F ≤
      (2 * d : ℝ) ^ Q⁻¹ * (blockSize Eref F * (s + u)) := by
  have hlam : 0 ≤ blockSize Eref F := PortableHistory.blockSize_nonneg hEref hF hFpd
  have hEF := (PortableHistory.blockSize_sandwich hEref hF hFpd).1
  have hAF : toFullBlockMat A ≤ (s * blockSize Eref F) • toFullBlockMat F := by
    have h := le_of_blockMatLoewnerLE hA (isSymmetricBlockMat_blockScale s hEref) hAle
    rw [toFullBlockMat_blockScale] at h
    refine h.trans ?_
    have h2 := smul_le_smul_of_le hs hEF
    rwa [smul_smul] at h2
  have hAmF : toFullBlockMat Am ≤ (u * blockSize Eref F) • toFullBlockMat F := by
    have h := le_of_blockMatLoewnerLE hAm (isSymmetricBlockMat_blockScale u hEref) hAmle
    rw [toFullBlockMat_blockScale] at h
    refine h.trans ?_
    have h2 := smul_le_smul_of_le hu hEF
    rwa [smul_smul] at h2
  have hA0 : (0 : FullBlockMat d) ≤ toFullBlockMat A := by
    refine Matrix.le_iff.mpr ?_
    rwa [sub_zero]
  have hAm0 : (0 : FullBlockMat d) ≤ toFullBlockMat Am := by
    refine Matrix.le_iff.mpr ?_
    rwa [sub_zero]
  set t : ℝ := blockSize Eref F * (s + u) with htdef
  have ht : 0 ≤ t := by
    rw [htdef]
    exact mul_nonneg hlam (by linarith only [hs, hu])
  refine schattenSize_le_of_sandwich hQ (isSymmetricBlockMat_blockSub hA hAm) hF hFpd ht
    ?_ ?_
  · rw [toFullBlockMat_blockSub]
    refine (sub_le_self _ hAm0).trans (hAF.trans ?_)
    have hstep : (s * blockSize Eref F) • toFullBlockMat F ≤ t • toFullBlockMat F := by
      have hdiff : t - s * blockSize Eref F = u * blockSize Eref F := by rw [htdef]; ring
      have := (posDef_toFullBlockMat hF hFpd).posSemidef.smul
        (mul_nonneg hu hlam)
      refine Matrix.le_iff.mpr ?_
      rwa [← sub_smul, hdiff]
    exact hstep
  · rw [toFullBlockMat_blockSub]
    have hstep : (-t) • toFullBlockMat F ≤ (-(u * blockSize Eref F)) • toFullBlockMat F := by
      refine Matrix.le_iff.mpr ?_
      have hdiff : -(u * blockSize Eref F) - -t = s * blockSize Eref F := by
        rw [htdef]; ring
      have := (posDef_toFullBlockMat hF hFpd).posSemidef.smul (mul_nonneg hs hlam)
      rwa [← sub_smul, hdiff]
    refine hstep.trans ?_
    have hneg : (-(u * blockSize Eref F)) • toFullBlockMat F ≤ -toFullBlockMat Am := by
      have := neg_le_neg hAmF
      rwa [← neg_smul] at this
    refine hneg.trans ?_
    have hfin : -toFullBlockMat Am ≤ toFullBlockMat A - toFullBlockMat Am := by
      have h := sub_le_sub_right hA0 (toFullBlockMat Am)
      rwa [zero_sub] at h
    exact hfin

end

end Transport
end HighContrast
end HCPolySupport

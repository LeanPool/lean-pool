/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastMeanSlotConversionAt

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The mean slot's conversion at a supplied comparability

The mean-to-reference conversion takes a variance normalized
at the adapted mean into one normalized at the reference block, and it builds
its own comparability from the entry estimate, so its constant is
`cF · kap2Value`.  Everything in that argument past the comparability step is
generic: the only fact used about the constant is that the reference is
dominated by that multiple of the mean.

This file isolates that generic half.  `scaleVariance_mean_le_of_comparability`
takes the domination as a hypothesis, and `entry_scaleVariance_mean_le_reference_at`
reads it from a comparability constant supplied by the caller.  At the isotropy
carriers the caller already holds such a constant — the same one the row cap
uses — and it is a function of the near-identity defect alone, so the conversion
factor `meanSlotConversionAt` names no geometric carrier.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The mean-slot conversion at a supplied comparability constant.**  The
`kap2Value` of the entry route is replaced by the caller's own constant. -/
@[expose]
def meanSlotConversionAt (d : ℕ) (cF kap : ℝ) : ℝ :=
  Real.sqrt (2 * d) * (cF * kap)

theorem meanSlotConversionAt_nonneg (d : ℕ) {cF kap : ℝ} (hcF0 : 0 ≤ cF)
    (hkap0 : 0 ≤ kap) : 0 ≤ meanSlotConversionAt d cF kap := by
  rw [meanSlotConversionAt]
  exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hcF0 hkap0)

/-- **The generic half of the conversion.**  Once the reference is dominated by
a multiple of the adapted mean, the normalized variance transfers with that
multiple and a dimensional Schatten factor. -/
theorem scaleVariance_mean_le_of_comparability
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {t : ℤ}
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cP : ℝ} (hcP0 : 0 ≤ cP)
    (hF2le : BlockMatLoewnerLE F (blockScale cP (adaptedMean P q t)))
    (hXm : AEStronglyMeasurable (fun a => schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t)) P) :
    scaleVariance P q (adaptedMean P q t) t ≤
      ENNReal.ofReal (Real.sqrt (2 * d) * cP) * scaleVariance P q F t := by
  classical
  have hmeansym : IsSymmetricBlockMat (adaptedMean P q t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P _ t
  have hpath : ∀ a : CoeffSpace d, schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t) ≤
      Real.sqrt (2 * d) * cP * schattenSize 2
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) F := by
    intro a
    have hXsym : IsSymmetricBlockMat
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) :=
      isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ a) hmeansym
    have h1 := PortableHistory.schattenSize_le_blockSize hXsym hmeansym hEt
      (by norm_num : (0 : ℝ) < 2)
    have hbF20 : 0 ≤ blockSize
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) F :=
      PortableHistory.blockSize_nonneg hXsym hFsym hFpd
    have hsand := PortableHistory.blockSize_sandwich hXsym hFsym hFpd
    have hF2full := le_of_blockMatLoewnerLE hFsym
      (isSymmetricBlockMat_blockScale _ hmeansym) hF2le
    rw [toFullBlockMat_blockScale] at hF2full
    have hup : toFullBlockMat
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) ≤
        (blockSize
            (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
            F * cP) • toFullBlockMat (adaptedMean P q t) := by
      refine hsand.1.trans ?_
      have h := smul_le_smul_of_nonneg_left hF2full hbF20
      rwa [smul_smul] at h
    have hlo : (-(blockSize
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
        F * cP)) • toFullBlockMat (adaptedMean P q t) ≤
        toFullBlockMat
          (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) := by
      refine le_trans ?_ hsand.2
      have h := smul_le_smul_of_nonneg_left hF2full hbF20
      rw [smul_smul] at h
      have h2 := neg_le_neg h
      rw [← neg_smul, ← neg_smul] at h2
      exact h2
    have h2 : blockSize
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
        (adaptedMean P q t) ≤
        blockSize
          (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
          F * cP :=
      PortableHistory.blockSize_le_of_sandwich hXsym hmeansym hEt
        (mul_nonneg hbF20 hcP0) hup hlo
    have h3 := PortableHistory.blockSize_le_schattenSize (Q := 2) hXsym hFsym hFpd
      (by norm_num)
    have hsq2d : (2 * d : ℝ) ^ (2 : ℝ)⁻¹ ≤ Real.sqrt (2 * d) := by
      refine le_of_eq ?_
      rw [Real.sqrt_eq_rpow, one_div]
    have hbsmean0 : 0 ≤ blockSize
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
        (adaptedMean P q t) :=
      PortableHistory.blockSize_nonneg hXsym hmeansym hEt
    calc schattenSize 2
            (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
            (adaptedMean P q t) ≤
          (2 * d : ℝ) ^ (2 : ℝ)⁻¹ * blockSize
            (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
            (adaptedMean P q t) := h1
      _ ≤ Real.sqrt (2 * d) * blockSize
          (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
          (adaptedMean P q t) :=
        mul_le_mul_of_nonneg_right hsq2d hbsmean0
      _ ≤ Real.sqrt (2 * d) *
          (blockSize
            (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
            F * cP) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (2 * d) *
          (schattenSize 2
            (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
            F * cP) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right h3 hcP0
      _ = Real.sqrt (2 * d) * cP * schattenSize 2
          (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
          F := by ring
  rw [scaleVariance, scaleVariance]
  have hsc0 : ∀ a : CoeffSpace d, 0 ≤ schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t) := by
    intro a
    rw [schattenSize]
    exact Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock
        (isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ a) hmeansym)) 2
  have hmono : eLpNorm
      (fun a => schattenSize 2
        (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
        (adaptedMean P q t)) 2 P ≤
      eLpNorm
        (fun a => Real.sqrt (2 * d) * cP * schattenSize 2
          (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
          F) 2 P := by
    refine eLpNorm_mono_real hXm fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hsc0 a)]
    exact hpath a
  refine le_trans hmono ?_
  have hsmul : (fun a => Real.sqrt (2 * d) * cP * schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) F) =
      (Real.sqrt (2 * d) * cP) •
        fun a => schattenSize 2
          (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) F := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, eLpNorm_const_smul,
    Real.enorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) hcP0)]

/-- **The conversion at a supplied comparability constant.**  The caller's
constant replaces the entry route's `kap2Value`, and with it every geometric
carrier leaves the conversion factor. -/
theorem entry_scaleVariance_mean_le_reference_at
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {E : BlockMat d} {t : ℤ}
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cF kap : ℝ} (hcF0 : 0 ≤ cF) (hkap0 : 0 ≤ kap) (hFeq : F = blockScale cF E)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X (blockMatVecMul (adaptedMean P q t) X))
    (hXm : AEStronglyMeasurable (fun a => schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t)) P) :
    scaleVariance P q (adaptedMean P q t) t ≤
      ENNReal.ofReal (meanSlotConversionAt d cF kap) * scaleVariance P q F t := by
  have hF2le : BlockMatLoewnerLE F
      (blockScale (cF * kap) (adaptedMean P q t)) := by
    intro X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
    have h1 : blockVecDot X (blockMatVecMul F X) =
        cF * blockVecDot X (blockMatVecMul E X) := by
      rw [hFeq, Sharp.blockVecDot_blockMatVecMul_blockScale]
    have h4 := mul_le_mul_of_nonneg_left (hcomp X) hcF0
    have hassoc : cF * (kap * blockVecDot X
        (blockMatVecMul (adaptedMean P q t) X)) =
        cF * kap * blockVecDot X (blockMatVecMul (adaptedMean P q t) X) := by
      ring
    rw [h1, hassoc] at *
    linarith only [h4]
  rw [meanSlotConversionAt]
  exact scaleVariance_mean_le_of_comparability hEt hFsym hFpd
    (mul_nonneg hcF0 hkap0) hF2le hXm

/-- **The mean slot at a supplied comparability constant.** -/
theorem entry_supply_mean_slot_bound_at
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {E : BlockMat d} {t : ℤ}
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {cF kap : ℝ} (hcF0 : 0 ≤ cF) (hkap0 : 0 ≤ kap) (hFeq : F = blockScale cF E)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X (blockMatVecMul (adaptedMean P q t) X))
    {V0 : ℝ} (hterm : scaleVariance P q F t ≤ ENNReal.ofReal V0)
    (hXm : AEStronglyMeasurable (fun a => schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      (adaptedMean P q t)) P) :
    scaleVariance P q (adaptedMean P q t) t ≤
      ENNReal.ofReal (meanSlotConversionAt d cF kap * V0) := by
  have hconv0 : 0 ≤ meanSlotConversionAt d cF kap :=
    meanSlotConversionAt_nonneg d hcF0 hkap0
  have hstep : ENNReal.ofReal (meanSlotConversionAt d cF kap) *
      scaleVariance P q F t ≤
      ENNReal.ofReal (meanSlotConversionAt d cF kap) * ENNReal.ofReal V0 :=
    mul_le_mul_right hterm _
  have hmul : ENNReal.ofReal (meanSlotConversionAt d cF kap) *
      ENNReal.ofReal V0 =
      ENNReal.ofReal (meanSlotConversionAt d cF kap * V0) :=
    (ENNReal.ofReal_mul hconv0).symm
  rw [← hmul]
  exact le_trans
    (entry_scaleVariance_mean_le_reference_at hEt hFsym hFpd hcF0 hkap0 hFeq
      hcomp hXm) hstep

end

end HCPolySupport.HighContrast.Quenched

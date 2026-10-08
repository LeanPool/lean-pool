/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewNormalization
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileCarriers
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewProfiles

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew invariance of response profile carriers

The hatted blocks in the response argument are simultaneous shear
congruences of the original samplewise blocks and annealed means.  This file
identifies the resulting all-scale maximum, recent defects, and centered and
below-start profile maxima with their unhatted carriers.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal Matrix

noncomputable section

variable {d : ℕ}

/-- Constant-skew recentering preserves the all-scale positive excess
maximum when the reference block is recentered simultaneously. -/
theorem diagonalWeakMaximum_subSkew {q : Mat d} (hq : q.PosDef)
    (rho : ℝ) (t : ℤ) (E : BlockMat d) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) :
    diagonalWeakMaximum rho q t (skewBlockCongr g E) (a.subSkew g hg) =
      diagonalWeakMaximum rho q t E a := by
  rw [diagonalWeakMaximum_eq, diagonalWeakMaximum_eq]
  simp_rw [adaptedResponse_subSkew hq, blockExcess_skewBlockCongr]

/-- Constant-skew recentering preserves every recent cell defect. -/
theorem diagonalWeakCellDefect_subSkew {q : Mat d} (hq : q.PosDef)
    (k t : ℤ) (E : BlockMat d) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) :
    diagonalWeakCellDefect q k t (skewBlockCongr g E) (a.subSkew g hg) =
      diagonalWeakCellDefect q k t E a := by
  have hterminal :
      coarseBlock (adaptedCell q t) (a.subSkew g hg) =
        skewBlockCongr g (coarseBlock (adaptedCell q t) a) := by
    simpa only [adaptedDomain_carrier] using
      coarseBlock_subSkew (adaptedDomain hq t) a g hg
  rw [diagonalWeakCellDefect_eq, diagonalWeakCellDefect_eq]
  simp_rw [adaptedResponse_subSkew hq, hterminal,
    ← blockSub_skewBlockCongr, blockSize_skewBlockCongr]

/-- The average of normalized defects is the normalization of their raw
average. -/
theorem diagonalWeakAverageDefect_eq_normalized_average
    (q : Mat d) (k t : ℤ) (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakAverageDefect q k t E a =
      normalizedBlock
        (ofFullBlockMat
          (((alignedIndex q k t).card : ℝ)⁻¹ •
            ∑ w ∈ alignedIndex q k t,
              toFullBlockMat
                (blockSub (adaptedResponse q k w a)
                  (coarseBlock (adaptedCell q t) a)))) E := by
  rw [diagonalWeakAverageDefect_eq]
  exact (normalizedBlock_ofFullBlockMat_smul_sum
    (alignedIndex q k t) ((alignedIndex q k t).card : ℝ)⁻¹
    (fun w ↦ blockSub (adaptedResponse q k w a)
      (coarseBlock (adaptedCell q t) a)) E).symm

private theorem isSymmetricBlockMat_ofFullBlockMat_smul_sum {ι : Type*}
    (s : Finset ι) (c : ℝ) (A : ι → BlockMat d)
    (hA : ∀ i ∈ s, IsSymmetricBlockMat (A i)) :
    IsSymmetricBlockMat
      (ofFullBlockMat (c • ∑ i ∈ s, toFullBlockMat (A i))) := by
  intro α β
  simp only [blockMatEntry_ofFullBlockMat, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  apply congrArg (c * ·)
  apply Finset.sum_congr rfl
  intro i hi
  have h := hA i hi α β
  simpa only [blockMatEntry_eq_toFullBlockMat] using h

/-- The scalar size of the averaged normalized defect is unchanged by a
constant-skew recentering. -/
theorem blockSize_diagonalWeakAverageDefect_subSkew {q : Mat d}
    (hq : q.PosDef) (k t : ℤ) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) :
    blockSize
        (diagonalWeakAverageDefect q k t (skewBlockCongr g E)
          (a.subSkew g hg)) (blockIdentity d) =
      blockSize (diagonalWeakAverageDefect q k t E a) (blockIdentity d) := by
  let raw : BlockMat d :=
    ofFullBlockMat
      (((alignedIndex q k t).card : ℝ)⁻¹ •
        ∑ w ∈ alignedIndex q k t,
          toFullBlockMat
            (blockSub (adaptedResponse q k w a)
              (coarseBlock (adaptedCell q t) a)))
  let rawHat : BlockMat d :=
    ofFullBlockMat
      (((alignedIndex q k t).card : ℝ)⁻¹ •
        ∑ w ∈ alignedIndex q k t,
          toFullBlockMat
            (blockSub (adaptedResponse q k w (a.subSkew g hg))
              (coarseBlock (adaptedCell q t) (a.subSkew g hg))))
  have hterminal :
      coarseBlock (adaptedCell q t) (a.subSkew g hg) =
        skewBlockCongr g (coarseBlock (adaptedCell q t) a) := by
    simpa only [adaptedDomain_carrier] using
      coarseBlock_subSkew (adaptedDomain hq t) a g hg
  have hraw : rawHat = skewBlockCongr g raw := by
    dsimp only [rawHat, raw]
    simp_rw [adaptedResponse_subSkew hq, hterminal,
      ← blockSub_skewBlockCongr]
    exact (skewBlockCongr_ofFullBlockMat_smul_sum g
      (alignedIndex q k t) ((alignedIndex q k t).card : ℝ)⁻¹
      (fun w ↦ blockSub (adaptedResponse q k w a)
        (coarseBlock (adaptedCell q t) a))).symm
  have hrawSym : IsSymmetricBlockMat raw := by
    apply isSymmetricBlockMat_ofFullBlockMat_smul_sum
    intro w _
    apply isSymmetricBlockMat_blockSub
    · simpa only [adaptedResponse] using
        isSymmetricBlockMat_coarseBlock (adaptedCellAt q k w) a
    · exact isSymmetricBlockMat_coarseBlock (adaptedCell q t) a
  have hrawHatSym : IsSymmetricBlockMat rawHat := by
    rw [hraw]
    exact isSymmetricBlockMat_skewBlockCongr hrawSym
  have hrepr : diagonalWeakAverageDefect q k t E a =
      normalizedBlock raw E := by
    exact diagonalWeakAverageDefect_eq_normalized_average q k t E a
  have hreprHat :
      diagonalWeakAverageDefect q k t (skewBlockCongr g E)
          (a.subSkew g hg) =
        normalizedBlock rawHat (skewBlockCongr g E) := by
    exact diagonalWeakAverageDefect_eq_normalized_average q k t
      (skewBlockCongr g E) (a.subSkew g hg)
  calc
    blockSize
        (diagonalWeakAverageDefect q k t (skewBlockCongr g E)
          (a.subSkew g hg)) (blockIdentity d) =
        blockSize rawHat (skewBlockCongr g E) := by
          rw [hreprHat, blockSize_normalizedBlock_identity hrawHatSym
            (isSymmetricBlockMat_skewBlockCongr hE)
            (blockPosDef_skewBlockCongr hEpd)]
    _ = blockSize raw E := by rw [hraw, blockSize_skewBlockCongr]
    _ = blockSize (diagonalWeakAverageDefect q k t E a)
        (blockIdentity d) := by
          rw [hrepr, blockSize_normalizedBlock_identity hrawSym hE hEpd]

/-- Constant-skew recentering preserves the recent cell sum. -/
theorem diagonalWeakCellSum_subSkew {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) (s : ℝ) (E : BlockMat d) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) :
    diagonalWeakCellSum q t H s (skewBlockCongr g E) (a.subSkew g hg) =
      diagonalWeakCellSum q t H s E a := by
  rw [diagonalWeakCellSum_eq, diagonalWeakCellSum_eq]
  simp_rw [diagonalWeakCellDefect_subSkew hq]

/-- Constant-skew recentering preserves the recent averaged-defect sum. -/
theorem diagonalWeakAverageSum_subSkew {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) (s rho : ℝ) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) :
    diagonalWeakAverageSum q t H s rho (skewBlockCongr g E)
        (a.subSkew g hg) =
      diagonalWeakAverageSum q t H s rho E a := by
  rw [diagonalWeakAverageSum_eq, diagonalWeakAverageSum_eq]
  simp_rw [blockSize_diagonalWeakAverageDefect_subSkew hq _ _ hE hEpd]

end

end HCPolySupport.HighContrast.Response

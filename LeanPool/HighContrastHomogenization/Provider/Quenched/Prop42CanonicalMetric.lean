/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.ReferenceRadius
public import LeanPool.HighContrastHomogenization.Setup.TransportObjects
public import LeanPool.HighContrastHomogenization.Provider.Initialization.Reference
public import LeanPool.HighContrastHomogenization.Provider.ShortHop.Eccentricity
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.SchurHelpers

/-!
# High-contrast homogenization: Provider.Quenched.Prop42CanonicalMetric

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Canonical-grid eccentricity for the small-contrast argument

The adapted grid in the perturbative argument is matched to the canonical
metric of the reference block.  Its eccentricity is controlled by the
reference aspect ratio, so the geometry introduces no dependence on the
private ellipticity constants of a coefficient field.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The canonical metric of a coarse-ellipticity reference block has
eccentricity at most the reference aspect ratio. -/
theorem witnessEccentricity_canonicalMetric_le_aspectRatio [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    witnessEccentricity (canonicalMetric E) ≤ aspectRatio E := by
  have : Nonempty (Fin d) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  let EF : FullBlockMat d := toFullBlockMat E
  let s : Mat d := schurSigma E
  let sStar : Mat d := schurSigmaStar E
  let k : Mat d := schurSkew E
  have hEF : EF.PosDef := by
    dsimp only [EF]
    exact posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hform : EF = schurBlock s sStar k := by
    dsimp only [EF, s, sStar, k]
    exact Initialization.toFullBlockMat_eq_schurBlock
      hdag.refBlock_isSymm hdag.refBlock_posDef
  have hStar : sStar.PosDef := by
    dsimp only [sStar, schurSigmaStar]
    exact (posDef_lowerRight hdag.refBlock_isSymm
      hdag.refBlock_posDef).inv
  have hs : s.PosDef := by
    apply posDef_of_posDef_schurBlock hStar
    rw [← hform]
    exact hEF
  have hsharpBlock : BlockMatLoewnerLE (blockSharp E) E :=
    Initialization.blockMatLoewnerLE_blockSharp_reference hdag
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_blockSharp hdag.refBlock_isSymm
      hdag.refBlock_posDef
  have hsharp : fullBlockSharp EF ≤ EF := by
    have hle := le_of_blockMatLoewnerLE hsharpSymm
      hdag.refBlock_isSymm hsharpBlock
    dsimp only [EF] at hle ⊢
    rwa [toFullBlockMat_blockSharp] at hle
  have horder : MatLoewnerLE sStar s := by
    dsimp only [sStar, s]
    exact Initialization.matLoewnerLE_of_le
      (Initialization.schurSigmaStar_le_schurSigma
        hdag.refBlock_isSymm hdag.refBlock_posDef hsharpBlock)
  have hPi : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_schurSigmaStar_le
      hdag.refBlock_isSymm hdag.refBlock_posDef horder
  have hR : E.lowerRight.PosDef :=
    posDef_lowerRight hdag.refBlock_isSymm hdag.refBlock_posDef
  have hspec : 0 < specBound E.lowerRight := by
    rw [specBound_eq_norm hR.posSemidef]
    exact norm_pos_iff.mpr hR.isUnit.ne_zero
  have hlam : 0 < lambdaRef E := by
    rw [lambdaRef]
    positivity
  have hLamLower : lambdaRef E ≤ bigLambdaRef E := by
    have h := (le_div_iff₀ hlam).mp hPi
    simpa only [one_mul, aspectRatio] using h
  have hLam : 0 < bigLambdaRef E :=
    lt_of_lt_of_le hlam hLamLower
  have hlowForm : MatLoewnerLE
      (lambdaRef E • (1 : Mat d)) sStar := by
    have hone := matLoewnerLE_one_specBound_smul_schurSigmaStar
      hdag.refBlock_isSymm hdag.refBlock_posDef
    have hscaled := matLoewnerLE_smul hlam.le hone
    have hcancel : lambdaRef E * specBound E.lowerRight = 1 := by
      rw [lambdaRef, inv_mul_cancel₀ hspec.ne']
    simpa only [smul_smul, hcancel, one_smul] using hscaled
  have hlow : lambdaRef E • (1 : Mat d) ≤ sStar :=
    Initialization.le_of_matLoewnerLE
      (Matrix.PosSemidef.one.smul hlam.le).isHermitian
      hStar.isHermitian hlowForm
  have hhighForm : MatLoewnerLE s
      (bigLambdaRef E • (1 : Mat d)) := by
    dsimp only [s]
    exact matLoewnerLE_schurSigma_bigLambdaRef_smul_one
      hdag.refBlock_posDef
  have hhigh : s ≤ bigLambdaRef E • (1 : Mat d) :=
    Initialization.le_of_matLoewnerLE hs.isHermitian
      (Matrix.PosSemidef.one.smul hLam.le).isHermitian hhighForm
  have hradius : projDist 1 (canonicalMetric E) ≤
      (1 / 2 : ℝ) * Real.log (aspectRatio E) := by
    have hraw := (canonMetric_reference_radius hEF hsharp hs hStar hform
      hlam hLam hlow hhigh).2.2
    simpa only [canonicalMetric, EF, aspectRatio] using hraw
  have hlogPi : 0 ≤ Real.log (aspectRatio E) :=
    Real.log_nonneg hPi
  have hradius' : projDist 1 (canonicalMetric E) ≤
      Real.log (aspectRatio E) := by
    linarith only [hradius, hlogPi]
  rw [ShortHop.witnessEccentricity_eq_exp
    (by simpa only [canonicalMetric] using posDef_canonMetric hEF)]
  calc
    Real.exp (projDist 1 (canonicalMetric E)) ≤
        Real.exp (Real.log (aspectRatio E)) :=
      Real.exp_le_exp.mpr hradius'
    _ = aspectRatio E :=
      Real.exp_log (lt_of_lt_of_le zero_lt_one hPi)

end

end HCPolySupport.HighContrast.Quenched

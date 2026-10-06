/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Consistency.PrintedForm
public import LeanPool.HighContrastHomogenization.Annealed.Positivity

/-!
# High-contrast homogenization: Annealed.Contrast

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed contrast in printed form

The reference text writes the annealed contrast `Θ_m` of `e.Theta.m`
as a minimum over skew matrices `h` of the conjugated norms
`|σ̄_*^{-1/2} (σ̄ + (k̄ - h)ᵗ σ̄_*⁻¹ (k̄ - h)) σ̄_*^{-1/2}|`,
the Schur data being that of the annealed block `𝐀̄(□_m)`.  The encoding
`annealedContrast` is instead the Loewner-scaling infimum, and the identification
of the two is available on symmetric positive definite doubled blocks.

This file supplies the symmetry half of that hypothesis at the annealed block —
unconditionally, since the sample response is symmetric at every field and the
annealed block is its entrywise expectation — and then assembles the printed
form of `Θ_m` and of the reference aspect ratio `Π` under
`e.coarse.ellipticity` alone: positive definiteness of the annealed block is
a consequence of that assumption, and positive definiteness of the reference
block is one of its fields.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The annealed block is a symmetric doubled matrix, at every law and every
cell.  Symmetry of the sample response is pointwise in the field, and the
annealed block is the entrywise expectation, so no integrability is needed. -/
theorem isSymmetricBlockMat_annealedBlock (P : Measure (CoeffSpace d))
    (U : Set (Vec d)) : IsSymmetricBlockMat (annealedBlock P U) := by
  intro α β
  rw [blockMatEntry_annealedBlock, blockMatEntry_annealedBlock]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  exact isSymmetricBlockMat_coarseBlockMatrix U _ α β

/-- **The annealed contrast in printed form.**  On a positive definite annealed
block, `Θ_m` is the infimum over skew `h` of the conjugated norms
`|σ̄_*^{-1/2} (σ̄ + (k̄ - h)ᵗ σ̄_*⁻¹ (k̄ - h)) σ̄_*^{-1/2}|`
of `e.Theta.m`, the conjugating matrix being the positive
semidefinite square root of the lower-right block `σ̄_*⁻¹`. -/
theorem annealedContrast_eq_sInf_conj {P : Measure (CoeffSpace d)} {m : ℤ}
    (hpos : Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d m))) :
    annealedContrast P m =
      sInf ((fun h => specBound
          (matSqrt (annealedBlock P (centeredCube d m)).lowerRight *
            skewCorrectedForm (annealedBlock P (centeredCube d m)) h *
            matSqrt (annealedBlock P (centeredCube d m)).lowerRight)) ''
        {h : Mat d | IsSkewMat h}) :=
  blockContrast_eq_sInf_conj (isSymmetricBlockMat_annealedBlock _ _) hpos

/-! ## The printed objects of the frozen conclusion -/

/-- Under `e.coarse.ellipticity` the annealed block is positive definite at
every scale, so `Θ_m` is the infimum of the printed family with no further
hypothesis. -/
theorem annealedContrast_eq_sInf_conj_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    annealedContrast P m =
      sInf ((fun h => specBound
          (matSqrt (annealedBlock P (centeredCube d m)).lowerRight *
            skewCorrectedForm (annealedBlock P (centeredCube d m)) h *
            matSqrt (annealedBlock P (centeredCube d m)).lowerRight)) ''
        {h : Mat d | IsSkewMat h}) :=
  annealedContrast_eq_sInf_conj
    (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m)

/-- **`Θ_m` is exactly the printed object.**  Under `e.coarse.ellipticity`
the annealed contrast of the frozen conclusion is the least value of
`|σ̄_*^{-1/2} (σ̄ + (k̄ - h)ᵗ σ̄_*⁻¹ (k̄ - h)) σ̄_*^{-1/2}|`
over the skew matrices, the bars being the spectral norm: the minimum written at
`e.Theta.m`, attained, with no infimum reading left over. -/
theorem isLeast_norm_annealedContrast_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    IsLeast ((fun h => ‖matSqrt (annealedBlock P (centeredCube d m)).lowerRight *
        skewCorrectedForm (annealedBlock P (centeredCube d m)) h *
        matSqrt (annealedBlock P (centeredCube d m)).lowerRight‖) ''
      {h : Mat d | IsSkewMat h})
      (annealedContrast P m) :=
  isLeast_norm_blockContrast (isSymmetricBlockMat_annealedBlock _ _)
    (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m)

/-- **`Λ_0` is exactly the printed object** under `e.coarse.ellipticity`: the
reference block of the assumption is symmetric and positive definite, which is
all the printed minimum needs. -/
theorem isLeast_norm_bigLambdaRef_of_coarseEllipticityDagger
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    IsLeast ((fun h => ‖skewCorrectedForm E h‖) '' {h : Mat d | IsSkewMat h})
      (bigLambdaRef E) :=
  isLeast_norm_bigLambdaRef hdag.refBlock_isSymm hdag.refBlock_posDef

/-- **`Π` is exactly the printed aspect ratio** under `e.coarse.ellipticity`:
the quotient `Λ_0 / λ_0` of `e.reference.aspect.ratio`, the numerator a minimum of
spectral norms realized at a skew matrix. -/
theorem exists_isSkewMat_aspectRatio_eq_norm_of_coarseEllipticityDagger
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    ∃ h : Mat d, IsSkewMat h ∧
      aspectRatio E = ‖skewCorrectedForm E h‖ / ‖E.lowerRight‖⁻¹ :=
  exists_isSkewMat_aspectRatio_eq_norm hdag.refBlock_isSymm hdag.refBlock_posDef

end

end HighContrast
end HCPolySupport

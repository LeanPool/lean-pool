/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AlignedSubdivisionVariance

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSubdivisionSupply

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The subdivision supply at the adapted-mean normalizer

The hypothesis `hsubdiv` normalizes both `lqSchattenSize` terms by
`adaptedMean P q p'`.
`AlignedSubdivisionVariance.exists_alignedSubdivisionVarianceConstant`
quantifies over the normalizer, so it can be instantiated at this block.  The
result below has exactly the `hsubdiv` shape used by
`entry_lagged_variance_supply_of_block_split`, `entry_supply_slot_bound_of_block_split` and
`entry_supply_deep_slot_bound_of_block_split`, with no reshaping.

The one extra frozen premise the producer needs beyond the supplies' own is
`IsUnitRangeLaw P`, which the subdivision constant carries.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

/-- A single dimensional subdivision constant serves every law, grid, and
scale pair at the adapted-mean normalizer. -/
theorem exists_repaired_subdivision_supply (d : ℕ) (hd : 2 ≤ d) :
    ∃ Csub : ℝ, 0 < Csub ∧
      ∀ (P : Measure (CoeffSpace d)) (g : ℝ) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ (lAl : ℤ) (mAl : Mat d),
          IsRoundedGrid lAl (roundedGrid lAl mAl) →
          ∀ (j' p' : ℤ), lAl ≤ j' → j' ≤ p' →
            ∃ Z : Finset (Fin d → ℤ),
              (↑Z : Set (Fin d → ℤ)) =
                  {w | adaptedCellCenter (roundedGrid lAl mAl) j' w ∈
                    adaptedCell (roundedGrid lAl mAl) p'} ∧
                Z.card = 3 ^ (d * (p' - j').toNat) ∧ Z.Nonempty ∧
                lqSchattenSize P 2
                    (fun a ↦ blockSub
                      (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                        ∑ w ∈ Z,
                          toFullBlockMat
                            (coarseBlock
                              (adaptedCellAt (roundedGrid lAl mAl) j' w) a)))
                      (adaptedMean P (roundedGrid lAl mAl) j'))
                      (adaptedMean P (roundedGrid lAl mAl) p') ≤
                  ENNReal.ofReal
                      (Csub * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
                    lqSchattenSize P 2
                      (fun a ↦ blockSub
                        (coarseBlock (adaptedCell (roundedGrid lAl mAl) j') a)
                        (adaptedMean P (roundedGrid lAl mAl) j'))
                      (adaptedMean P (roundedGrid lAl mAl) p') := by
  obtain ⟨C, hC, hsub⟩ := exists_alignedSubdivisionVarianceConstant d hd
  refine ⟨C, hC, ?_⟩
  intro P g E Ψ K S hP hstat hunit hdag lAl mAl hgrid j' p' hlj hjp
  exact hsub P g E Ψ K S hP hstat hunit hdag lAl (roundedGrid lAl mAl) hgrid
    j' p' hlj hjp (adaptedMean P (roundedGrid lAl mAl) p')

end

end HCPolySupport.HighContrast.Quenched

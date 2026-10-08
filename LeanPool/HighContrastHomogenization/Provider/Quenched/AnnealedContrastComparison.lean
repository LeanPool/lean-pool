/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedEndpointAssembly
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate

/-!
# High-contrast homogenization: Provider.Quenched.AnnealedContrastComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed block comparison from the annealed contrast

The endgame display
`e.algebraic.block.decay` compares the
Euclidean annealed blocks with the annealed limit block at the factor
`1 + 6·3^{-αj}`.  Its scalar input is the annealed contrast `Θ` of
`e.Theta.m`, not the canonical imbalance `𝔡` of
`e.scale.selection.canonical.metric`, and the reference intermediate
`κ_𝐄 ≤ 1 + 6(Θ - 1)` of the factor-six reference-block comparison is exactly
what converts the one into the other.

The intermediate applies to every Euclidean annealed block, because the annealed
primal-adjoint order puts that block above its own sharp.  Combined with
`𝐀_bar(□_m) ≼ 𝔡(𝐀_bar(□_m)) · 𝐀_bar`, this yields the printed comparison, with the
printed constant six and no further input.

Consequently the whole annealed package of the endgame — the limit block, its
symmetry, its positive definiteness, both Loewner comparisons, the reindexing
along the scale covariance, and the polynomial length account — rests on the
single scalar clause
`e.algebraic.contrast.decay`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

section Dagger

variable [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
  {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}

/-- **The annealed imbalance is controlled by the annealed contrast**, at the
printed constant six.  This is the factor-six reference-block comparison read at
the Euclidean annealed block, whose sharp ordering, the annealed primal-adjoint
order, supplies the intermediate's hypothesis. -/
theorem blockImbalance_annealedBlock_le_one_add_six_mul_annealedContrast_sub_one
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    blockImbalance (annealedBlock P (centeredCube d m)) ≤
      1 + 6 * (annealedContrast P m - 1) := by
  have hsymm : IsSymmetricBlockMat (annealedBlock P (centeredCube d m)) :=
    isSymmetricBlockMat_annealedBlock P _
  have hpos := blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m
  have hsharp :
      BlockMatLoewnerLE (blockSharp (annealedBlock P (centeredCube d m)))
        (annealedBlock P (centeredCube d m)) :=
    Sharp.blockSharp_annealedBlock_le_centeredCube m
      (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag m)
  have hk : blockImbalance (annealedBlock P (centeredCube d m)) =
      kappaRef (annealedBlock P (centeredCube d m)) :=
    (kappaRef_eq_canonImbalance hsymm hpos).symm
  rw [hk]
  exact Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one hsymm hpos hsharp

/-- **The upper half of the endgame block comparison, from the annealed contrast
alone**, at the printed constant six. -/
theorem blockMatLoewnerLE_blockScale_annealedLimitBlock_of_annealedContrast_le
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {m : ℤ} (hm : 0 ≤ m)
    {eps : ℝ} (heps : annealedContrast P m - 1 ≤ eps) :
    BlockMatLoewnerLE (annealedBlock P (centeredCube d m))
      (blockScale (1 + 6 * eps) (annealedLimitBlock P)) := by
  refine blockMatLoewnerLE_blockScale_annealedLimitBlock_of_blockImbalance_le hstat hdag
    hm ?_
  have h := blockImbalance_annealedBlock_le_one_add_six_mul_annealedContrast_sub_one hdag m
  linarith only [h, heps]

end Dagger

/-! ## The endpoint from the printed contrast decay -/

/-- **The annealed endpoint of the endgame from the printed contrast decay
alone.**  The hypothesis `hcontrast` is
`e.algebraic.contrast.decay` on the rebased law; the
block comparison `e.algebraic.block.decay`
is derived, not assumed. -/
theorem exists_annealed_endpoint_of_rebased_contrast_decay [NeZero d]
    {P Pbase : Measure (CoeffSpace d)} [IsProbabilityMeasure Pbase]
    {E Ebase : BlockMat d} {Ψbase : ℝ → ℝ} {K Kbase gBase : ℝ}
    {Sbase : CoeffSpace d → ℝ} {alpha Crebase Cdelay Cann : ℝ} {nBase m0 : ℕ}
    (hstat : HCPoly.Frozen.IsStationaryLaw Pbase)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger Pbase gBase Ebase Ψbase Kbase Sbase)
    (hcovContrast : ∀ j : ℕ,
      annealedContrast Pbase (j : ℤ) = annealedContrast P ((nBase + j : ℕ) : ℤ))
    (hcovBlock : ∀ j : ℕ,
      annealedBlock Pbase (centeredCube d (j : ℤ)) =
        annealedBlock P (centeredCube d ((nBase + j : ℕ) : ℤ)))
    (hbase : 1 ≤ 2 + aspectRatio E * K)
    (hnBase : (3 : ℝ) ^ nBase ≤ (2 + aspectRatio E * K) ^ Crebase)
    (hrefCost : 2 + aspectRatio Ebase * Kbase ≤ (2 + aspectRatio E * K) ^ Crebase)
    (hCdelay : 0 ≤ Cdelay) (hCann : Crebase * (1 + Cdelay) ≤ Cann)
    (hdelay : (3 : ℝ) ^ m0 ≤ (2 + aspectRatio Ebase * Kbase) ^ Cdelay)
    (hcontrast : ∀ j : ℕ,
      annealedContrast Pbase ((m0 + j : ℕ) : ℤ) - 1 ≤ (3 : ℝ) ^ (-alpha * (j : ℝ))) :
    ∃ (Abar : BlockMat d) (Nann : ℕ),
      IsSymmetricBlockMat Abar ∧
      Book.Ch02.BlockPosDef Abar ∧
      (3 : ℝ) ^ Nann ≤ (2 + aspectRatio E * K) ^ Cann ∧
      (∀ j : ℕ,
        annealedContrast P ((Nann + j : ℕ) : ℤ) - 1 ≤ (3 : ℝ) ^ (-alpha * (j : ℝ))) ∧
      (∀ j : ℕ,
        BlockMatLoewnerLE Abar (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ))) ∧
        BlockMatLoewnerLE (annealedBlock P (centeredCube d ((Nann + j : ℕ) : ℤ)))
          (blockScale (1 + 6 * (3 : ℝ) ^ (-alpha * (j : ℝ))) Abar)) ∧
      Abar = annealedLimitBlock Pbase := by
  refine exists_annealed_endpoint_of_rebased_decay hstat hdag hcovContrast hcovBlock hbase
    hnBase hrefCost hCdelay hCann hdelay hcontrast ?_
  intro j
  exact blockMatLoewnerLE_blockScale_annealedLimitBlock_of_annealedContrast_le hstat hdag
    (Int.natCast_nonneg _) (hcontrast j)

end

end Quenched
end HighContrast
end HCPolySupport

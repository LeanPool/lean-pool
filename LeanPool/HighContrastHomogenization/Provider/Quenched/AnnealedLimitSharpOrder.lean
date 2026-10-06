/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Provider.Entry.ContrastBridge
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedLimitBlock
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockPositivity

/-!
# High-contrast homogenization: Provider.Quenched.AnnealedLimitSharpOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp order around the annealed limit block

The annealed limit block of the Euclidean cubes is caught between a Euclidean
annealed block and its primal-adjoint dual.  The primal-adjoint involution
reverses the Loewner order, so where the annealed blocks decrease along the
generations their sharps increase, and the annealed primal-adjoint order keeps
every sharp below its own block.  Consequently

`𝐀(□_m)^♯ ≼ 𝐀̄ ≼ 𝐀(□_m)`

at every nonnegative generation, with `𝐀̄` the limit block.  Two consequences are
recorded.

*Positivity.*  The sharp of a positive definite doubled block is positive
definite, so the limit block is positive definite.  This uses no quantitative
decay of the annealed contrast.

*The upper comparison.*  The canonical imbalance `𝔡` of
`e.scale.selection.canonical.metric` satisfies `F ≼ 𝔡(F) F^♯` by definition, so

`𝐀̄(□_m) ≼ 𝔡(𝐀̄(□_m)) · 𝐀̄`.

The upper half of the endgame display
`e.algebraic.block.decay` therefore follows
from a scalar bound on the annealed imbalance alone.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open Filter Topology

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The imbalance is an admissible dilation against the sharp -/

/-- **A doubled block lies below its imbalance times its own sharp.**  This is
the defining property of the canonical imbalance of
`e.scale.selection.canonical.metric`, in the structural dialect. -/
theorem blockMatLoewnerLE_blockScale_blockImbalance_blockSharp {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    BlockMatLoewnerLE F (blockScale (blockImbalance F) (blockSharp F)) := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hsymm hpos
  have himb : toFullBlockMat F ≤
      blockImbalance F • fullBlockSharp (toFullBlockMat F) := by
    have hrw : blockImbalance F = canonImbalance (toFullBlockMat F) := rfl
    rw [hrw, canonImbalance_eq hFfull]
    exact le_relSize_smul hFfull.posSemidef (posDef_fullBlockSharp hFfull)
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale, toFullBlockMat_blockSharp]
  exact himb

/-! ## The sharp order along the generations -/

section Dagger

variable [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
  {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}

/-- **The sharp of a Euclidean annealed block lies below every Euclidean
annealed block of a nonnegative generation.**  Above the given generation this
is the order reversal of the primal-adjoint involution followed by the annealed
primal-adjoint order; below it, the sharp order followed by the mean order of
`p.fixed.geometry.parent.child.recurrence`. -/
theorem blockMatLoewnerLE_blockSharp_annealedBlock
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {m : ℤ} (hm : 0 ≤ m)
    (n : ℕ) :
    BlockMatLoewnerLE (blockSharp (annealedBlock P (centeredCube d m)))
      (annealedBlock P (centeredCube d (n : ℤ))) := by
  have hsymm : IsSymmetricBlockMat (annealedBlock P (centeredCube d m)) :=
    isSymmetricBlockMat_annealedBlock P _
  have hsymn : IsSymmetricBlockMat (annealedBlock P (centeredCube d (n : ℤ))) :=
    isSymmetricBlockMat_annealedBlock P _
  have hpdm := blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m
  have hpdn := blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag (n : ℤ)
  have hsharpm :
      BlockMatLoewnerLE (blockSharp (annealedBlock P (centeredCube d m)))
        (annealedBlock P (centeredCube d m)) :=
    Sharp.blockSharp_annealedBlock_le_centeredCube m
      (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag m)
  rcases le_total m (n : ℤ) with hmn | hnm
  · have hmono :
        BlockMatLoewnerLE (annealedBlock P (centeredCube d (n : ℤ)))
          (annealedBlock P (centeredCube d m)) :=
      Entry.annealedBlock_centeredCube_le_of_nonneg hstat hdag hm hmn
    exact (blockMatLoewnerLE_blockSharp_of_le hsymn hsymm hpdn hpdm hmono).trans
      (Sharp.blockSharp_annealedBlock_le_centeredCube (n : ℤ)
        (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag (n : ℤ)))
  · exact hsharpm.trans
      (Entry.annealedBlock_centeredCube_le_of_nonneg hstat hdag (Int.natCast_nonneg n) hnm)

/-- **The sharp of a Euclidean annealed block lies below the annealed limit
block.** -/
theorem blockMatLoewnerLE_blockSharp_annealedLimitBlock
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {m : ℤ} (hm : 0 ≤ m) :
    BlockMatLoewnerLE (blockSharp (annealedBlock P (centeredCube d m)))
      (annealedLimitBlock P) :=
  blockMatLoewnerLE_annealedLimitBlock_of_forall hstat hdag
    (blockMatLoewnerLE_blockSharp_annealedBlock hstat hdag hm)

/-- **The annealed limit block is positive definite.**  Its form dominates that
of the sharp of a Euclidean annealed block, which is positive definite because
that block is.  No quantitative decay of the annealed contrast is used. -/
theorem blockPosDef_annealedLimitBlock (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    Book.Ch02.BlockPosDef (annealedLimitBlock P) := by
  have hsymm : IsSymmetricBlockMat (annealedBlock P (centeredCube d (0 : ℤ))) :=
    isSymmetricBlockMat_annealedBlock P _
  have hpd := blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag (0 : ℤ)
  have hfull : (toFullBlockMat (annealedBlock P (centeredCube d (0 : ℤ)))).PosDef :=
    posDef_toFullBlockMat hsymm hpd
  have hsharpFull :
      (toFullBlockMat (blockSharp (annealedBlock P (centeredCube d (0 : ℤ))))).PosDef := by
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp hfull
  have hsharpPd :
      Book.Ch02.BlockPosDef (blockSharp (annealedBlock P (centeredCube d (0 : ℤ)))) :=
    (blockPosDef_iff_posDef
      (isSymmetricBlockMat_of_posSemidef hsharpFull.posSemidef)).mpr hsharpFull
  intro X hX
  have hle := blockMatLoewnerLE_blockSharp_annealedLimitBlock hstat hdag (m := (0 : ℤ)) le_rfl X
  have hpos := hsharpPd X hX
  linarith only [hle, hpos]

/-! ## The upper comparison from a scalar imbalance bound -/

/-- **The upper Loewner comparison against the annealed limit block, at the
annealed imbalance.**  The block lies below its imbalance times its own sharp,
and its sharp lies below the limit. -/
theorem blockMatLoewnerLE_blockScale_blockImbalance_annealedLimitBlock
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {m : ℤ} (hm : 0 ≤ m) :
    BlockMatLoewnerLE (annealedBlock P (centeredCube d m))
      (blockScale (blockImbalance (annealedBlock P (centeredCube d m)))
        (annealedLimitBlock P)) := by
  have hsymm : IsSymmetricBlockMat (annealedBlock P (centeredCube d m)) :=
    isSymmetricBlockMat_annealedBlock P _
  have hpd := blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m
  have himb1 : 1 ≤ blockImbalance (annealedBlock P (centeredCube d m)) :=
    Entry.one_le_blockImbalance_annealedBlock_centeredCube hdag m
  exact (blockMatLoewnerLE_blockScale_blockImbalance_blockSharp hsymm hpd).trans
    (blockMatLoewnerLE_blockScale_of_le (le_trans zero_le_one himb1)
      (blockMatLoewnerLE_blockSharp_annealedLimitBlock hstat hdag hm))

/-- **The upper half of the endgame block comparison follows from a scalar bound
on the annealed imbalance.** -/
theorem blockMatLoewnerLE_blockScale_annealedLimitBlock_of_blockImbalance_le
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {m : ℤ} (hm : 0 ≤ m)
    {c : ℝ} (hc : blockImbalance (annealedBlock P (centeredCube d m)) ≤ c) :
    BlockMatLoewnerLE (annealedBlock P (centeredCube d m))
      (blockScale c (annealedLimitBlock P)) :=
  (blockMatLoewnerLE_blockScale_blockImbalance_annealedLimitBlock hstat hdag hm).trans
    (blockMatLoewnerLE_blockScale_of_scalar_le hc
      (blockPosDef_annealedLimitBlock hstat hdag))

end Dagger

end

end Quenched
end HighContrast
end HCPolySupport

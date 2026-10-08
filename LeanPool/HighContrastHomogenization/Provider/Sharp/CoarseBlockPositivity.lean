/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AnnealedBlockBridge
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockOrder

/-!
# High-contrast homogenization: Provider.Sharp.CoarseBlockPositivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pathwise positivity of the coarse response, and the annealed sharp order

The variational coarse block response `𝐀(U; a)` of `s.introduction` is positive
definite along every realization of the coefficient field, on every
nondegenerate bounded open convex domain.  This is the deterministic
coarse-graining theory of such a domain read on the response: the doubled
quadratic form splits over the Schur data as

  `½ P · 𝐀(U) P = ½ p · σ(U) p + ½ r · σ_*(U)⁻¹ r`,  `r = q - κ(U) p`,

both corner matrices are positive definite -- `σ_*` because it is the Hessian
of the flux problem and `σ` because it dominates `σ_*` -- and the two halves of
the splitting vanish together only at the zero doubled vector.  Nothing beyond
nonemptiness of the domain enters, and no dimension is excluded.

The statement is recorded here in the shape the sharp order of the elementary
block bounds is stated in, over a domain of positive volume, so that the two
pathwise facts about the response can be read together.  Read together they
discharge both sample hypotheses of the annealed primal-adjoint order on the
paper's own random matrix: positive definiteness of the annealed block,
integrability of the pathwise sharp, and the annealed order `𝐀_bar(U)^♯ ≤ 𝐀_bar(U)`
itself all hold on every bounded open convex domain of positive volume, under
the printed integrability assumption `E|𝐀(U)| < ∞` alone.
-/

namespace HCPolySupport
namespace HighContrast
namespace Sharp

open MeasureTheory
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-! ## The pathwise positivity clause -/

/-- **The coarse block response is positive definite along every realization**,
on a bounded open convex domain of positive volume.  Positivity of the volume
is used only through nonemptiness of the domain, which is the sole
nondegeneracy the deterministic theory asks for. -/
theorem blockPosDef_coarseBlock_of_volume_pos {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hvol : 0 < (volume U).toReal)
    (a : CoeffSpace d) : Book.Ch02.BlockPosDef (coarseBlock U a) := by
  have hne : U.Nonempty := by
    rcases U.eq_empty_or_nonempty with rfl | hne
    · simp at hvol
    · exact hne
  exact HCPolySupport.HighContrast.blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain
    hU hne a

/-! ## The consequences for the annealed block -/

/-- **The annealed block is positive definite** on a bounded open convex domain
of positive volume, as soon as the coarse response is integrable over the law:
positivity holds at every sample and survives the expectation.  This is the
well-formedness that the annealed contrast of `e.Theta.m`
presupposes. -/
theorem blockPosDef_annealedBlock_of_volume_pos {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal) (hint : HasIntegrableCoarseBlock P U) :
    Book.Ch02.BlockPosDef (annealedBlock P U) :=
  blockPosDef_annealedBlock hint (blockPosDef_coarseBlock_of_volume_pos hU hvol)

/-! ## The annealed sharp order on the coarse response -/

/-- **The annealed primal-adjoint order**, on the coarse block response of the
paper and over a bounded open convex domain of positive volume: the annealed
block dominates its own sharp.  Both hypotheses on the sample -- pathwise
positive definiteness and the pathwise elementary block bounds -- are theorems
here, so the printed integrability assumption `E|𝐀(U)| < ∞` is the only
hypothesis on the law. -/
theorem blockSharp_annealedBlock_le_of_volume_pos {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal) (hint : HasIntegrableCoarseBlock P U) :
    BlockMatLoewnerLE (blockSharp (annealedBlock P U)) (annealedBlock P U) :=
  blockSharp_annealedBlock_le hint (blockPosDef_coarseBlock_of_volume_pos hU hvol)
    (blockMatLoewnerLE_blockSharp_coarseBlock hU hvol)

/-- **The annealed sharp order** on a nonempty bounded open convex domain: the
form in which it is consumed, the positivity of the volume being that of a
nonempty open set. -/
theorem blockSharp_annealedBlock_le_of_nonempty {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) (hint : HasIntegrableCoarseBlock P U) :
    BlockMatLoewnerLE (blockSharp (annealedBlock P U)) (annealedBlock P U) :=
  blockSharp_annealedBlock_le_of_volume_pos hU
    (ENNReal.toReal_pos (hU.isOpen.measure_pos volume hne).ne' hU.volume_lt_top.ne) hint

/-- **The annealed sharp order on the centered triadic cube** `□_m`, the carrier
the annealed contrast `Θ_m` of `e.Theta.m` is read on. -/
theorem blockSharp_annealedBlock_le_centeredCube {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (m : ℤ)
    (hint : HasIntegrableCoarseBlock P (centeredCube d m)) :
    BlockMatLoewnerLE (blockSharp (annealedBlock P (centeredCube d m)))
      (annealedBlock P (centeredCube d m)) :=
  blockSharp_annealedBlock_le_of_nonempty
    (Book.Ch02.cubeDomain (originCube d m)).isDomain
    (Book.Ch02.cubeDomain (originCube d m)).nonempty hint

end Sharp
end HighContrast
end HCPolySupport

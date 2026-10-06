/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeBlockReassembly
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockPositivity
public import LeanPool.HighContrastHomogenization.Provider.Initialization.Reference

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeReferenceComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reference block is dominated by the annealed block

The renormalization of ellipticity replaces the reference block of a
coarse-ellipticity datum by the annealed block at an inner generation, and it
converts the deviation it produces — which is measured against the reference
block — into a deviation measured against the annealed one.  That conversion is
the comparison of the reference block with the annealed one.

The comparison has a short proof on this carrier.  At its own generation the
coarse-ellipticity datum puts the coarse block below the reference block on the
event that the source has burnt in; the sharp map reverses that, and the
pathwise block bounds put the sharp of a coarse block below the block itself, so
the sharp of the reference block is below the coarse block on the same event.
Averaging costs only the probability of that event, which the source tail keeps
above one half, and the reference block is above its own sharp by the intrinsic
reference ratio.  Nothing in the argument sees a second generation, so no scale
factor survives.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The annealed block as an average of quadratic forms -/

/-- The entries of the annealed block are the integrals of the entries. -/
theorem blockMatEntry_annealedBlock (P : Measure (CoeffSpace d)) (U : Set (Vec d))
    (α β : BlockCoord d) :
    blockMatEntry (annealedBlock P U) α β =
      ∫ a, blockMatEntry (coarseBlock U a) α β ∂P := by
  cases α <;> cases β <;> rfl

/-- The quadratic form of a coarse block is integrable as soon as its entries
are. -/
theorem integrable_blockVecDot_coarseBlock {P : Measure (CoeffSpace d)}
    {U : Set (Vec d)} (hint : HasIntegrableCoarseBlock P U) (X : BlockVec d) :
    Integrable (fun a => blockVecDot X (blockMatVecMul (coarseBlock U a) X)) P := by
  have hrw : (fun a => blockVecDot X (blockMatVecMul (coarseBlock U a) X))
      = fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α *
            (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β) := by
    funext a
    exact blockVecDot_blockMatVecMul_eq_sum _ _
  rw [hrw]
  refine integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => ?_
  exact ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)

/-- **The quadratic form of the annealed block is the average of the quadratic
forms.** -/
theorem blockVecDot_annealedBlock_eq_integral {P : Measure (CoeffSpace d)}
    {U : Set (Vec d)} (hint : HasIntegrableCoarseBlock P U) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedBlock P U) X)
      = ∫ a, blockVecDot X (blockMatVecMul (coarseBlock U a) X) ∂P := by
  have hrw : (∫ a, blockVecDot X (blockMatVecMul (coarseBlock U a) X) ∂P)
      = ∫ a, ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α *
            (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β) ∂P := by
    refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
    exact blockVecDot_blockMatVecMul_eq_sum _ _
  rw [blockVecDot_blockMatVecMul_eq_sum, hrw,
    integral_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ =>
        ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finsetSum _ fun β _ =>
    ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)]
  refine Finset.sum_congr rfl fun β _ => ?_
  calc toFullBlockVec X α *
        (blockMatEntry (annealedBlock P U) α β * toFullBlockVec X β)
      = (∫ a, blockMatEntry (coarseBlock U a) α β ∂P) *
          (toFullBlockVec X α * toFullBlockVec X β) := by
        rw [blockMatEntry_annealedBlock]
        ring
    _ = ∫ a, blockMatEntry (coarseBlock U a) α β *
          (toFullBlockVec X α * toFullBlockVec X β) ∂P :=
        (integral_mul_const _ _).symm
    _ = ∫ a, toFullBlockVec X α *
          (blockMatEntry (coarseBlock U a) α β * toFullBlockVec X β) ∂P := by
        refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
        ring

/-! ## Averaging a pathwise bound over an event -/

/-- The quadratic form of a positive block is nonnegative. -/
theorem blockVecDot_nonneg_of_blockPosDef {H : BlockMat d}
    (hH : Book.Ch02.BlockPosDef H) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul H X) := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp [blockVecDot_blockMatVecMul_eq_sum, toFullBlockVec]
  · exact (hH X hX).le

/-- **A pathwise Loewner bound valid on an event survives averaging**, at the
cost of the probability of that event. -/
theorem blockMatLoewnerLE_blockScale_annealedBlock_of_ae_on
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hvol : 0 < (volume U).toReal)
    (hint : HasIntegrableCoarseBlock P U) {B : BlockMat d}
    {G : Set (CoeffSpace d)} (hGmeas : MeasurableSet G)
    (hG : ∀ᵐ a ∂P, a ∈ G → BlockMatLoewnerLE B (coarseBlock U a)) :
    BlockMatLoewnerLE (blockScale (P.real G) B) (annealedBlock P U) := by
  intro X
  rw [blockVecDot_blockMatVecMul_blockScale, blockVecDot_annealedBlock_eq_integral hint]
  have hAint := integrable_blockVecDot_coarseBlock hint X
  have hnn : ∀ a : CoeffSpace d,
      0 ≤ blockVecDot X (blockMatVecMul (coarseBlock U a) X) := fun a =>
    blockVecDot_nonneg_of_blockPosDef
      (Sharp.blockPosDef_coarseBlock_of_volume_pos hU hvol a) X
  have hind : (Set.indicator G (fun _ => blockVecDot X (blockMatVecMul B X)))
      ≤ᵐ[P] fun a => blockVecDot X (blockMatVecMul (coarseBlock U a) X) := by
    filter_upwards [hG] with a ha
    by_cases hmem : a ∈ G
    · rw [Set.indicator_of_mem hmem]
      have h := ha hmem X
      linarith only [h]
    · rw [Set.indicator_of_notMem hmem]
      exact hnn a
  have hindint : Integrable
      (Set.indicator G (fun _ => blockVecDot X (blockMatVecMul B X))) P :=
    (integrable_const _).indicator hGmeas
  have hle := integral_mono_ae hindint hAint hind
  rw [integral_indicator_const _ hGmeas, smul_eq_mul] at hle
  linarith only [hle]

/-! ## The comparison -/

/-- **The reference block is dominated by the annealed block.**  On the event
that the source has burnt in at the generation `l`, the coarse-ellipticity datum
puts the coarse block below the reference block; the sharp map reverses that and
the pathwise block bounds close the loop, so the reference block is below twice
its intrinsic reference ratio times the annealed block, as soon as the source
tail at `3^l` is at most one half. -/
theorem blockMatLoewnerLE_blockScale_annealedBlock_reference [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S) (l : ℤ)
    (hint : HasIntegrableCoarseBlock P (centeredCube d l))
    (hhalf : (Psi ((3 : ℝ) ^ l))⁻¹ ≤ 1 / 2) :
    BlockMatLoewnerLE E
      (blockScale (2 * kappaRef E) (annealedBlock P (centeredCube d l))) := by
  classical
  have hUdom : IsOpenBoundedConvexDomain (centeredCube d l) :=
    (Book.Ch02.cubeDomain (originCube d l)).isDomain
  have hvol : 0 < (volume (centeredCube d l)).toReal :=
    ENNReal.toReal_pos
      (hUdom.isOpen.measure_pos volume
        (Book.Ch02.cubeDomain (originCube d l)).nonempty).ne'
      hUdom.volume_lt_top.ne
  have hEsymm : IsSymmetricBlockMat E := hdag.refBlock_isSymm
  have hEpd : Book.Ch02.BlockPosDef E := hdag.refBlock_posDef
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hEsymm hEpd
  have hsharpFull : (toFullBlockMat (blockSharp E)).PosDef := by
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp hEfull
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_blockSharp hEsymm hEpd
  have hsharpPd : Book.Ch02.BlockPosDef (blockSharp E) :=
    (blockPosDef_iff_posDef hsharpSymm).mpr hsharpFull
  set G : Set (CoeffSpace d) := {a : CoeffSpace d | S a ≤ (3 : ℝ) ^ l} with hGdef
  have hGmeas : MeasurableSet G := by
    rw [hGdef]
    exact measurableSet_le hdag.source_measurable measurable_const
  have hGle : ∀ᵐ a ∂P, a ∈ G → BlockMatLoewnerLE (blockSharp E)
      (coarseBlock (centeredCube d l) a) := by
    filter_upwards [hdag.coarse_bound] with a ha hmem
    have hsrc : S a ≤ (3 : ℝ) ^ l := hmem
    have hcell := ha l hsrc l le_rfl 0 (standardCellCenter_zero_mem_centeredCube l l)
    rw [standardCell_zero] at hcell
    have hone : (3 : ℝ) ^ (g * ((l : ℝ) - (l : ℝ))) = 1 := by
      rw [show g * ((l : ℝ) - (l : ℝ)) = 0 by ring, Real.rpow_zero]
    rw [hone, blockScale_one] at hcell
    have hApd : Book.Ch02.BlockPosDef (coarseBlock (centeredCube d l) a) :=
      Sharp.blockPosDef_coarseBlock_of_volume_pos hUdom hvol a
    have hAsymm : IsSymmetricBlockMat (coarseBlock (centeredCube d l) a) :=
      isSymmetricBlockMat_coarseBlock _ a
    exact (blockMatLoewnerLE_blockSharp_of_le hAsymm hEsymm hApd hEpd hcell).trans
      (Sharp.blockMatLoewnerLE_blockSharp_coarseBlock hUdom hvol a)
  have hlarge : (1 : ℝ) / 2 ≤ P.real G := by
    have hpos : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
    have htail := hdag.source_tail ((3 : ℝ) ^ l) hpos
    have hcover : (Set.univ : Set (CoeffSpace d)) ⊆
        G ∪ IndependentSums.upperTailEvent S ((3 : ℝ) ^ l) := by
      intro a _
      by_cases hmem : S a ≤ (3 : ℝ) ^ l
      · exact Or.inl hmem
      · exact Or.inr (not_le.1 hmem)
    have hone : (1 : ℝ) ≤ P.real G +
        P.real (IndependentSums.upperTailEvent S ((3 : ℝ) ^ l)) := by
      have hmono := measureReal_mono (μ := P) hcover (measure_ne_top P _)
      have hunion := measureReal_union_le (μ := P) G
        (IndependentSums.upperTailEvent S ((3 : ℝ) ^ l))
      rw [probReal_univ] at hmono
      linarith only [hmono, hunion]
    linarith only [hone, htail, hhalf]
  have haverage := blockMatLoewnerLE_blockScale_annealedBlock_of_ae_on hUdom hvol hint
    hGmeas hGle
  have href := Initialization.blockMatLoewnerLE_reference_kappaRef_blockSharp hEsymm hEpd
  have hkappa : (0 : ℝ) ≤ kappaRef E :=
    le_trans zero_le_one
      (Initialization.one_le_kappaRef hEsymm hEpd (Initialization.blockMatLoewnerLE_blockSharp_reference hdag))
  intro X
  have h1 := href X
  rw [blockVecDot_blockMatVecMul_blockScale] at h1
  have h2 := haverage X
  rw [blockVecDot_blockMatVecMul_blockScale] at h2
  have hnn : 0 ≤ blockVecDot X (blockMatVecMul (blockSharp E) X) :=
    blockVecDot_nonneg_of_blockPosDef hsharpPd X
  rw [blockVecDot_blockMatVecMul_blockScale]
  set q : ℝ := blockVecDot X (blockMatVecMul (blockSharp E) X) with hqdef
  set r : ℝ := blockVecDot X
    (blockMatVecMul (annealedBlock P (centeredCube d l)) X) with hrdef
  clear_value q r
  have hstep1 : (1 / 2 : ℝ) * q ≤ P.real G * q := by nlinarith only [hnn, hlarge]
  have hstep2 : (1 / 2 : ℝ) * q ≤ r := by linarith only [h2, hstep1]
  have hstep3 : kappaRef E * ((1 / 2 : ℝ) * q) ≤ kappaRef E * r :=
    mul_le_mul_of_nonneg_left hstep2 hkappa
  linarith only [h1, hstep3]

end

end Quenched
end HighContrast
end HCPolySupport

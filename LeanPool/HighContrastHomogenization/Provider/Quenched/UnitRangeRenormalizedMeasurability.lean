/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoarseExcessMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedScale

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeRenormalizedMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of the renormalized radius

The bad cells in the one-time ellipticity rebase are scalar excess events.
Writing them in that form makes the bad generations, their countable supremum,
and the buffered radius measurable on the coefficient space.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem blockMatLoewnerLE_iff_blockExcess_le [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hUvol : 0 < (volume U).toReal) (a : CoeffSpace d)
    {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hApd : Book.Ch02.BlockPosDef A) {c : ℝ} (hc : 0 ≤ c) :
    BlockMatLoewnerLE (coarseBlock U a) (blockScale (1 + c) A) ↔
      blockExcess (coarseBlock U a) A ≤ c := by
  have hU0 : volume U ≠ 0 := by
    intro hzero
    rw [hzero] at hUvol
    simp at hUvol
  have hHsymm : IsSymmetricBlockMat (coarseBlock U a) :=
    isSymmetricBlockMat_coarseBlock U a
  have hHps : (toFullBlockMat (coarseBlock U a)).PosSemidef :=
    Transport.posSemidef_toFullBlockMat_coarseBlock hU hU0 a
  have hAfull : (toFullBlockMat A).PosDef := posDef_toFullBlockMat hA hApd
  rw [blockExcess_eq hHsymm hA hApd hHps, max_le_iff]
  constructor
  · intro hle
    have hflat :=
      (blockMatLoewnerLE_iff_le hHsymm
        (isSymmetricBlockMat_blockScale (1 + c) hA)).mp hle
    rw [toFullBlockMat_blockScale] at hflat
    have hrel : relSize (toFullBlockMat (coarseBlock U a)) (toFullBlockMat A) ≤ 1 + c :=
      (relSize_le_iff hHps hAfull (by linarith only [hc])).mpr hflat
    exact ⟨by linarith only [hrel], hc⟩
  · rintro ⟨hrel, -⟩
    apply blockMatLoewnerLE_of_le
    rw [toFullBlockMat_blockScale]
    exact (relSize_le_iff hHps hAfull (by linarith only [hc])).mp
      (by linarith only [hrel])

/-- A bad cell is measurable once the source scale is measurable and the
reference block is positive symmetric. -/
theorem measurableSet_renormBadCell [NeZero d]
    {S : CoeffSpace d → ℝ} (hS : Measurable S)
    {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hApd : Book.Ch02.BlockPosDef A) {delta rho : ℝ}
    (hdelta : 0 ≤ delta) (m k : ℤ) (w : Fin d → ℤ) :
    MeasurableSet (renormBadCell S A delta rho m k w) := by
  let U : Set (Vec d) := standardCell d k w
  have hU : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_openCubeSet (translateCube w (originCube d k))
  have hUvol : 0 < (volume U).toReal := by
    change 0 < (volume (openCubeSet (translateCube w (originCube d k)))).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos _
  have hc : 0 ≤ delta * (3 : ℝ) ^ (rho * ((m : ℝ) - (k : ℝ))) :=
    mul_nonneg hdelta (Real.rpow_nonneg (by norm_num) _)
  have heq : renormBadCell S A delta rho m k w =
      {a | S a ≤ (3 : ℝ) ^ m} ∩
        {a | delta * (3 : ℝ) ^ (rho * ((m : ℝ) - (k : ℝ))) <
          blockExcess (coarseBlock U a) A} := by
    ext a
    simp only [renormBadCell, Set.mem_ofPred_eq, Set.mem_inter_iff]
    have hiff := blockMatLoewnerLE_iff_blockExcess_le hU hUvol a hA hApd hc
    constructor
    · rintro ⟨hsource, hnot⟩
      exact ⟨hsource, lt_of_not_ge fun hexcess => hnot (hiff.mpr hexcess)⟩
    · rintro ⟨hsource, hexcess⟩
      exact ⟨hsource, fun hloewner => (not_le_of_gt hexcess) (hiff.mp hloewner)⟩
  rw [heq]
  exact (hS measurableSet_Iic).inter
    ((measurable_blockExcess_coarseBlock hU hUvol hA hApd)
      (measurableSet_Ioi))

/-- Every bad-generation event is measurable. -/
theorem measurableSet_renormBadGeneration [NeZero d]
    {S : CoeffSpace d → ℝ} (hS : Measurable S)
    {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hApd : Book.Ch02.BlockPosDef A) {delta rho : ℝ}
    (hdelta : 0 ≤ delta) (h : ℕ) (m : ℤ) :
    MeasurableSet (renormBadGeneration S A delta rho h m) := by
  rw [renormBadGeneration]
  exact Finset.measurableSet_biUnion _ fun k _ =>
    Finset.measurableSet_biUnion _ fun w _ =>
      measurableSet_renormBadCell hS hA hApd hdelta m k w

@[expose]
public noncomputable def measurableRenormScale (S : CoeffSpace d → ℝ)
    (A : BlockMat d) (delta rho : ℝ) (h n : ℕ)
    (a : CoeffSpace d) : ℝ≥0∞ := by
  classical
  exact iSup fun m : ℤ =>
    if (n : ℤ) ≤ m ∧ a ∈ renormBadGeneration S A delta rho h m then
      ENNReal.ofReal ((3 : ℝ) ^ m) else 0

private theorem measurableRenormScale_eq (S : CoeffSpace d → ℝ)
    (A : BlockMat d) (delta rho : ℝ) (h n : ℕ) :
    measurableRenormScale S A delta rho h n = renormScale S A delta rho h n := by
  classical
  funext a
  apply le_antisymm
  · refine iSup_le fun m => ?_
    split_ifs with hm
    · exact le_iSup_of_le m (le_iSup_of_le hm le_rfl)
    · exact bot_le
  · rw [renormScale]
    refine iSup_le fun m => iSup_le fun hm => ?_
    exact le_iSup_of_le m (by rw [ite_eq_left hm])

/-- The renormalized minimal scale is measurable. -/
theorem measurable_renormScale [NeZero d]
    {S : CoeffSpace d → ℝ} (hS : Measurable S)
    {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hApd : Book.Ch02.BlockPosDef A) {delta rho : ℝ}
    (hdelta : 0 ≤ delta) (h n : ℕ) :
    Measurable (renormScale S A delta rho h n) := by
  classical
  rw [← measurableRenormScale_eq S A delta rho h n]
  refine Measurable.iSup fun m => ?_
  have hbad := measurableSet_renormBadGeneration (rho := rho) hS hA hApd hdelta h m
  by_cases hnm : (n : ℤ) ≤ m
  · simpa only [measurableRenormScale, hnm, true_and] using
      (Measurable.ite (p := fun b : CoeffSpace d => b ∈ renormBadGeneration S A delta rho h m)
        hbad measurable_const measurable_const)
  · simp only [hnm, false_and, ite_false]
    exact measurable_const

/-- The buffered real-valued renormalized radius is measurable. -/
theorem measurable_renormRadius [NeZero d]
    {S : CoeffSpace d → ℝ} (hS : Measurable S)
    {A : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hApd : Book.Ch02.BlockPosDef A) {delta rho : ℝ}
    (hdelta : 0 ≤ delta) (h n : ℕ) :
    Measurable (renormRadius S A delta rho h n) := by
  exact (measurable_const.mul
    (measurable_const.max ((ENNReal.measurable_toReal.comp
      (measurable_renormScale hS hA hApd hdelta h n)))))

end

end Quenched
end HighContrast
end HCPolySupport

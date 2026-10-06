/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeInnerCells

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeCentring

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centring block of the inner cells

The concentration estimate centres each observable at its own mean, so the
renormalization argument has to identify the block of those means with the
annealed block at the inner generation.  Two facts do that.

The mean commutes with the normalization, because the normalization is a fixed
linear map of the entries.  And the annealed block of an aligned cell is the
annealed block of the centred cell of the same generation, because the law is
invariant under integer translations and the coarse block is covariant under
them.  Together they replace the mean of every inner cell by one reference
block.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The entry algebra of the difference and the scaling -/

theorem blockMatEntry_blockSub (A B : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (blockSub A B) α β = blockMatEntry A α β - blockMatEntry B α β := by
  cases α <;> cases β <;> rfl

/-! ## The mean commutes with the normalization -/

/-- **The mean commutes with the normalization.**  The normalization is a fixed
linear map of the entries, so it passes through the entrywise mean. -/
theorem meanBlock_normalizedBlock {P : Measure (CoeffSpace d)}
    {M : CoeffSpace d → BlockMat d} (E : BlockMat d) (hM : HasIntegrableBlock P M) :
    meanBlock P (fun a => normalizedBlock (M a) E) = normalizedBlock (meanBlock P M) E := by
  refine toFullBlockMat_injective ?_
  ext α β
  rw [toFullBlockMat_eq_blockMatEntry, toFullBlockMat_eq_blockMatEntry,
    blockMatEntry_meanBlock, blockMatEntry_normalizedBlock_eq_sum]
  have hint : ∀ delta gamma : BlockCoord d,
      Integrable (fun a => matSqrt (toFullBlockMat E)⁻¹ α gamma *
        (blockMatEntry (M a) gamma delta * matSqrt (toFullBlockMat E)⁻¹ delta β)) P :=
    fun delta gamma =>
      ((hM gamma delta).mul_const (matSqrt (toFullBlockMat E)⁻¹ delta β)).const_mul _
  have hrw : (∫ a, blockMatEntry (normalizedBlock (M a) E) α β ∂P)
      = ∫ a, ∑ delta : BlockCoord d, ∑ gamma : BlockCoord d,
          matSqrt (toFullBlockMat E)⁻¹ α gamma *
            (blockMatEntry (M a) gamma delta *
              matSqrt (toFullBlockMat E)⁻¹ delta β) ∂P := by
    refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun a => ?_)
    exact blockMatEntry_normalizedBlock_eq_sum (M a) E α β
  rw [hrw, integral_finsetSum _ fun delta _ =>
    integrable_finsetSum _ fun gamma _ => hint delta gamma]
  refine Finset.sum_congr rfl fun delta _ => ?_
  rw [integral_finsetSum _ fun gamma _ => hint delta gamma]
  refine Finset.sum_congr rfl fun gamma _ => ?_
  rw [blockMatEntry_meanBlock]
  rw [integral_const_mul, integral_mul_const]

/-! ## The annealed block of an aligned cell -/

/-- An aligned cell is the integer translate of the centred cell of the same
generation. -/
theorem standardCell_eq_translateSet_centeredCube {l : ℤ} (hl : 0 ≤ l)
    (u : Fin d → ℤ) :
    standardCell d l u
      = translateSet (Source.AKL.intTranslation (parentShift l u)) (centeredCube d l) := by
  rw [← standardCell_zero (d := d) l]
  refine Entry.standardCell_eq_translateSet ?_
  intro i
  have hcast : ((parentShift l u i : ℤ) : ℝ) = (u i : ℝ) * (3 : ℝ) ^ l := by
    rw [parentShift]
    push_cast
    congr 1
    rw [← zpow_natCast (3 : ℝ) l.toNat, Int.toNat_of_nonneg hl]
  rw [hcast]
  simp

/-- **The annealed block of an aligned cell is the annealed block of the centred
cell.**  Integer stationarity of the law and the covariance of the coarse block
under integer translations. -/
theorem annealedBlock_standardCell_eq_centeredCube {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} (hl : 0 ≤ l) (u : Fin d → ℤ)
    (hmeas : HasMeasurableCoarseBlock P (centeredCube d l)) :
    annealedBlock P (standardCell d l u) = annealedBlock P (centeredCube d l) := by
  refine toFullBlockMat_injective ?_
  ext α β
  rw [toFullBlockMat_eq_blockMatEntry, toFullBlockMat_eq_blockMatEntry,
    blockMatEntry_annealedBlock, blockMatEntry_annealedBlock]
  set z : Fin d → ℤ := parentShift l u with hzdef
  have hcell : standardCell d l u
      = translateSet (Source.AKL.intTranslation z) (centeredCube d l) := by
    rw [hzdef]
    exact standardCell_eq_translateSet_centeredCube hl u
  have hmap := Recurrence.map_blockMatEntry_coarseBlock_translateSet hstat hmeas z α β
  have hleft : AEMeasurable (fun a : CoeffSpace d =>
      blockMatEntry (coarseBlock (translateSet (Source.AKL.intTranslation z)
        (centeredCube d l)) a) α β) P := by
    have hrw : (fun a : CoeffSpace d =>
        blockMatEntry (coarseBlock (translateSet (Source.AKL.intTranslation z)
          (centeredCube d l)) a) α β)
        = fun a : CoeffSpace d =>
            blockMatEntry (coarseBlock (centeredCube d l) (translateCoeff z a)) α β := by
      funext a
      rw [Recurrence.coarseBlock_translateSet]
    rw [hrw]
    have hg : AEStronglyMeasurable
        (fun b : CoeffSpace d => blockMatEntry (coarseBlock (centeredCube d l) b) α β)
        (Measure.map (translateCoeff z) P) := by
      rw [hstat z]
      exact hmeas α β
    exact (hg.comp_measurable (measurable_translateCoeff z)).aemeasurable
  have hright : AEMeasurable
      (fun a : CoeffSpace d => blockMatEntry (coarseBlock (centeredCube d l) a) α β) P :=
    (hmeas α β).aemeasurable
  have hidL := MeasureTheory.integral_map (φ := fun a : CoeffSpace d =>
      blockMatEntry (coarseBlock (translateSet (Source.AKL.intTranslation z)
        (centeredCube d l)) a) α β) (f := fun x : ℝ => x) hleft
    aestronglyMeasurable_id
  have hidR := MeasureTheory.integral_map (φ := fun a : CoeffSpace d =>
      blockMatEntry (coarseBlock (centeredCube d l) a) α β) (f := fun x : ℝ => x) hright
    aestronglyMeasurable_id
  rw [hcell]
  rw [← hidL, ← hidR, hmap]

/-! ## The prefactor of the reassembly is absorbed by a shift -/

/-- The dimensional shift absorbing the reassembly's prefactor. -/
@[expose]
def renormShift (d : ℕ) : ℝ := Real.log (4 * (d : ℝ) ^ 2 + 1) / (2 * frGaugeConst d)

theorem renormShift_nonneg (d : ℕ) : 0 ≤ renormShift d := by
  refine div_nonneg (Real.log_nonneg ?_) ?_
  · nlinarith only [sq_nonneg ((d : ℝ))]
  · have := (frGaugeConst_pos d).le
    linarith only [this]

/-- **The prefactor of the reassembly is absorbed by shifting the parameter.** -/
theorem prefactor_absorb (d : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    (2 * (d : ℝ)) ^ 2 * (frGauge d (t + renormShift d))⁻¹ ≤ (frGauge d t)⁻¹ := by
  have hc : 0 < frGaugeConst d := frGaugeConst_pos d
  have hs : 0 ≤ renormShift d := renormShift_nonneg d
  have hpos : (0 : ℝ) < 4 * (d : ℝ) ^ 2 + 1 := by positivity
  have hlogeq : Real.log (4 * (d : ℝ) ^ 2 + 1) = 2 * frGaugeConst d * renormShift d := by
    rw [renormShift, mul_div_cancel₀]
    exact ne_of_gt (by linarith only [hc])
  have hsq : (2 * (d : ℝ)) ^ 2 ≤ 4 * (d : ℝ) ^ 2 + 1 := by nlinarith only [sq_nonneg ((d : ℝ))]
  have hmul : (2 * (d : ℝ)) ^ 2 * (frGauge d (t + renormShift d))⁻¹ ≤
      (4 * (d : ℝ) ^ 2 + 1) * (frGauge d (t + renormShift d))⁻¹ :=
    mul_le_mul_of_nonneg_right hsq (inv_pos.2 (frGauge_pos d _)).le
  refine hmul.trans ?_
  rw [inv_frGauge, inv_frGauge]
  have hexp : (4 * (d : ℝ) ^ 2 + 1) *
      Real.exp (-(frGaugeConst d * (t + renormShift d) ^ 2))
      = Real.exp (Real.log (4 * (d : ℝ) ^ 2 + 1)
        - frGaugeConst d * (t + renormShift d) ^ 2) := by
    rw [Real.exp_sub, Real.exp_log hpos, div_eq_mul_inv, Real.exp_neg]
  rw [hexp]
  refine Real.exp_le_exp.2 ?_
  have hgap : Real.log (4 * (d : ℝ) ^ 2 + 1) ≤
      frGaugeConst d * (t + renormShift d) ^ 2 - frGaugeConst d * t ^ 2 := by
    rw [hlogeq]
    have hexpand : frGaugeConst d * (t + renormShift d) ^ 2 - frGaugeConst d * t ^ 2
        = frGaugeConst d * (2 * t * renormShift d + renormShift d ^ 2) := by ring
    rw [hexpand]
    have h1 : 0 ≤ renormShift d * (t - 1) := mul_nonneg hs (by linarith only [ht])
    have h3 : 0 ≤ frGaugeConst d * (renormShift d * (t - 1)) := mul_nonneg hc.le h1
    have h4 : 0 ≤ frGaugeConst d * renormShift d ^ 2 :=
      mul_nonneg hc.le (sq_nonneg _)
    nlinarith only [h3, h4]
  linarith only [hgap]

/-! ## The normalization is linear -/

/-- The normalization passes through a difference. -/
theorem normalizedBlock_blockSub (A B E : BlockMat d) :
    normalizedBlock (blockSub A B) E
      = blockSub (normalizedBlock A E) (normalizedBlock B E) := by
  refine toFullBlockMat_injective ?_
  rw [Recurrence.toFullBlockMat_normalizedBlock_blockSub, Recurrence.toFullBlockMat_blockSub,
    Recurrence.toFullBlockMat_normalizedBlock, Recurrence.toFullBlockMat_normalizedBlock]

/-- The normalization passes through an average. -/
theorem normalizedBlock_avgBlockOf {ι : Type*} (Z : Finset ι) (M : ι → BlockMat d)
    (E : BlockMat d) :
    normalizedBlock (avgBlockOf Z M) E
      = avgBlockOf Z fun t => normalizedBlock (M t) E := by
  refine toFullBlockMat_injective ?_
  rw [Recurrence.toFullBlockMat_normalizedBlock, toFullBlockMat_avgBlockOf,
    toFullBlockMat_avgBlockOf, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Recurrence.toFullBlockMat_normalizedBlock]

end

end Quenched
end HighContrast
end HCPolySupport

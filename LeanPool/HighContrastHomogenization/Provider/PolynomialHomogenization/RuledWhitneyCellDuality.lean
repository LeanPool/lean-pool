/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

/- Fractional duality on the cells of an enlarged-margin ruled carrier. -/

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledWhitneyRowCauchySchwarz
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyPositiveRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CompactTestDensity
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NegativeSobolevCubeDuality

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledWhitneyCellDuality

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The inverse fractional side-length weight used internally by the ruled
one-cell duality calculation. -/
@[expose]
public def scaleWeight
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (i : system.CellIndex) : ℝ≥0∞ :=
  ENNReal.ofReal (((3 : ℝ) ^ system.scale i) ^ (-2 * s))

/-- The expanded positive fractional square used internally by the ruled
one-cell duality calculation. -/
@[expose]
public def positiveWhitneyCellEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : Vec d → Vec d) (i : system.CellIndex) : ℝ≥0∞ :=
  (volume (system.cell i))⁻¹ *
    (scaleWeight system s i *
        ∫⁻ x in system.cell i,
          ENNReal.ofReal (vecNormSq (F x)) ∂volume +
      ∫⁻ z in system.cell i ×ˢ system.cell i,
        whitneyRowFractionalKernel s F z ∂(volume.prod volume))

private theorem aemeasurable_whitneyCellFractionalKernel
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict (system.cell i)))
    {s : ℝ} (hs : 0 ≤ s) :
    AEMeasurable (whitneyRowFractionalKernel s F)
      ((volume.prod volume).restrict
        (system.cell i ×ˢ system.cell i)) := by
  rw [← Measure.prod_restrict]
  have hsub : AEMeasurable
      (fun z : Vec d × Vec d => F z.1 - F z.2)
      ((volume.restrict (system.cell i)).prod
        (volume.restrict (system.cell i))) :=
    hF.aestronglyMeasurable.aemeasurable.comp_fst.sub
      hF.aestronglyMeasurable.aemeasurable.comp_snd
  have hnum : AEMeasurable
      (fun z : Vec d × Vec d => vecNormSq (F z.1 - F z.2))
      ((volume.restrict (system.cell i)).prod
        (volume.restrict (system.cell i))) :=
    continuous_vecNormSq.measurable.comp_aemeasurable hsub
  have hp : 0 ≤ (d : ℝ) + 2 * s := by
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  have hdist : Continuous
      (fun z : Vec d × Vec d =>
        Real.sqrt (vecNormSq (z.1 - z.2))) :=
    (continuous_vecNormSq.comp (continuous_fst.sub continuous_snd)).sqrt
  have hden : Measurable
      (fun z : Vec d × Vec d =>
        Real.sqrt (vecNormSq (z.1 - z.2)) ^ ((d : ℝ) + 2 * s)) :=
    (hdist.rpow_const fun _ => Or.inr hp).measurable
  exact (hnum.div hden.aemeasurable).ennreal_ofReal

private theorem volume_whitneyCell_eq_ofReal
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    volume (system.cell i) =
      ENNReal.ofReal (((3 : ℝ) ^ system.scale i) ^ d) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (volume_openCubeSet_lt_top
      (translateCube (system.index i) (originCube d (system.scale i)))).ne
    ENNReal.ofReal_ne_top).mp
  rw [volume_openCubeSet_toReal,
    ENNReal.toReal_ofReal
      (by positivity : 0 ≤ ((3 : ℝ) ^ system.scale i) ^ d),
    cubeVolume_eq_pow_scale]
  simp only [translateCube, originCube]

private theorem whitneyCell_hsScale_eq_scaleWeight
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    volume (system.cell i) ^ (-(2 * s) / (d : ℝ)) =
      scaleWeight system s i := by
  let r : ℝ := (3 : ℝ) ^ system.scale i
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  rw [volume_whitneyCell_eq_ofReal system i,
    ENNReal.ofReal_rpow_of_pos (pow_pos hr d)]
  unfold scaleWeight
  apply congrArg ENNReal.ofReal
  change (r ^ d) ^ (-(2 * s) / (d : ℝ)) = r ^ (-2 * s)
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hr.le]
  congr 1
  field_simp

/-- On a Whitney cell, the expanded positive square is exactly the normalized
fractional Sobolev norm square. -/
theorem hsNormSq_whitneyCell_eq_positiveWhitneyCellEnergy
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict (system.cell i)))
    (hs : 0 ≤ s) :
    hsNormSq (system.cell i) s F =
      positiveWhitneyCellEnergy system s F i := by
  have hpair :
      (∫⁻ z in system.cell i ×ˢ system.cell i,
          whitneyRowFractionalKernel s F z ∂(volume.prod volume)) =
        ∫⁻ x in system.cell i, ∫⁻ y in system.cell i,
          whitneyRowFractionalKernel s F (x, y) ∂volume := by
    exact setLIntegral_prod _
      (aemeasurable_whitneyCellFractionalKernel system i hF hs)
  unfold hsNormSq fracSeminormSq eVolumeAverage
    positiveWhitneyCellEnergy
  rw [whitneyCell_hsScale_eq_scaleWeight hd system i, hpair]
  unfold whitneyRowFractionalKernel
  simp only [ENNReal.div_eq_inv_mul]
  rw [mul_add]
  ac_rfl

/-- The negative square used in the Whitney-row Cauchy--Schwarz estimate. -/
@[expose]
def negativeWhitneyCellEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : Vec d → Vec d) (i : system.CellIndex) : ℝ≥0∞ :=
  negSobolevNorm (system.cell i) s F ^ (2 : ℝ)

/-- Below the trace threshold, the normalized pairing on one Whitney cell is
bounded by its negative and positive fractional squares. -/
theorem ofReal_abs_volumeAverage_vecDot_le_cellDuality
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F G : Vec d → Vec d)
    (hF : MemLp F 2 (volume.restrict (system.cell i)))
    (hG : Integrable G (volume.restrict (system.cell i)))
    (hGfinite : hsNormSq (system.cell i) s G ≠ ⊤) :
    ENNReal.ofReal
        |volumeAverage (system.cell i) (fun x => vecDot (F x) (G x))| ≤
      (negativeWhitneyCellEnergy system s F i) ^ (1 / 2 : ℝ) *
        (positiveWhitneyCellEnergy system s G i) ^ (1 / 2 : ℝ) := by
  let Q : TriadicCube d :=
    translateCube (system.index i) (originCube d (system.scale i))
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd)⟩
  have hdual :=
    ofReal_abs_volumeAverage_le_sqrt_hsNormSq_mul_negSobolevNorm
      Q hs hsHalf F G hF hG.aestronglyMeasurable hGfinite
  have hpositive :=
    hsNormSq_whitneyCell_eq_positiveWhitneyCellEnergy
      hd system i hG hs.le
  have hnegative :
      (negativeWhitneyCellEnergy system s F i) ^ (1 / 2 : ℝ) =
        negSobolevNorm (system.cell i) s F := by
    unfold negativeWhitneyCellEnergy
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hnegative, ← hpositive]
  simpa only [mul_comm] using! hdual

end

end HighContrast
end HCPolySupport

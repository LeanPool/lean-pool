/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledPairingSplit
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledHardyPositiveRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledWhitneyPhysicalDualRHSRow

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledPairingAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pairing aggregation over ruled Whitney cells

The exact ruled-cell decomposition and countable Cauchy--Schwarz estimate
combine the local negative and positive fractional squares.  The negative
row is then priced by the physical full-dual row.  Exact disjointness leaves
the supplied positive-row coefficient unchanged.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The negative fractional square of a ruled-cell-indexed field. -/
@[expose]
def negativeWhitneyFamilyCellEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : system.CellIndex → Vec d → Vec d)
    (i : system.CellIndex) : ℝ≥0∞ :=
  negSobolevNorm (system.cell i) s (F i) ^ (2 : ℝ)

/-- The physical full-dual Besov square of a ruled-cell-indexed field. -/
@[expose]
def physicalFullDualWhitneyFamilyCellEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) (s : ℝ)
    (F : system.CellIndex → Vec d → Vec d)
    (i : system.CellIndex) : ℝ≥0∞ :=
  ENNReal.ofReal
      (physicalFullDualBesovVectorNorm (whitneyCellCube system i) s (F i)) ^ 2

/-- Cellwise fractional duality for a ruled family of local negative fields
tested against one global positive field. -/
theorem ofReal_abs_volumeAverage_vecDot_le_familyCellDuality
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : system.CellIndex → Vec d → Vec d) (G : Vec d → Vec d)
    (hF : MemLp (F i) 2 (volume.restrict (system.cell i)))
    (hG : Integrable G (volume.restrict (system.cell i)))
    (hGfinite : hsNormSq (system.cell i) s G ≠ ∞) :
    ENNReal.ofReal
        |volumeAverage (system.cell i) (fun x => vecDot (F i x) (G x))| ≤
      (negativeWhitneyFamilyCellEnergy system s F i) ^ (1 / 2 : ℝ) *
        (ruledPositiveWhitneyCellEnergy system s G i) ^ (1 / 2 : ℝ) := by
  simpa only [negativeWhitneyFamilyCellEnergy, negativeWhitneyCellEnergy] using!
    ofReal_abs_volumeAverage_vecDot_le_cellDuality
      hd system i hs hsHalf (F i) G hF hG hGfinite

private theorem ofReal_volume_toReal_inv
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U ≠ ∞) :
    ENNReal.ofReal (volume U).toReal⁻¹ = (volume U)⁻¹ := by
  have hreal : 0 < (volume U).toReal :=
    (ENNReal.toReal_pos_iff).2 ⟨hUpos, lt_top_iff_ne_top.mpr hUtop⟩
  rw [ENNReal.ofReal_inv_of_pos hreal, ENNReal.ofReal_toReal hUtop]

private theorem inv_mul_half_products
    (v N P : ℝ≥0∞) :
    v⁻¹ * (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) =
      (v⁻¹ * N) ^ (1 / 2 : ℝ) *
        (v⁻¹ * P) ^ (1 / 2 : ℝ) := by
  have hv : (v⁻¹) ^ (1 / 2 : ℝ) * (v⁻¹) ^ (1 / 2 : ℝ) = v⁻¹ := by
    rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
      (by norm_num) (by norm_num)]
    norm_num
  calc
    v⁻¹ * (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) =
        ((v⁻¹) ^ (1 / 2 : ℝ) * (v⁻¹) ^ (1 / 2 : ℝ)) *
          (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) :=
      congrArg (fun z => z *
        (N ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ))) hv.symm
    _ = ((v⁻¹) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) *
        ((v⁻¹) ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ)) := by
      ac_rfl
    _ = (v⁻¹ * N) ^ (1 / 2 : ℝ) *
        (v⁻¹ * P) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]

/-- Normalized constant-one Cauchy--Schwarz aggregation over the ruled
Whitney decomposition. -/
theorem ofReal_abs_volumeAverage_le_normalizedWhitneyRow_cauchySchwarz
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hd : 1 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hUpos : 0 < volume U) (hUtop : volume U ≠ ∞)
    {f : Vec d → ℝ} (hf : IntegrableOn f U volume)
    (N P : system.CellIndex → ℝ≥0∞)
    (hcell : ∀ i : system.CellIndex,
      ENNReal.ofReal |volumeAverage (system.cell i) f| ≤
        N i ^ (1 / 2 : ℝ) * P i ^ (1 / 2 : ℝ)) :
    ENNReal.ofReal |volumeAverage U f| ≤
      (normalizedWhitneyRowEnergy system N) ^ (1 / 2 : ℝ) *
        (normalizedWhitneyRowEnergy system P) ^ (1 / 2 : ℝ) := by
  have hraw := ofReal_abs_volumeAverage_le_whitneyRow_cauchySchwarz
    system hd hU hf N P hcell
  unfold normalizedWhitneyRowEnergy
  rw [← inv_mul_half_products]
  rw [← ofReal_volume_toReal_inv hUpos hUtop]
  exact hraw

/-- The complete ruled negative row is bounded by the physical full-dual row
with the finite dimension-only density coefficient. -/
theorem normalizedNegativeWhitneyFamilyRow_le_fullDualRow
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : system.CellIndex → Vec d → Vec d)
    (hF : ∀ i, MemVectorL2 (system.cell i) (F i)) :
    normalizedWhitneyRowEnergy system
        (negativeWhitneyFamilyCellEnergy system s F) ≤
      (fractionalDualToBesovConstant d) ^ (2 : ℕ) *
        normalizedWhitneyRowEnergy system
          (physicalFullDualWhitneyFamilyCellEnergy system s F) := by
  unfold normalizedWhitneyRowEnergy rawWhitneyRowEnergy
  let K : ℝ≥0∞ := (fractionalDualToBesovConstant d) ^ (2 : ℕ)
  have hpoint : ∀ i : system.CellIndex,
      volume (system.cell i) * negativeWhitneyFamilyCellEnergy system s F i ≤
        K * (volume (system.cell i) *
          physicalFullDualWhitneyFamilyCellEnergy system s F i) := by
    intro i
    have hi := negativeWhitneyCellEnergy_le_fullDual
      hd system i hs hsHalf (F i) (hF i)
    rw [show negativeWhitneyFamilyCellEnergy system s F i =
        negativeWhitneyCellEnergy system s (F i) i by rfl]
    calc
      volume (system.cell i) * negativeWhitneyCellEnergy system s (F i) i ≤
          volume (system.cell i) *
            (K * physicalFullDualWhitneyFamilyCellEnergy system s F i) := by
              simpa only [mul_comm] using!
                (mul_le_mul_right hi (volume (system.cell i)))
      _ = K * (volume (system.cell i) *
            physicalFullDualWhitneyFamilyCellEnergy system s F i) := by
          ac_rfl
  calc
    (volume U)⁻¹ * ∑' i : system.CellIndex,
        volume (system.cell i) * negativeWhitneyFamilyCellEnergy system s F i ≤
      (volume U)⁻¹ * ∑' i : system.CellIndex,
        K * (volume (system.cell i) *
          physicalFullDualWhitneyFamilyCellEnergy system s F i) := by
            simpa only [mul_comm] using
              (mul_le_mul_right (ENNReal.tsum_le_tsum hpoint) (volume U)⁻¹)
    _ = (volume U)⁻¹ *
        (K * ∑' i : system.CellIndex,
          volume (system.cell i) *
            physicalFullDualWhitneyFamilyCellEnergy system s F i) := by
      rw [ENNReal.tsum_mul_left]
    _ = K * ((volume U)⁻¹ * ∑' i : system.CellIndex,
          volume (system.cell i) *
            physicalFullDualWhitneyFamilyCellEnergy system s F i) := by
      ac_rfl

/-- The ruled physical full-dual negative row and a supplied positive Hardy
row control the normalized domain pairing.  Exact disjointness preserves the
Hardy coefficient `C` without an overlap multiplier. -/
theorem ofReal_abs_volumeAverage_vecDot_le_fullDualWhitneyRow_mul_hs
    (hd : 1 ≤ d) {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U)
    (hUpos : 0 < volume U) (hUtop : volume U ≠ ∞)
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : system.CellIndex → Vec d → Vec d)
    (G : Vec d → Vec d) (f : Vec d → ℝ)
    (hf : IntegrableOn f U volume)
    (hpair : ∀ i, volumeAverage (system.cell i) f =
      volumeAverage (system.cell i) (fun x => vecDot (F i x) (G x)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (system.cell i)))
    (hG : ∀ i, Integrable G (volume.restrict (system.cell i)))
    (hGfinite : ∀ i, hsNormSq (system.cell i) s G ≠ ∞)
    {C : ℝ≥0∞}
    (hHardy : normalizedWhitneyRowEnergy system
        (ruledPositiveWhitneyCellEnergy system s G) ≤ C * hsNormSq U s G) :
    ENNReal.ofReal |volumeAverage U f| ≤
      ((fractionalDualToBesovConstant d) ^ (2 : ℕ) *
        normalizedWhitneyRowEnergy system
          (physicalFullDualWhitneyFamilyCellEnergy system s F)) ^
          (1 / 2 : ℝ) *
        (C * hsNormSq U s G) ^ (1 / 2 : ℝ) := by
  have hcell : ∀ i : system.CellIndex,
      ENNReal.ofReal |volumeAverage (system.cell i) f| ≤
        (negativeWhitneyFamilyCellEnergy system s F i) ^ (1 / 2 : ℝ) *
          (ruledPositiveWhitneyCellEnergy system s G i) ^ (1 / 2 : ℝ) := by
    intro i
    rw [hpair i]
    exact ofReal_abs_volumeAverage_vecDot_le_familyCellDuality
      hd system i hs hsHalf F G (hF i) (hG i) (hGfinite i)
  have hrows := ofReal_abs_volumeAverage_le_normalizedWhitneyRow_cauchySchwarz
    system hd hU hUpos hUtop hf
      (negativeWhitneyFamilyCellEnergy system s F)
      (ruledPositiveWhitneyCellEnergy system s G) hcell
  have hnegative := normalizedNegativeWhitneyFamilyRow_le_fullDualRow
    hd system hs hsHalf F hF
  exact hrows.trans (mul_le_mul
    (ENNReal.rpow_le_rpow hnegative (by norm_num))
    (ENNReal.rpow_le_rpow hHardy (by norm_num)) bot_le bot_le)

end

end HighContrast
end HCPolySupport

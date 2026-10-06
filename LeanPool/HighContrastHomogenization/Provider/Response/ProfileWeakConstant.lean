/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormGeometric

/-!
# High-contrast homogenization: Provider.Response.ProfileWeakConstant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant fields in the scale-average seminorm

The normalized seminorm of a constant doubled vector is its Euclidean length
times the geometric scale sum.  This identifies exactly the constant
contribution that appears when a random cell average is replaced by its
annealed center.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A constant doubled field has the same average on every adapted cell. -/
theorem blockCellAverage_const_adapted {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (z : Fin d → ℤ) (c : BlockVec d) :
    blockCellAverage (adaptedCellAt q k z) (fun _ ↦ c) = c := by
  have hU := Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k z
  have hvol : (volume (adaptedCellAt q k z)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (Recurrence.volume_adaptedCellAt_pos hq k z).ne'
      hU.volume_lt_top.ne).ne'
  refine Prod.ext ?_ ?_
  · funext i
    exact volumeAverage_const hvol
  · funext i
    exact volumeAverage_const hvol

/-- The half-order scale weights sum to the constant coefficient. -/
theorem tsum_rpow_three_neg_half_eq_constantSeminormCoefficient :
    ∑' j : ℕ, (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) =
      constantSeminormCoefficient := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hrle : (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - (1 / 2 : ℝ) / 2 :=
    rpow_three_neg_le (by norm_num) (by norm_num)
  have hr1 : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    linarith only [hrle]
  calc
    ∑' j : ℕ, (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) =
        ∑' j : ℕ, ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ j :=
      tsum_congr fun j ↦ rpow_three_neg_natCast (1 / 2 : ℝ) j
    _ = (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ :=
      tsum_geometric_of_lt_one hr0 hr1
    _ = constantSeminormCoefficient := by
      rw [constantSeminormCoefficient_eq]
      congr 2
      ring_nf

/-- The exact normalized seminorm of a constant doubled field. -/
theorem normalized_adaptedWeakSeminorm_const {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (c : BlockVec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
        adaptedWeakSeminorm q t (1 / 2) (fun _ ↦ c) =
      ENNReal.ofReal constantSeminormCoefficient *
        ENNReal.ofReal (Real.sqrt (blockVecDot c c)) := by
  rw [ofReal_rpow_mul_adaptedWeakSeminorm]
  have hroot0 : 0 ≤ Real.sqrt (blockVecDot c c) := Real.sqrt_nonneg _
  have hweight0 : ∀ j : ℕ,
      0 ≤ (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) :=
    fun j ↦ Real.rpow_nonneg (by norm_num) _
  have hsumm : Summable fun j : ℕ ↦
      (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) :=
    summable_rpow_three_neg (by norm_num) (by norm_num)
  simp_rw [show ∀ j : ℕ,
      blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
          (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
            (fun _ ↦ c)) = Real.sqrt (blockVecDot c c) by
    intro j
    have hjt : t - (j : ℤ) ≤ t := by omega
    have hZ := alignedIndex_nonempty hq hjt
    rw [blockAvsumL2_eq]
    simp_rw [blockCellAverage_const_adapted hq]
    rw [avsum_const hZ]]
  calc
    ∑' j : ℕ, ENNReal.ofReal
        ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
          Real.sqrt (blockVecDot c c)) =
        ∑' j : ℕ, ENNReal.ofReal
          ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ)))) *
            ENNReal.ofReal (Real.sqrt (blockVecDot c c)) := by
      apply tsum_congr
      intro j
      rw [ENNReal.ofReal_mul (hweight0 j)]
    _ = (∑' j : ℕ, ENNReal.ofReal
          ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))))) *
            ENNReal.ofReal (Real.sqrt (blockVecDot c c)) :=
      ENNReal.tsum_mul_right
    _ = ENNReal.ofReal (∑' j : ℕ,
          (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ)))) *
            ENNReal.ofReal (Real.sqrt (blockVecDot c c)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hweight0 hsumm]
    _ = ENNReal.ofReal constantSeminormCoefficient *
          ENNReal.ofReal (Real.sqrt (blockVecDot c c)) := by
      rw [tsum_rpow_three_neg_half_eq_constantSeminormCoefficient]

/-- The exact constant-field identity in the canonical diagonal metric. -/
theorem normalized_adaptedWeakSeminorm_blockDiag_const {q : Mat d}
    (hq : q.PosDef) {m : Mat d} (hm : m.PosDef) (t : ℤ) (c : BlockVec d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
        adaptedWeakSeminorm q t (1 / 2) (fun _ ↦
          blockMatVecMul (blockDiag (matSqrt m) (matSqrt m)⁻¹) c) =
      ENNReal.ofReal constantSeminormCoefficient *
        ENNReal.ofReal (Real.sqrt (metricBlockNormSq m c)) := by
  rw [normalized_adaptedWeakSeminorm_const hq]
  have hspec := matSqrt_spec hm.posSemidef
  have hsymm : matTranspose (matSqrt m) = matSqrt m := by
    show (matSqrt m).transpose = matSqrt m
    rw [← conjTranspose_eq_transpose' (matSqrt m)]
    exact hspec.1.isHermitian
  rw [blockVecDot_self_blockDiag_root hsymm hspec.2]

end

end HCPolySupport.HighContrast.Response

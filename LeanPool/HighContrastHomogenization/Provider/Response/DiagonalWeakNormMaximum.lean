/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormComparison

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormMaximum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The all-scale response maximum

This file turns the extended-real maximum of the diagonal weak estimate into
pointwise real bounds whenever that maximum is finite.  The extended-real
carrier retains the divergent branch rather than assigning it a favourable
real value.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A positive response has size at most one plus its excess above the
reference block. -/
theorem blockSize_le_one_add_blockExcess {A E : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hApsd : (toFullBlockMat A).PosSemidef)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    blockSize A E ≤ 1 + blockExcess A E := by
  rw [blockSize_eq_relSize hA hE hEpd hApsd,
    blockExcess_eq hA hE hEpd hApsd]
  linarith only [le_max_left (relSize (toFullBlockMat A) (toFullBlockMat E) - 1) 0]

/-- The excess of a positive response is nonnegative. -/
theorem blockExcess_nonneg {A E : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hApsd : (toFullBlockMat A).PosSemidef)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    0 ≤ blockExcess A E := by
  rw [blockExcess_eq hA hE hEpd hApsd]
  exact le_max_right _ _

/-- Taking square roots in the size--excess comparison leaves the convenient
majorant `1 + √excess`. -/
theorem sqrt_blockSize_le_one_add_sqrt_blockExcess {A E : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hApsd : (toFullBlockMat A).PosSemidef)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    Real.sqrt (blockSize A E) ≤ 1 + Real.sqrt (blockExcess A E) := by
  have hexc0 := blockExcess_nonneg hA hApsd hE hEpd
  have hsqrt0 := Real.sqrt_nonneg (blockExcess A E)
  have hsq : (1 + Real.sqrt (blockExcess A E)) ^ 2 =
      1 + blockExcess A E + 2 * Real.sqrt (blockExcess A E) := by
    calc
      (1 + Real.sqrt (blockExcess A E)) ^ 2 =
          1 + Real.sqrt (blockExcess A E) ^ 2 +
            2 * Real.sqrt (blockExcess A E) := by ring
      _ = 1 + blockExcess A E + 2 * Real.sqrt (blockExcess A E) := by
        rw [Real.sq_sqrt hexc0]
  rw [Real.sqrt_le_iff]
  constructor
  · linarith only [hsqrt0]
  · rw [hsq]
    exact (blockSize_le_one_add_blockExcess hA hApsd hE hEpd).trans
      (by linarith only [hsqrt0])

/-- On the finite branch, every weighted cell excess is bounded by the real
value of the extended maximum. -/
theorem weighted_excess_le_diagonalWeakMaximum_toReal
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t k : ℤ} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
        blockExcess (adaptedResponse q k w a) E ≤
      (diagonalWeakMaximum rho q t E a).toReal := by
  have h := weighted_excess_le_diagonalWeakMaximum rho q t k E a hkt w hw
  have hterm0 : 0 ≤
      (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
        blockExcess (adaptedResponse q k w a) E := by
    refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
    exact blockExcess_nonneg
      (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a)
      (posDef_toFullBlockMat
        (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a)
        (Recurrence.blockPosDef_adaptedResponse hq k w a)).posSemidef
      hE hEpd
  have hreal := ENNReal.toReal_mono hfinite h
  rwa [ENNReal.toReal_ofReal hterm0] at hreal

/-- Removing the maximum's weight costs the reciprocal geometric factor. -/
theorem blockExcess_le_mul_rpow_of_weighted_le {rho B : ℝ} {t k : ℤ}
    {e : ℝ} (hweighted :
      (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) * e ≤ B) :
    e ≤ B * (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) := by
  have hfac0 : 0 ≤ (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hcancel :
      (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) *
          (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
    simp
  calc
    e = (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) *
          ((3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) * e) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) * B :=
      mul_le_mul_of_nonneg_left hweighted hfac0
    _ = B * (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) := mul_comm _ _

/-- The square root of a cell excess inherits half of the maximum's geometric
weight. -/
theorem sqrt_blockExcess_le_sqrt_mul_rpow_of_weighted_le
    {rho B : ℝ} {t k : ℤ} {e : ℝ} (hB : 0 ≤ B)
    (hweighted :
      (3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) * e ≤ B) :
    Real.sqrt e ≤ Real.sqrt B *
      (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) := by
  have hrootB0 := Real.sqrt_nonneg B
  have hfac0 : 0 ≤
      (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hfacSq :
      ((3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)) ^ 2 =
        (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg hrootB0 hfac0
  · calc
      e ≤ B * (3 : ℝ) ^ (rho * ((t : ℝ) - (k : ℝ))) :=
        blockExcess_le_mul_rpow_of_weighted_le hweighted
      _ = (Real.sqrt B *
          (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hB, hfacSq]

/-- A finite all-scale maximum controls the square root of every normalized
response block. -/
theorem sqrt_blockSize_adaptedResponse_le_of_maximum_finite
    {rho : ℝ} {q : Mat d} (hq : q.PosDef) {t k : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {a : CoeffSpace d} (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    Real.sqrt (blockSize (adaptedResponse q k w a) E) ≤
      1 + Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
        (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) := by
  have hAsymm := Recurrence.isSymmetricBlockMat_adaptedResponse q k w a
  have hApsd := (posDef_toFullBlockMat hAsymm
    (Recurrence.blockPosDef_adaptedResponse hq k w a)).posSemidef
  have hM0 : 0 ≤ (diagonalWeakMaximum rho q t E a).toReal := ENNReal.toReal_nonneg
  calc
    Real.sqrt (blockSize (adaptedResponse q k w a) E) ≤
        1 + Real.sqrt (blockExcess (adaptedResponse q k w a) E) :=
      sqrt_blockSize_le_one_add_sqrt_blockExcess hAsymm hApsd hE hEpd
    _ ≤ 1 + Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
        (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) := by
      simpa only [add_comm] using add_le_add_left
        (sqrt_blockExcess_le_sqrt_mul_rpow_of_weighted_le hM0
          (weighted_excess_le_diagonalWeakMaximum_toReal hq hE hEpd
            hkt hw hfinite)) 1

end

end Response
end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormCentering
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormSummation

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormBad

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The all-scale bad branch of the diagonal weak estimate

When the response maximum exceeds the threshold, the single-scale energy
bound is summable over every scale.  The extended-real seminorm is therefore
controlled by the bad-event geometric majorant.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- On the branch where the response maximum exceeds `delta`, the normalized
weak seminorm of the centered canonical state has the all-scale bound. -/
theorem normalized_adaptedWeakSeminorm_bad_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hbad : delta < (diagonalWeakMaximum rho q t E a).toReal) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
      ENNReal.ofReal
        ((Real.sqrt 2 * diagonalWeakMetricFactor m E *
            diagonalWeakEnergy hq t a p r) *
          (8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
            Real.sqrt (diagonalWeakMaximum rho q t E a).toReal)) := by
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let C : ℝ := Real.sqrt 2 * diagonalWeakMetricFactor m E *
    diagonalWeakEnergy hq t a p r
  let b : ℕ → ℝ := fun j => C *
    ((3 : ℝ) ^ (-(s * (j : ℝ))) +
      Real.sqrt M *
        (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))))
  have hC0 : 0 ≤ C := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (diagonalWeakMetricFactor_nonneg m E))
      (diagonalWeakEnergy_nonneg hq t a p r)
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    exact mul_nonneg hC0 (add_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)))
  have hs0 : 0 < s := lt_trans (by linarith only [hrho]) hs
  have ha0 : 0 < s - rho / 2 := by linarith only [hs]
  have ha1 : s - rho / 2 ≤ 1 := by linarith only [hs1, hrho]
  have hsummS := summable_rpow_three_neg hs0 hs1
  have hsummA := summable_rpow_three_neg ha0 ha1
  have hsummMA : Summable fun j : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) :=
    hsummA.mul_left _
  have hbsum : Summable b := by
    exact (hsummS.add hsummMA).mul_left C
  have hscale : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))) ≤ b j := by
    intro j
    have hj := normalized_scaleTerm_metricRoot_centered_diagonalWeakState_le
      hq t s hsymm hsq hm hE hEpd p r hfinite j
    change _ ≤ C *
      ((3 : ℝ) ^ (-(s * (j : ℝ))) +
        Real.sqrt M *
          (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))))
    calc
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))) ≤
          Real.sqrt 2 * diagonalWeakMetricFactor m E *
            ((3 : ℝ) ^ (-(s * (j : ℝ))) +
              Real.sqrt M *
                (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) *
              diagonalWeakEnergy hq t a p r := hj
      _ = C *
          ((3 : ℝ) ^ (-(s * (j : ℝ))) +
            Real.sqrt M *
              (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) := by ring
  have hseminorm := normalized_adaptedWeakSeminorm_le_of_summable
    hb0 hbsum hscale
  have hmajor := tsum_diagonalWeak_bad_majorant_le
    hrho hs hs1 hdelta hdelta1 hbad
  have htsum : (∑' j, b j) ≤
      C * (8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) * Real.sqrt M) := by
    change (∑' j : ℕ, C *
      ((3 : ℝ) ^ (-(s * (j : ℝ))) +
        Real.sqrt M *
          (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))))) ≤ _
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hmajor hC0
  exact hseminorm.trans (ENNReal.ofReal_le_ofReal htsum)

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The bad branch of the all-scale estimate, at a released split level. -/
theorem normalized_adaptedWeakSeminorm_bad_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hdelta : 0 < delta)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hbad : delta < (diagonalWeakMaximum rho q t E a).toReal) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
      ENNReal.ofReal
        ((Real.sqrt 2 * diagonalWeakMetricFactor m E *
            diagonalWeakEnergy hq t a p r) *
          (4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹ /
              (2 * s - rho) *
            Real.sqrt (diagonalWeakMaximum rho q t E a).toReal)) := by
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let C : ℝ := Real.sqrt 2 * diagonalWeakMetricFactor m E *
    diagonalWeakEnergy hq t a p r
  let b : ℕ → ℝ := fun j => C *
    ((3 : ℝ) ^ (-(s * (j : ℝ))) +
      Real.sqrt M * (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))))
  have hC0 : 0 ≤ C := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (diagonalWeakMetricFactor_nonneg m E))
      (diagonalWeakEnergy_nonneg hq t a p r)
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    exact mul_nonneg hC0 (add_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)))
  have hs0 : 0 < s := lt_trans (by linarith only [hrho]) hs
  have ha0 : 0 < s - rho / 2 := by linarith only [hs]
  have ha1 : s - rho / 2 ≤ 1 := by linarith only [hs1, hrho]
  have hsummS := summable_rpow_three_neg hs0 hs1
  have hsummA := summable_rpow_three_neg ha0 ha1
  have hsummMA : Summable fun j : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) :=
    hsummA.mul_left _
  have hbsum : Summable b := (hsummS.add hsummMA).mul_left C
  have hscale : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))) ≤ b j := by
    intro j
    have hj := normalized_scaleTerm_metricRoot_centered_diagonalWeakState_le
      hq t s hsymm hsq hm hE hEpd p r hfinite j
    change _ ≤ C *
      ((3 : ℝ) ^ (-(s * (j : ℝ))) +
        Real.sqrt M * (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))))
    calc
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))) ≤
          Real.sqrt 2 * diagonalWeakMetricFactor m E *
            ((3 : ℝ) ^ (-(s * (j : ℝ))) +
              Real.sqrt M *
                (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) *
              diagonalWeakEnergy hq t a p r := hj
      _ = C *
          ((3 : ℝ) ^ (-(s * (j : ℝ))) +
            Real.sqrt M *
              (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) := by ring
  have hseminorm := normalized_adaptedWeakSeminorm_le_of_summable
    hb0 hbsum hscale
  have hmajor := tsum_diagonalWeak_bad_majorant_at_level_le
    hrho hs hs1 hdelta hbad
  have htsum : (∑' j, b j) ≤
      C * (4 * (1 + Real.sqrt delta) * (Real.sqrt delta)⁻¹ /
        (2 * s - rho) * Real.sqrt M) := by
    change (∑' j : ℕ, C *
      ((3 : ℝ) ^ (-(s * (j : ℝ))) +
        Real.sqrt M *
          (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))))) ≤ _
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hmajor hC0
  exact hseminorm.trans (ENNReal.ofReal_le_ofReal htsum)

end

end HCPolySupport.HighContrast.Response

end HighContrast

end HCPolySupport

end

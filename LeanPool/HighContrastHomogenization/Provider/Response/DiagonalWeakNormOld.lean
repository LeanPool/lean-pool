/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormBad

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormOld

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The old-scale tail of the diagonal weak estimate

On the good branch, the normalized scale-energy estimate is summed only after
the recent window.  The resulting extended-real tail carries the decay at the
edge of that window.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The normalized weak-seminorm tail after `n` recent scales obeys the
good-branch geometric bound. -/
theorem normalized_adaptedWeakSeminorm_good_tail_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta)
    (n : ℕ) :
    (∑' j : ℕ, ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))))) ≤
      ENNReal.ofReal
        ((Real.sqrt 2 * diagonalWeakMetricFactor m E *
            diagonalWeakEnergy hq t a p r) *
          (8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
            (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))))) := by
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let C : ℝ := Real.sqrt 2 * diagonalWeakMetricFactor m E *
    diagonalWeakEnergy hq t a p r
  let b : ℕ → ℝ := fun j => C *
    ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
      Real.sqrt M *
        (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))))
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
  have hsummS0 := summable_rpow_three_neg hs0 hs1
  have hsummA0 := summable_rpow_three_neg ha0 ha1
  have hfactorS : (fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ => (3 : ℝ) ^ (-(s * (n : ℝ))) *
        (3 : ℝ) ^ (-(s * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hfactorA : (fun j : ℕ =>
      (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ => (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))) *
        (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hsummS : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorS]
    exact hsummS0.mul_left _
  have hsummA : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorA]
    exact hsummA0.mul_left _
  have hsummMA : Summable fun j : ℕ => Real.sqrt M *
      (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))) :=
    hsummA.mul_left _
  have hbsum : Summable b := (hsummS.add hsummMA).mul_left C
  have hscale : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))) ≤ b j := by
    intro j
    have hj := normalized_scaleTerm_metricRoot_centered_diagonalWeakState_le
      hq t s hsymm hsq hm hE hEpd p r hfinite (j + n)
    change _ ≤ C *
      ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
        Real.sqrt M *
          (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))))
    calc
      (3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))) ≤
          Real.sqrt 2 * diagonalWeakMetricFactor m E *
            ((3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) +
              Real.sqrt M *
                (3 : ℝ) ^ (-((s - rho / 2) * ((j + n : ℕ) : ℝ)))) *
              diagonalWeakEnergy hq t a p r := hj
      _ = C *
          ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
            Real.sqrt M *
              (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ))))) := by
        simp only [Nat.cast_add]
        ring
  have hmajor := tsum_diagonalWeak_good_tail_majorant_le
    hrho hs hs1 hdelta hdelta1 hgood n
  have htsum : (∑' j, b j) ≤ C *
      (8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
        (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ)))) := by
    change (∑' j : ℕ, C *
      ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
        Real.sqrt M *
          (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))))) ≤ _
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hmajor hC0
  calc
    (∑' j : ℕ, ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))))) ≤
        ∑' j : ℕ, ENNReal.ofReal (b j) :=
      ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hscale j)
    _ = ENNReal.ofReal (∑' j, b j) :=
      (ENNReal.ofReal_tsum_of_nonneg hb0 hbsum).symm
    _ ≤ ENNReal.ofReal (C *
        (8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
          (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))))) :=
      ENNReal.ofReal_le_ofReal htsum

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The good old-scale tail of the all-scale estimate, at a released split
level. -/
theorem normalized_adaptedWeakSeminorm_good_tail_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta)
    (n : ℕ) :
    (∑' j : ℕ, ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))))) ≤
      ENNReal.ofReal
        ((Real.sqrt 2 * diagonalWeakMetricFactor m E *
            diagonalWeakEnergy hq t a p r) *
          (4 * (1 + Real.sqrt delta) / (2 * s - rho) *
            (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))))) := by
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  let C : ℝ := Real.sqrt 2 * diagonalWeakMetricFactor m E *
    diagonalWeakEnergy hq t a p r
  let b : ℕ → ℝ := fun j => C *
    ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
      Real.sqrt M *
        (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))))
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
  have hsummS0 := summable_rpow_three_neg hs0 hs1
  have hsummA0 := summable_rpow_three_neg ha0 ha1
  have hfactorS : (fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ => (3 : ℝ) ^ (-(s * (n : ℝ))) *
        (3 : ℝ) ^ (-(s * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hfactorA : (fun j : ℕ =>
      (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ))))) =
      fun j : ℕ => (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))) *
        (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) := by
    funext j
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hsummS : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorS]; exact hsummS0.mul_left _
  have hsummA : Summable fun j : ℕ =>
      (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))) := by
    rw [hfactorA]; exact hsummA0.mul_left _
  have hsummMA : Summable fun j : ℕ => Real.sqrt M *
      (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))) :=
    hsummA.mul_left _
  have hbsum : Summable b := (hsummS.add hsummMA).mul_left C
  have hscale : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))) ≤ b j := by
    intro j
    have hj := normalized_scaleTerm_metricRoot_centered_diagonalWeakState_le
      hq t s hsymm hsq hm hE hEpd p r hfinite (j + n)
    change _ ≤ C *
      ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
        Real.sqrt M *
          (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))))
    calc
      (3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))) ≤
          Real.sqrt 2 * diagonalWeakMetricFactor m E *
            ((3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) +
              Real.sqrt M *
                (3 : ℝ) ^ (-((s - rho / 2) * ((j + n : ℕ) : ℝ)))) *
              diagonalWeakEnergy hq t a p r := hj
      _ = C *
          ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
            Real.sqrt M *
              (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ))))) := by
        simp only [Nat.cast_add]
        ring
  have hmajor := tsum_diagonalWeak_good_tail_majorant_at_level_le
    hrho hs hs1 hgood n
  have htsum : (∑' j, b j) ≤ C *
      (4 * (1 + Real.sqrt delta) / (2 * s - rho) *
        (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ)))) := by
    change (∑' j : ℕ, C *
      ((3 : ℝ) ^ (-(s * ((j : ℝ) + (n : ℝ)))) +
        Real.sqrt M *
          (3 : ℝ) ^ (-((s - rho / 2) * ((j : ℝ) + (n : ℝ)))))) ≤ _
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hmajor hC0
  calc
    (∑' j : ℕ, ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * ((j + n : ℕ) : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - ((j + n : ℕ) : ℤ)) t)
            (fun z => blockCellAverage
              (adaptedCellAt q (t - ((j + n : ℕ) : ℤ)) z) (fun x =>
                blockMatVecMul (blockDiag S S⁻¹)
                  (diagonalWeakState hq t a p r x -
                    blockCellAverage (adaptedCell q t)
                      (diagonalWeakState hq t a p r)))))) ≤
        ∑' j : ℕ, ENNReal.ofReal (b j) :=
      ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hscale j)
    _ = ENNReal.ofReal (∑' j, b j) :=
      (ENNReal.ofReal_tsum_of_nonneg hb0 hbsum).symm
    _ ≤ ENNReal.ofReal (C *
        (4 * (1 + Real.sqrt delta) / (2 * s - rho) *
          (3 : ℝ) ^ (-((s - rho / 2) * (n : ℝ))))) :=
      ENNReal.ofReal_le_ofReal htsum

end

end HCPolySupport.HighContrast.Response

end HighContrast

end HCPolySupport

end

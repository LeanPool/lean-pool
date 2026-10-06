/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentHead
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormOld

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormGood

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem normalized_adaptedWeakSeminorm_good_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
      ENNReal.ofReal
        (4 * diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
            (diagonalWeakCellSum q t H s E a +
              diagonalWeakAverageSum q t H s rho E a) +
          (Real.sqrt 2 * diagonalWeakMetricFactor m E *
              diagonalWeakEnergy hq t a p r) *
            (8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
              (3 : ℝ) ^ (-((s - rho / 2) * ((H + 1 : ℕ) : ℝ))))) := by
  let F : Vec d → BlockVec d := fun x =>
    blockMatVecMul (blockDiag S S⁻¹)
      (diagonalWeakState hq t a p r x -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r))
  let f : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
    ((3 : ℝ) ^ (-(s * (j : ℝ))) *
      blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
        (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) F))
  let Rrecent := 4 * diagonalWeakMetricFactor m E *
    diagonalWeakLoadMinus E p r *
      (diagonalWeakCellSum q t H s E a +
        diagonalWeakAverageSum q t H s rho E a)
  let Rold := (Real.sqrt 2 * diagonalWeakMetricFactor m E *
      diagonalWeakEnergy hq t a p r) *
    (8 * (Real.sqrt delta)⁻¹ / (2 * s - rho) *
      (3 : ℝ) ^ (-((s - rho / 2) * ((H + 1 : ℕ) : ℝ))))
  have hrecent : (∑ j ∈ Finset.range (H + 1), f j) ≤
      ENNReal.ofReal Rrecent := by
    exact normalized_diagonalWeak_recent_head_le hq t H hsymm hsq hm hE hEpd
      hrho hdelta1 p r hfinite hgood
  have hold : (∑' j : ℕ, f (j + (H + 1))) ≤ ENNReal.ofReal Rold := by
    exact normalized_adaptedWeakSeminorm_good_tail_le hq t hsymm hsq hm
      hE hEpd hrho hs hs1 hdelta hdelta1 p r hfinite hgood (H + 1)
  have hrecent0 : 0 ≤ Rrecent := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (diagonalWeakMetricFactor_nonneg m E))
        (diagonalWeakLoadMinus_nonneg E p r))
      (add_nonneg
        (diagonalWeakCellSum_nonneg q t H s E a)
        (diagonalWeakAverageSum_nonneg q t H s rho E a))
  have hden : 0 < 2 * s - rho := by linarith only [hs]
  have hold0 : 0 ≤ Rold := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (diagonalWeakMetricFactor_nonneg m E))
        (diagonalWeakEnergy_nonneg hq t a p r))
      (mul_nonneg
        (div_nonneg
          (mul_nonneg (by positivity) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
          hden.le)
        (Real.rpow_nonneg (by norm_num) _))
  have hsplit : (∑' j : ℕ, f j) =
      (∑ j ∈ Finset.range (H + 1), f j) +
        ∑' j : ℕ, f (j + (H + 1)) := by
    have hsumm : Summable fun j : ℕ => f (j + (H + 1)) := ENNReal.summable
    exact (hsumm.sum_add_tsum_nat_add' (k := H + 1)).symm
  rw [ofReal_rpow_mul_adaptedWeakSeminorm]
  change (∑' j : ℕ, f j) ≤ ENNReal.ofReal (Rrecent + Rold)
  rw [hsplit]
  calc
    (∑ j ∈ Finset.range (H + 1), f j) +
          ∑' j : ℕ, f (j + (H + 1)) ≤
        ENNReal.ofReal Rrecent + ENNReal.ofReal Rold := add_le_add hrecent hold
    _ = ENNReal.ofReal (Rrecent + Rold) :=
      (ENNReal.ofReal_add hrecent0 hold0).symm

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The good branch of the all-scale estimate, at a released split level. -/
theorem normalized_adaptedWeakSeminorm_good_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hs : rho / 2 < s)
    (hs1 : s ≤ 1)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (t : ℝ)))) *
        adaptedWeakSeminorm q t s (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
      ENNReal.ofReal
        (recentConstantAtLevel delta * diagonalWeakMetricFactor m E *
            diagonalWeakLoadMinus E p r *
            (diagonalWeakCellSum q t H s E a +
              diagonalWeakAverageSum q t H s rho E a) +
          (Real.sqrt 2 * diagonalWeakMetricFactor m E *
              diagonalWeakEnergy hq t a p r) *
            (4 * (1 + Real.sqrt delta) / (2 * s - rho) *
              (3 : ℝ) ^ (-((s - rho / 2) * ((H + 1 : ℕ) : ℝ))))) := by
  let F : Vec d → BlockVec d := fun x =>
    blockMatVecMul (blockDiag S S⁻¹)
      (diagonalWeakState hq t a p r x -
        blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r))
  let f : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
    ((3 : ℝ) ^ (-(s * (j : ℝ))) *
      blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
        (fun z => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) F))
  let Rrecent := recentConstantAtLevel delta * diagonalWeakMetricFactor m E *
    diagonalWeakLoadMinus E p r *
      (diagonalWeakCellSum q t H s E a +
        diagonalWeakAverageSum q t H s rho E a)
  let Rold := (Real.sqrt 2 * diagonalWeakMetricFactor m E *
      diagonalWeakEnergy hq t a p r) *
    (4 * (1 + Real.sqrt delta) / (2 * s - rho) *
      (3 : ℝ) ^ (-((s - rho / 2) * ((H + 1 : ℕ) : ℝ))))
  have hrecent : (∑ j ∈ Finset.range (H + 1), f j) ≤
      ENNReal.ofReal Rrecent :=
    normalized_diagonalWeak_recent_head_at_level_le hq t H hsymm hsq hm hE hEpd
      hrho p r hfinite hgood
  have hold : (∑' j : ℕ, f (j + (H + 1))) ≤ ENNReal.ofReal Rold :=
    normalized_adaptedWeakSeminorm_good_tail_at_level_le hq t hsymm hsq hm
      hE hEpd hrho hs hs1 p r hfinite hgood (H + 1)
  have hcrec0 : 0 ≤ recentConstantAtLevel delta :=
    zero_le_recentConstantAtLevel delta
  have hrecent0 : 0 ≤ Rrecent := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcrec0 (diagonalWeakMetricFactor_nonneg m E))
        (diagonalWeakLoadMinus_nonneg E p r))
      (add_nonneg
        (diagonalWeakCellSum_nonneg q t H s E a)
        (diagonalWeakAverageSum_nonneg q t H s rho E a))
  have hden : 0 < 2 * s - rho := by linarith only [hs]
  have hsd0 : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hold0 : 0 ≤ Rold := by
    refine mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (diagonalWeakMetricFactor_nonneg m E))
        (diagonalWeakEnergy_nonneg hq t a p r))
      (mul_nonneg (div_nonneg (by positivity) hden.le)
        (Real.rpow_nonneg (by norm_num) _))
  have hsplit : (∑' j : ℕ, f j) =
      (∑ j ∈ Finset.range (H + 1), f j) +
        ∑' j : ℕ, f (j + (H + 1)) := by
    have hsumm : Summable fun j : ℕ => f (j + (H + 1)) := ENNReal.summable
    exact (hsumm.sum_add_tsum_nat_add' (k := H + 1)).symm
  rw [ofReal_rpow_mul_adaptedWeakSeminorm]
  change (∑' j : ℕ, f j) ≤ ENNReal.ofReal (Rrecent + Rold)
  rw [hsplit]
  calc
    (∑ j ∈ Finset.range (H + 1), f j) +
          ∑' j : ℕ, f (j + (H + 1)) ≤
        ENNReal.ofReal Rrecent + ENNReal.ofReal Rold := add_le_add hrecent hold
    _ = ENNReal.ofReal (Rrecent + Rold) :=
      (ENNReal.ofReal_add hrecent0 hold0).symm

end

end HCPolySupport.HighContrast.Response

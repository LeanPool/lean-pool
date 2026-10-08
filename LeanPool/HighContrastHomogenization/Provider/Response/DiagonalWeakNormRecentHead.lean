/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentDecomposition

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentHead

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem normalized_diagonalWeak_recent_head_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho) (hdelta1 : delta ≤ 1)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun w => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) w)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))))) ≤
      ENNReal.ofReal
        (4 * diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
          (diagonalWeakCellSum q t H s E a +
            diagonalWeakAverageSum q t H s rho E a)) := by
  let K := diagonalWeakMetricFactor m E
  let L := diagonalWeakLoadMinus E p r
  let b : ℕ → ℝ := fun j => 4 * K * L *
    ((3 : ℝ) ^ (-(s * (j : ℝ))) *
        diagonalWeakCellDefect q (t - (j : ℤ)) t E a +
      (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) *
        Real.sqrt (blockSize
          (diagonalWeakAverageDefect q (t - (j : ℤ)) t E a)
          (blockIdentity d)))
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hL0 : 0 ≤ L := diagonalWeakLoadMinus_nonneg E p r
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    exact mul_nonneg (mul_nonneg (by positivity) hL0)
      (add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (diagonalWeakCellDefect_nonneg q (t - (j : ℤ)) t E a))
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.sqrt_nonneg _)))
  have hscale : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
        blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
          (fun w => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) w)
            (fun x => blockMatVecMul (blockDiag S S⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r)))) ≤ b j := by
    intro j
    let k : ℤ := t - (j : ℤ)
    let C := diagonalWeakCellDefect q k t E a
    let D := Real.sqrt
      (blockSize (diagonalWeakAverageDefect q k t E a) (blockIdentity d))
    let W := (3 : ℝ) ^ (-(s * (j : ℝ)))
    let R := (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)
    have hkt : k ≤ t := sub_le_self t (Int.natCast_nonneg j)
    have hinner : blockAvsumL2 (alignedIndex q k t)
        (fun w => blockCellAverage (adaptedCellAt q k w)
          (fun x => blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r)))) =
      blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakState hq t a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) := by
      rw [blockAvsumL2_eq, blockAvsumL2_eq]
      congr 1
      unfold avsum
      congr 1
      refine Finset.sum_congr rfl fun w hw => ?_
      have hcell := blockCellAverage_metricRoot_centered_diagonalWeakState
        hq hkt hw p r (S := S) (a := a)
      exact congrArg₂ blockVecDot hcell hcell
    have hrecent := diagonalWeak_recent_scale_decomposition_le
      hq hkt hsymm hsq hm hE hEpd hrho hdelta1 p r hfinite hgood
    have hW0 : 0 ≤ W := Real.rpow_nonneg (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hrecent hW0
    have hpow : W * R =
        (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      dsimp only [W, R, k]
      norm_num
      ring
    have hC0 : 0 ≤ C :=
      diagonalWeakCellDefect_nonneg q k t E a
    have hcellcoef : K * L * (W * C) ≤ 4 * K * L * (W * C) := by
      have hprod0 : 0 ≤ K * L * (W * C) := by positivity
      linarith only [hprod0]
    change W * blockAvsumL2 (alignedIndex q k t) _ ≤ _
    rw [hinner]
    calc
      W * blockAvsumL2 (alignedIndex q k t) (fun w =>
          blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakState hq t a p r) -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
        W * (K * L * C + 4 * K * L * R * D) := hmul
      _ = K * L * (W * C) + 4 * K * L * (W * R) * D := by ring
      _ ≤ 4 * K * L * (W * C) + 4 * K * L * (W * R) * D :=
        add_le_add hcellcoef le_rfl
      _ = b j := by
        rw [hpow]
        dsimp only [b, C, D, W, k]
        ring
  have hsum : ∑ j ∈ Finset.range (H + 1), b j =
      4 * K * L *
        (diagonalWeakCellSum q t H s E a +
          diagonalWeakAverageSum q t H s rho E a) := by
    rw [diagonalWeakCellSum_eq, diagonalWeakAverageSum_eq]
    change (∑ j ∈ Finset.range (H + 1), (4 * K * L) *
        ((3 : ℝ) ^ (-(s * (j : ℝ))) *
            diagonalWeakCellDefect q (t - (j : ℤ)) t E a +
          (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) *
            Real.sqrt (blockSize
              (diagonalWeakAverageDefect q (t - (j : ℤ)) t E a)
              (blockIdentity d)))) = _
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    congr 2
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ring
  calc
    (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun w => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) w)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))))) ≤
      ∑ j ∈ Finset.range (H + 1), ENNReal.ofReal (b j) :=
        Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal (hscale j)
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (H + 1), b j) :=
      (ENNReal.ofReal_sum_of_nonneg fun j _ => hb0 j).symm
    _ = ENNReal.ofReal (4 * K * L *
        (diagonalWeakCellSum q t H s E a +
          diagonalWeakAverageSum q t H s rho E a)) := by rw [hsum]

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The recent head block of the all-scale estimate, at a released split
level. -/
theorem normalized_diagonalWeak_recent_head_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho s delta : ℝ} (hrho : 0 < rho)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun w => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) w)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))))) ≤
      ENNReal.ofReal
        (recentConstantAtLevel delta *
          diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
          (diagonalWeakCellSum q t H s E a +
            diagonalWeakAverageSum q t H s rho E a)) := by
  set crec : ℝ := recentConstantAtLevel delta with hcrecdef
  have hcrec1 : 1 ≤ crec := one_le_recentConstantAtLevel delta
  have hcrec0 : 0 ≤ crec := le_trans zero_le_one hcrec1
  let K := diagonalWeakMetricFactor m E
  let L := diagonalWeakLoadMinus E p r
  let b : ℕ → ℝ := fun j => crec * K * L *
    ((3 : ℝ) ^ (-(s * (j : ℝ))) *
        diagonalWeakCellDefect q (t - (j : ℤ)) t E a +
      (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) *
        Real.sqrt (blockSize
          (diagonalWeakAverageDefect q (t - (j : ℤ)) t E a)
          (blockIdentity d)))
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hL0 : 0 ≤ L := diagonalWeakLoadMinus_nonneg E p r
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    exact mul_nonneg (mul_nonneg (by positivity) hL0)
      (add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (diagonalWeakCellDefect_nonneg q (t - (j : ℤ)) t E a))
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.sqrt_nonneg _)))
  have hscale : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
        blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
          (fun w => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) w)
            (fun x => blockMatVecMul (blockDiag S S⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r)))) ≤ b j := by
    intro j
    let k : ℤ := t - (j : ℤ)
    let C := diagonalWeakCellDefect q k t E a
    let D := Real.sqrt
      (blockSize (diagonalWeakAverageDefect q k t E a) (blockIdentity d))
    let W := (3 : ℝ) ^ (-(s * (j : ℝ)))
    let R := (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)
    have hkt : k ≤ t := sub_le_self t (Int.natCast_nonneg j)
    have hinner : blockAvsumL2 (alignedIndex q k t)
        (fun w => blockCellAverage (adaptedCellAt q k w)
          (fun x => blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r)))) =
      blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakState hq t a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) := by
      rw [blockAvsumL2_eq, blockAvsumL2_eq]
      congr 1
      unfold avsum
      congr 1
      refine Finset.sum_congr rfl fun w hw => ?_
      have hcell := blockCellAverage_metricRoot_centered_diagonalWeakState
        hq hkt hw p r (S := S) (a := a)
      exact congrArg₂ blockVecDot hcell hcell
    have hrecent := diagonalWeak_recent_scale_decomposition_at_level_le
      hq hkt hsymm hsq hm hE hEpd hrho p r hfinite hgood
    have hW0 : 0 ≤ W := Real.rpow_nonneg (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hrecent hW0
    have hpow : W * R =
        (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      dsimp only [W, R, k]
      norm_num
      ring
    have hC0 : 0 ≤ C := diagonalWeakCellDefect_nonneg q k t E a
    have hcellcoef : K * L * (W * C) ≤ crec * K * L * (W * C) := by
      have hprod0 : 0 ≤ K * L * (W * C) := by positivity
      nlinarith only [hprod0, hcrec1]
    change W * blockAvsumL2 (alignedIndex q k t) _ ≤ _
    rw [hinner]
    calc
      W * blockAvsumL2 (alignedIndex q k t) (fun w =>
          blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakState hq t a p r) -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
        W * (K * L * C + crec * K * L * R * D) := hmul
      _ = K * L * (W * C) + crec * K * L * (W * R) * D := by ring
      _ ≤ crec * K * L * (W * C) + crec * K * L * (W * R) * D :=
        add_le_add hcellcoef le_rfl
      _ = b j := by
        rw [hpow]
        dsimp only [b, C, D, W, k]
        ring
  have hsum : ∑ j ∈ Finset.range (H + 1), b j =
      crec * K * L *
        (diagonalWeakCellSum q t H s E a +
          diagonalWeakAverageSum q t H s rho E a) := by
    rw [diagonalWeakCellSum_eq, diagonalWeakAverageSum_eq]
    change (∑ j ∈ Finset.range (H + 1), (crec * K * L) *
        ((3 : ℝ) ^ (-(s * (j : ℝ))) *
            diagonalWeakCellDefect q (t - (j : ℤ)) t E a +
          (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) *
            Real.sqrt (blockSize
              (diagonalWeakAverageDefect q (t - (j : ℤ)) t E a)
              (blockIdentity d)))) = _
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    congr 2
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ring
  calc
    (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal
        ((3 : ℝ) ^ (-(s * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun w => blockCellAverage (adaptedCellAt q (t - (j : ℤ)) w)
              (fun x => blockMatVecMul (blockDiag S S⁻¹)
                (diagonalWeakState hq t a p r x -
                  blockCellAverage (adaptedCell q t)
                    (diagonalWeakState hq t a p r)))))) ≤
      ∑ j ∈ Finset.range (H + 1), ENNReal.ofReal (b j) :=
        Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal (hscale j)
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (H + 1), b j) :=
      (ENNReal.ofReal_sum_of_nonneg fun j _ => hb0 j).symm
    _ = ENNReal.ofReal (crec * K * L *
        (diagonalWeakCellSum q t H s E a +
          diagonalWeakAverageSum q t H s rho E a)) := by rw [hsum]

end

end HCPolySupport.HighContrast.Response

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormScaleClosure

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormCentering

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Centering the optimizer state inside the weak seminorm

On every aligned child, averaging commutes with both subtraction of the parent
mean and the fixed block-diagonal metric root.  This identifies the field in
the weak seminorm with the centered scale quantity estimated variationally.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The average on one child of the metric-root image of the centered
canonical state is the metric-root image of the difference of averages. -/
theorem blockCellAverage_metricRoot_centered_diagonalWeakState [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t) {S : Mat d}
    {a : CoeffSpace d} (p r : Vec d) :
    blockCellAverage (adaptedCellAt q k w) (fun x =>
        blockMatVecMul (blockDiag S S⁻¹)
          (diagonalWeakState hq t a p r x -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) =
      blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r) -
          blockCellAverage (adaptedCell q t)
            (diagonalWeakState hq t a p r)) := by
  let F := diagonalWeakState hq t a p r
  let c := blockCellAverage (adaptedCell q t) F
  obtain ⟨hpotParent, hfluxParent⟩ :=
    diagonalWeakState_memVectorL2 hq t a p r
  have hsub : adaptedCellAt q k w ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw
  have hpot : MemVectorL2 (adaptedCellAt q k w) (fun x => (F x).1) :=
    memVectorL2_mono hsub hpotParent
  have hflux : MemVectorL2 (adaptedCellAt q k w) (fun x => (F x).2) :=
    memVectorL2_mono hsub hfluxParent
  have hdom := Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w
  have hpotCentered : MemVectorL2 (adaptedCellAt q k w)
      (fun x => (F x - c).1) := by
    change MemVectorL2 (adaptedCellAt q k w) (fun x => (F x).1 - c.1)
    exact memVectorL2_sub_const hdom hpot c.1
  have hfluxCentered : MemVectorL2 (adaptedCellAt q k w)
      (fun x => (F x - c).2) := by
    change MemVectorL2 (adaptedCellAt q k w) (fun x => (F x).2 - c.2)
    exact memVectorL2_sub_const hdom hflux c.2
  have hne : volume (adaptedCellAt q k w) ≠ 0 :=
    ne_of_gt (Recurrence.volume_adaptedCellAt_pos hq k w)
  have htop : volume (adaptedCellAt q k w) ≠ ⊤ :=
    ne_of_lt hdom.volume_lt_top
  change blockCellAverage (adaptedCellAt q k w) (fun x =>
      blockMatVecMul (blockDiag S S⁻¹) (F x - c)) =
    blockMatVecMul (blockDiag S S⁻¹)
      (blockCellAverage (adaptedCellAt q k w) F - c)
  calc
    blockCellAverage (adaptedCellAt q k w) (fun x =>
        blockMatVecMul (blockDiag S S⁻¹) (F x - c)) =
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) (fun x => F x - c)) :=
      blockCellAverage_blockDiag (U := adaptedDomainAt hq k w)
        S S⁻¹ hpotCentered hfluxCentered
    _ = blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w) F - c) := by
      have hcenter := blockCellAverage_sub_const (U := adaptedDomainAt hq k w)
        c hne htop hpot hflux
      exact congrArg (blockMatVecMul (blockDiag S S⁻¹)) hcenter

/-- The normalized inner scale term of the centered metric-root field obeys
the variational scale-energy majorant. -/
theorem normalized_scaleTerm_metricRoot_centered_diagonalWeakState_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (s : ℝ) {S m : Mat d}
    (hsymm : matTranspose S = S) (hsq : S * S = m) (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    {rho : ℝ} {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) (j : ℕ) :
    (3 : ℝ) ^ (-(s * (j : ℝ))) *
        blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t) (fun w =>
          blockCellAverage (adaptedCellAt q (t - (j : ℤ)) w) (fun x =>
            blockMatVecMul (blockDiag S S⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r)))) ≤
      Real.sqrt 2 * diagonalWeakMetricFactor m E *
        ((3 : ℝ) ^ (-(s * (j : ℝ))) +
          Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
            (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) *
        diagonalWeakEnergy hq t a p r := by
  let k : ℤ := t - (j : ℤ)
  let M : ℝ := (diagonalWeakMaximum rho q t E a).toReal
  have hkt : k ≤ t := sub_le_self t (Int.natCast_nonneg j)
  have hinner : blockAvsumL2 (alignedIndex q k t) (fun w =>
      blockCellAverage (adaptedCellAt q k w) (fun x =>
        blockMatVecMul (blockDiag S S⁻¹)
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
  have hscale := diagonalWeak_scale_energy_bound hq hkt hsymm hsq hm
    hE hEpd p r hfinite
  have hweight0 : 0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hscale hweight0
  have hpow : (3 : ℝ) ^ (-(s * (j : ℝ))) *
      (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) =
      (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    dsimp only [k]
    norm_num
    ring
  change (3 : ℝ) ^ (-(s * (j : ℝ))) *
      blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockCellAverage (adaptedCellAt q k w) (fun x =>
          blockMatVecMul (blockDiag S S⁻¹)
            (diagonalWeakState hq t a p r x -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r)))) ≤ _
  rw [hinner]
  calc
    (3 : ℝ) ^ (-(s * (j : ℝ))) *
        blockAvsumL2 (alignedIndex q k t) (fun w =>
          blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w)
                (diagonalWeakState hq t a p r) -
              blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r))) ≤
        (3 : ℝ) ^ (-(s * (j : ℝ))) *
          (Real.sqrt 2 * diagonalWeakMetricFactor m E *
            (1 + Real.sqrt M *
              (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)) *
                diagonalWeakEnergy hq t a p r) := hmul
    _ = Real.sqrt 2 * diagonalWeakMetricFactor m E *
        ((3 : ℝ) ^ (-(s * (j : ℝ))) +
          Real.sqrt M *
            (3 : ℝ) ^ (-((s - rho / 2) * (j : ℝ)))) *
        diagonalWeakEnergy hq t a p r := by
      calc
        (3 : ℝ) ^ (-(s * (j : ℝ))) *
            (Real.sqrt 2 * diagonalWeakMetricFactor m E *
              (1 + Real.sqrt M *
                (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)) *
                  diagonalWeakEnergy hq t a p r) =
            Real.sqrt 2 * diagonalWeakMetricFactor m E *
              ((3 : ℝ) ^ (-(s * (j : ℝ))) +
                Real.sqrt M *
                  ((3 : ℝ) ^ (-(s * (j : ℝ))) *
                    (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2))) *
                diagonalWeakEnergy hq t a p r := by ring
        _ = _ := by rw [hpow]

end

end HCPolySupport.HighContrast.Response

end HighContrast

end HCPolySupport

end

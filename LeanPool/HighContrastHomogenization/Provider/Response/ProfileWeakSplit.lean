/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyMeasurability

/-!
# High-contrast homogenization: Provider.Response.ProfileWeakSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Replacing the random optimizer average by its annealed center

At every scale, the optimizer state centered at a deterministic vector splits
as the state centered at its random parent average plus a fixed field.  The
scale-average triangle inequality and the exact fixed-field computation
give the corresponding normalized seminorm bound.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Averaging the metric-root image of a state minus an arbitrary fixed vector
commutes with both operations. -/
theorem blockCellAverage_metricRoot_sub_const_diagonalWeakState
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t) {S : Mat d}
    {a : CoeffSpace d} (p r : Vec d) (c : BlockVec d) :
    blockCellAverage (adaptedCellAt q k w) (fun x ↦
        blockMatVecMul (blockDiag S S⁻¹)
          (diagonalWeakState hq t a p r x - c)) =
      blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r) - c) := by
  let F := diagonalWeakState hq t a p r
  obtain ⟨hpotParent, hfluxParent⟩ :=
    diagonalWeakState_memVectorL2 hq t a p r
  have hsub : adaptedCellAt q k w ⊆ adaptedCell q t :=
    adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw
  have hpot : MemVectorL2 (adaptedCellAt q k w) (fun x ↦ (F x).1) :=
    memVectorL2_mono hsub hpotParent
  have hflux : MemVectorL2 (adaptedCellAt q k w) (fun x ↦ (F x).2) :=
    memVectorL2_mono hsub hfluxParent
  have hdom := Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w
  have hpotCentered : MemVectorL2 (adaptedCellAt q k w)
      (fun x ↦ (F x - c).1) := by
    change MemVectorL2 (adaptedCellAt q k w) (fun x ↦ (F x).1 - c.1)
    exact memVectorL2_sub_const hdom hpot c.1
  have hfluxCentered : MemVectorL2 (adaptedCellAt q k w)
      (fun x ↦ (F x - c).2) := by
    change MemVectorL2 (adaptedCellAt q k w) (fun x ↦ (F x).2 - c.2)
    exact memVectorL2_sub_const hdom hflux c.2
  have hne : volume (adaptedCellAt q k w) ≠ 0 :=
    ne_of_gt (Recurrence.volume_adaptedCellAt_pos hq k w)
  have htop : volume (adaptedCellAt q k w) ≠ ⊤ :=
    ne_of_lt hdom.volume_lt_top
  change blockCellAverage (adaptedCellAt q k w) (fun x ↦
      blockMatVecMul (blockDiag S S⁻¹) (F x - c)) = _
  calc
    blockCellAverage (adaptedCellAt q k w) (fun x ↦
        blockMatVecMul (blockDiag S S⁻¹) (F x - c)) =
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) (fun x ↦ F x - c)) :=
      blockCellAverage_blockDiag (U := adaptedDomainAt hq k w)
        S S⁻¹ hpotCentered hfluxCentered
    _ = blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w) F - c) := by
      exact congrArg (blockMatVecMul (blockDiag S S⁻¹))
        (blockCellAverage_sub_const (U := adaptedDomainAt hq k w)
          c hne htop hpot hflux)

private theorem normalized_primal_weak_split
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {m : Mat d}
    (hm : m.PosDef) (a : CoeffSpace d) (p r : Vec d)
    (center : BlockVec d) :
    profilePrimalWeakRoot m hq t id p r center a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          adaptedWeakSeminorm q t (1 / 2) (fun x ↦
            blockMatVecMul (blockDiag (matSqrt m) (matSqrt m)⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r))) +
        ENNReal.ofReal constantSeminormCoefficient *
          ENNReal.ofReal (Real.sqrt (metricBlockNormSq m
            (blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r) - center))) := by
  let S := matSqrt m
  let parent := blockCellAverage (adaptedCell q t)
    (diagonalWeakState hq t a p r)
  let target : Vec d → BlockVec d := fun x ↦
    blockMatVecMul (blockDiag S S⁻¹)
      (diagonalWeakState hq t a p r x - center)
  let raw : Vec d → BlockVec d := fun x ↦
    blockMatVecMul (blockDiag S S⁻¹)
      (diagonalWeakState hq t a p r x - parent)
  let constField : Vec d → BlockVec d := fun _ ↦
    blockMatVecMul (blockDiag S S⁻¹) (parent - center)
  have hterm : ∀ j : ℕ,
      ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              target)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              raw)) +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              constField)) := by
    intro j
    have hkt : t - (j : ℤ) ≤ t := by omega
    have hsplit : ∀ z ∈ alignedIndex q (t - (j : ℤ)) t,
        blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) target =
          blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw +
            blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) constField := by
      intro z hz
      rw [show blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) target =
          blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
                (diagonalWeakState hq t a p r) - center) by
        exact blockCellAverage_metricRoot_sub_const_diagonalWeakState
          hq hkt hz p r center,
        show blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw =
          blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
                (diagonalWeakState hq t a p r) - parent) by
        exact blockCellAverage_metricRoot_centered_diagonalWeakState
          hq hkt hz p r,
        show blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) constField =
          blockMatVecMul (blockDiag S S⁻¹) (parent - center) by
        exact blockCellAverage_const_adapted hq _ z _]
      rw [← blockMatVecMul_add]
      congr 1
      abel
    have hfamilies :
        blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              target) =
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦
              blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw +
                blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) constField) := by
      rw [blockAvsumL2_eq, blockAvsumL2_eq]
      congr 1
      unfold avsum
      congr 1
      exact Finset.sum_congr rfl fun z hz ↦
        congrArg₂ blockVecDot (hsplit z hz) (hsplit z hz)
    have hL2 := blockAvsumL2_add_le
      (alignedIndex q (t - (j : ℤ)) t)
      (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw)
      (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) constField)
    have hL2target :
        blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              target) ≤
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
              (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw) +
            blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
              (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
                constField) := hfamilies.le.trans hL2
    have hw0 : 0 ≤ (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hL2target hw0
    calc
      ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              target)) ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
            (blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
                (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw) +
              blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
                (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
                  constField))) := ENNReal.ofReal_le_ofReal hmul
      _ = ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
            blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
              (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw) +
          (3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
            blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
              (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
                constField)) := by
        congr 1
        ring
      _ = _ := ENNReal.ofReal_add
        (mul_nonneg hw0 (blockAvsumL2_nonneg _ _))
        (mul_nonneg hw0 (blockAvsumL2_nonneg _ _))
  rw [← normalized_adaptedWeakSeminorm_blockDiag_const hq hm t
    (parent - center)]
  simp only [profilePrimalWeakRoot, id_eq]
  have hexpT : (-(1 / 2 : ℝ)) * (t : ℝ) =
      -((1 / 2 : ℝ) * (t : ℝ)) := by ring
  rw [hexpT]
  change ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
      adaptedWeakSeminorm q t (1 / 2) target ≤
    ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
        adaptedWeakSeminorm q t (1 / 2) raw +
      ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
        adaptedWeakSeminorm q t (1 / 2) constField
  rw [ofReal_rpow_mul_adaptedWeakSeminorm]
  calc
    _ ≤ ∑' j : ℕ,
        (ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw)) +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
          blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
            (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
              constField))) := ENNReal.tsum_le_tsum hterm
    _ = (∑' j : ℕ, ENNReal.ofReal
          ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
            blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
              (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z) raw))) +
        ∑' j : ℕ, ENNReal.ofReal
          ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (j : ℝ))) *
            blockAvsumL2 (alignedIndex q (t - (j : ℤ)) t)
              (fun z ↦ blockCellAverage (adaptedCellAt q (t - (j : ℤ)) z)
                constField)) := ENNReal.tsum_add
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          adaptedWeakSeminorm q t (1 / 2) raw +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          adaptedWeakSeminorm q t (1 / 2) constField := by
      rw [ofReal_rpow_mul_adaptedWeakSeminorm,
        ofReal_rpow_mul_adaptedWeakSeminorm]
    _ = _ := by rfl

/-- The primal normalized weak root splits into its random-centered part and
the exact constField correction. -/
theorem profilePrimalWeakRoot_le_randomCentered_add_constant
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {m : Mat d}
    (hm : m.PosDef) (a : CoeffSpace d) (p r : Vec d)
    (center : BlockVec d) :
    profilePrimalWeakRoot m hq t id p r center a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          adaptedWeakSeminorm q t (1 / 2) (fun x ↦
            blockMatVecMul (blockDiag (matSqrt m) (matSqrt m)⁻¹)
              (diagonalWeakState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakState hq t a p r))) +
        ENNReal.ofReal constantSeminormCoefficient *
          ENNReal.ofReal (Real.sqrt (metricBlockNormSq m
            (blockCellAverage (adaptedCell q t)
                (diagonalWeakState hq t a p r) - center))) :=
  normalized_primal_weak_split hq t hm a p r center

/-- The adjoint normalized weak root has the analogous split. -/
theorem profileAdjointWeakRoot_le_randomCentered_add_constant
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {m : Mat d}
    (hm : m.PosDef) (a : CoeffSpace d) (p r : Vec d)
    (center : BlockVec d) :
    profileAdjointWeakRoot m hq t id p r center a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 2 : ℝ) * (t : ℝ)))) *
          adaptedWeakSeminorm q t (1 / 2) (fun x ↦
            blockMatVecMul (blockDiag (matSqrt m) (matSqrt m)⁻¹)
              (diagonalWeakAdjointState hq t a p r x -
                blockCellAverage (adaptedCell q t)
                  (diagonalWeakAdjointState hq t a p r))) +
        ENNReal.ofReal constantSeminormCoefficient *
          ENNReal.ofReal (Real.sqrt (metricBlockNormSq m
            (blockCellAverage (adaptedCell q t)
                (diagonalWeakAdjointState hq t a p r) - center))) := by
  simpa only [profileAdjointWeakRoot, diagonalWeakAdjointState_eq] using!
    normalized_primal_weak_split hq t hm a.transpose p r center

end

end HCPolySupport.HighContrast.Response
